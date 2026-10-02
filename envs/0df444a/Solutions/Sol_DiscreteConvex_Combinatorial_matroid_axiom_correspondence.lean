-- Prove2me | solution 1 for DiscreteConvex.Combinatorial.matroid_axiom_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T02:18:11.477728+00:00
-- url     : https://prove2.me/submissions/9b01fb52-ff99-419e-99d5-526f85b66408

import Definitions.Def_DiscreteConvex_Combinatorial_ExchangeFamily
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega
import Definitions.Def_DiscreteConvex_Combinatorial_RankAxioms
import Definitions.Def_DiscreteConvex_Combinatorial_RankOfFamily
import Definitions.Def_DiscreteConvex_Combinatorial_FamilyOfRank
import Theorems.Thm_SteinitzExchange_Duality_frank_discrete_separation
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Theorems.Thm_SteinitzExchange_Duality_baseSet_iff_submodular_system
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Data.Nat.Cast.Order.Ring


set_option autoImplicit false
open scoped BigOperators

namespace DcaRankIndicator

variable {V : Type*} [DecidableEq V]

def indicator (J : Finset V) : V → ℤ := fun v => if v ∈ J then 1 else 0

lemma indicator_injective : Function.Injective (indicator (V := V)) := by
  intro J K h
  ext v
  have hv := congrFun h v
  by_cases hJ : v ∈ J <;> by_cases hK : v ∈ K <;> simp_all [indicator]

lemma positive_difference_iff (J K : Finset V) (v : V) :
    0 < (indicator J - indicator K) v ↔ v ∈ J \ K := by
  by_cases hJ : v ∈ J <;> by_cases hK : v ∈ K <;>
    simp [indicator,Pi.sub_apply,hJ,hK]

lemma negative_difference_iff (J K : Finset V) (v : V) :
    (indicator J - indicator K) v < 0 ↔ v ∈ K \ J := by
  by_cases hJ : v ∈ J <;> by_cases hK : v ∈ K <;>
    simp [indicator,Pi.sub_apply,hJ,hK]

lemma indicator_exchange (J : Finset V) (i j : V) (hi : i ∈ J) (hj : j ∉ J) :
    indicator (insert j (J.erase i)) =
      indicator J - SteinitzExchange.Extension.chi i + SteinitzExchange.Extension.chi j := by
  have hij : i ≠ j := by intro h; subst j; exact hj hi
  ext v
  by_cases hvi : v = i
  · subst v
    simp [indicator,SteinitzExchange.Extension.chi,Pi.single_apply,Pi.add_apply,Pi.sub_apply,hi,hij]
  · by_cases hvj : v = j
    · subst v
      simp [indicator,SteinitzExchange.Extension.chi,Pi.single_apply,Pi.add_apply,Pi.sub_apply,hj,Ne.symm hij]
    · simp [indicator,SteinitzExchange.Extension.chi,Pi.single_apply,Pi.add_apply,Pi.sub_apply,hvi,hvj]

lemma subset_sum_indicator (J X : Finset V) :
    (∑ v ∈ X, indicator J v) = ((X ∩ J).card : ℤ) := by
  simp [indicator,Finset.sum_ite_mem]

lemma total_sum_indicator [Fintype V] (J : Finset V) :
    (∑ v, indicator J v) = (J.card : ℤ) := by
  simpa using subset_sum_indicator J Finset.univ

open Classical in
noncomputable def liftFamily (F : Finset (Finset V)) : Finset (V → ℤ) :=
  F.image indicator

lemma mem_liftFamily (F : Finset (Finset V)) (x : V → ℤ) :
    x ∈ liftFamily F ↔ ∃ J ∈ F, indicator J = x := by
  classical
  exact Finset.mem_image

lemma indicator_mem_liftFamily_iff (F : Finset (Finset V)) (J : Finset V) :
    indicator J ∈ liftFamily F ↔ J ∈ F := by
  classical
  constructor
  · rintro h
    obtain ⟨K,hK,hKJ⟩ := (mem_liftFamily F (indicator J)).mp h
    exact indicator_injective hKJ ▸ hK
  · intro hJ
    exact (mem_liftFamily F (indicator J)).mpr ⟨J,hJ,rfl⟩

lemma liftFamily_nonempty_iff (F : Finset (Finset V)) :
    (liftFamily F).Nonempty ↔ F.Nonempty := by
  classical
  exact Finset.image_nonempty

lemma liftFamily_isBase [Fintype V] (F : Finset (Finset V)) (hne : F.Nonempty)
    (hF : DiscreteConvex.Combinatorial.ExchangeFamily F) :
    SteinitzExchange.Extension.IsIntegralBaseSet (liftFamily F) := by
  classical
  refine ⟨(liftFamily_nonempty_iff F).mpr hne,?_⟩
  intro x hx y hy i hi
  obtain ⟨J,hJ,rfl⟩ := (mem_liftFamily F x).mp hx
  obtain ⟨K,hK,rfl⟩ := (mem_liftFamily F y).mp hy
  have hiJK := (positive_difference_iff J K i).mp hi
  obtain ⟨j,hjKJ,hJ',hK'⟩ := hF J hJ K hK i hiJK
  refine ⟨j,(negative_difference_iff J K j).mpr hjKJ,?_⟩
  rw [← indicator_exchange J i j (Finset.mem_sdiff.mp hiJK).1 (Finset.mem_sdiff.mp hjKJ).2]
  exact (indicator_mem_liftFamily_iff F _).mpr hJ'

/-- Ordinary B1 exchange on binary vectors transports back to one-sided set exchange.
The simultaneous upgrade is a separate matroid theorem, not assumed here. -/
lemma one_sided_exchange_of_liftFamily_isBase (F : Finset (Finset V))
    (hF : SteinitzExchange.Extension.IsIntegralBaseSet (liftFamily F)) :
    ∀ J ∈ F, ∀ K ∈ F, ∀ i ∈ J \ K,
      ∃ j ∈ K \ J, insert j (J.erase i) ∈ F := by
  classical
  intro J hJ K hK i hi
  obtain ⟨j,hj,hnew⟩ := hF.2 (indicator J) ((indicator_mem_liftFamily_iff F J).mpr hJ)
    (indicator K) ((indicator_mem_liftFamily_iff F K).mpr hK) i
    ((positive_difference_iff J K i).mpr hi)
  have hjKJ := (negative_difference_iff J K j).mp hj
  refine ⟨j,hjKJ,?_⟩
  apply (indicator_mem_liftFamily_iff F _).mp
  rw [indicator_exchange J i j (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hjKJ).2]
  exact hnew

#print axioms indicator_injective
#print axioms subset_sum_indicator
#print axioms liftFamily_isBase
#print axioms one_sided_exchange_of_liftFamily_isBase

end DcaRankIndicator


set_option autoImplicit false
open scoped BigOperators

namespace DcaRankCore

open Finset DiscreteConvex.Combinatorial SteinitzExchange.Duality

theorem integer_sandwich {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (f g : Finset V → ℤ) (hf : IsSubmodular f) (hg : IsSupermodular g)
    (hf0 : f ∅ = 0) (hg0 : g ∅ = 0) (hgf : ∀ X : Finset V, g X ≤ f X) :
    ∃ x : V → ℤ, ∀ X : Finset V,
      g X ≤ ∑ v ∈ X, x v ∧ (∑ v ∈ X, x v) ≤ f X := by
  let fR : Finset V → ℝ := fun X => (f X : ℝ)
  let gR : Finset V → ℝ := fun X => (g X : ℝ)
  have hfR : IsSubmodular fR := by
    intro X Y
    change (f (X ∪ Y) : ℝ) + (f (X ∩ Y) : ℝ) ≤ (f X : ℝ) + (f Y : ℝ)
    exact_mod_cast hf X Y
  have hgR : IsSupermodular gR := by
    intro X Y
    change (g X : ℝ) + (g Y : ℝ) ≤ (g (X ∪ Y) : ℝ) + (g (X ∩ Y) : ℝ)
    exact_mod_cast hg X Y
  have hfR0 : fR ∅ = 0 := by simp [fR, hf0]
  have hgR0 : gR ∅ = 0 := by simp [gR, hg0]
  have hgfR : ∀ X, gR X ≤ fR X := by
    intro X
    change (g X : ℝ) ≤ (f X : ℝ)
    exact_mod_cast hgf X
  obtain ⟨x, hx⟩ := (frank_discrete_separation fR gR hfR hgR hfR0 hgR0 hgfR).2
    (fun X => ⟨f X, rfl⟩) (fun X => ⟨g X, rfl⟩)
  refine ⟨x, fun X => ?_⟩
  have h := hx X
  change (g X : ℝ) ≤ ((∑ v ∈ X, x v : ℤ) : ℝ) ∧
    ((∑ v ∈ X, x v : ℤ) : ℝ) ≤ (f X : ℝ) at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩


variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The normalized integer base system associated to a rank function. -/
def BaseSystem (ρ : Finset V → ℤ) (x : V → ℤ) : Prop :=
  (∀ X : Finset V, (∑ v ∈ X, x v) ≤ ρ X) ∧ (∑ v, x v) = ρ univ

lemma rank_empty (ρ : Finset V → ℤ) (hρ : RankAxioms ρ) : ρ ∅ = 0 := by
  have h := hρ.1 ∅
  simp only [card_empty, Int.natCast_zero] at h
  omega

lemma rankOfFamily_bounds (F : Finset (Finset V)) (X : Finset V) :
    0 ≤ RankOfFamily F X ∧ RankOfFamily F X ≤ (X.card : ℤ) := by
  have h : F.sup (fun J => (X ∩ J).card) ≤ X.card :=
    Finset.sup_le fun J _ => Finset.card_le_card Finset.inter_subset_left
  constructor
  · exact Int.natCast_nonneg _
  · unfold RankOfFamily
    exact_mod_cast h

lemma rankOfFamily_mono (F : Finset (Finset V)) (X Y : Finset V) (hXY : X ⊆ Y) :
    RankOfFamily F X ≤ RankOfFamily F Y := by
  have h : F.sup (fun J => (X ∩ J).card) ≤ F.sup (fun J => (Y ∩ J).card) := by
    apply Finset.sup_mono_fun
    intro J _
    apply Finset.card_le_card
    exact Finset.inter_subset_inter_right hXY
  unfold RankOfFamily
  exact_mod_cast h

/-- Public integer Frank separation constructs a feasible base before any base family is assumed. -/
theorem exists_baseSystem [Nonempty V] (ρ : Finset V → ℤ) (hρ : RankAxioms ρ) :
    ∃ x : V → ℤ, BaseSystem ρ x := by
  have h0 := rank_empty ρ hρ
  let g : Finset V → ℤ := fun X => ρ univ - ρ Xᶜ
  have hg : IsSupermodular g := by
    intro X Y
    have h := hρ.2.2 Xᶜ Yᶜ
    simp only [g, Finset.compl_union, Finset.compl_inter]
    omega
  have hg0 : g ∅ = 0 := by simp [g]
  have hgf : ∀ X : Finset V, g X ≤ ρ X := by
    intro X
    have h := hρ.2.2 X Xᶜ
    simp only [Finset.union_compl, Finset.inter_compl, h0, add_zero] at h
    dsimp [g]
    omega
  obtain ⟨x, hx⟩ := integer_sandwich ρ g hρ.2.2 hg h0 hg0 hgf
  refine ⟨x, (fun X => (hx X).2), ?_⟩
  apply le_antisymm (hx univ).2
  have h := (hx univ).1
  simpa only [g, Finset.compl_univ, h0, sub_zero] using h

lemma coordinate_bounds_of_baseSystem (ρ : Finset V → ℤ) (hρ : RankAxioms ρ)
    (x : V → ℤ) (hx : BaseSystem ρ x) (i : V) : 0 ≤ x i ∧ x i ≤ 1 := by
  have hi := hx.1 {i}
  simp only [Finset.sum_singleton] at hi
  have hr : ρ {i} ≤ 1 := by simpa using (hρ.1 {i}).2
  have hc := hx.1 ({i} : Finset V)ᶜ
  have hm := hρ.2.1 ({i} : Finset V)ᶜ univ (subset_univ _)
  have hs : x i + (∑ v ∈ ({i} : Finset V)ᶜ, x v) = ρ univ := by
    simpa only [Finset.sum_singleton, hx.2] using
      (Finset.sum_add_sum_compl ({i} : Finset V) x)
  omega

lemma binary_of_baseSystem (ρ : Finset V → ℤ) (hρ : RankAxioms ρ)
    (x : V → ℤ) (hx : BaseSystem ρ x) : ∀ i, x i = 0 ∨ x i = 1 := by
  intro i
  have h := coordinate_bounds_of_baseSystem ρ hρ x hx i
  omega

/-- Maximum-rank independent sets obey all rank inequalities as binary vectors. -/
lemma inter_card_le_of_mem_family (ρ : Finset V → ℤ) (hρ : RankAxioms ρ)
    (J : Finset V) (hJ : J ∈ FamilyOfRank ρ) (X : Finset V) :
    ((X ∩ J).card : ℤ) ≤ ρ X := by
  have hJrank : ρ J = (J.card : ℤ) := (Finset.mem_filter.mp hJ).2.1
  have hs := hρ.2.2 (J \ X) (J ∩ X)
  have hd : (J \ X) ∩ (J ∩ X) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hdv := Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).1
    have hiv := Finset.mem_inter.mp (Finset.mem_inter.mp hv).2
    exact hdv.2 hiv.2
  rw [Finset.sdiff_union_inter, hd, rank_empty ρ hρ, add_zero] at hs
  have hb := (hρ.1 (J \ X)).2
  have hm := hρ.2.1 (J ∩ X) X Finset.inter_subset_right
  have hcard : ((J \ X).card : ℤ) + ((J ∩ X).card : ℤ) = (J.card : ℤ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_inter J X)
  rw [Finset.inter_comm X J]
  omega

#print axioms exists_baseSystem
#print axioms binary_of_baseSystem
#print axioms inter_card_le_of_mem_family

end DcaRankCore


set_option autoImplicit false
open scoped BigOperators

namespace DcaRankFamily

section MatroidSymmetry
open Set

theorem symmetric_basis_exchange {α : Type*} (M : Matroid α)
    {X Y : Set α} (hX : M.IsBase X) (hY : M.IsBase Y)
    {e : α} (he : e ∈ X \ Y) :
    ∃ f ∈ Y \ X,
      M.IsBase (insert f (X \ {e})) ∧ M.IsBase (insert e (Y \ {f})) := by
  have heE : e ∈ M.E := hX.subset_ground he.1
  have hC := hY.fundCircuit_isCircuit heE he.2
  have hK := hX.compl_closure_sdiff_singleton_isCocircuit he.1
  have heK : e ∈ M.E \ M.closure (X \ {e}) :=
    ⟨heE, hX.indep.notMem_closure_sdiff_of_mem he.1⟩
  have hn := hC.isCocircuit_inter_nontrivial hK
    ⟨e, M.mem_fundCircuit e Y, heK⟩
  obtain ⟨f, hf, hfe⟩ := hn.exists_ne e
  have hfY : f ∈ Y := by
    have h := M.fundCircuit_subset_insert e Y hf.1
    rcases h with h | h
    · exact (hfe h).elim
    · exact h
  have hfX : f ∉ X := by
    intro h
    exact hf.2.2 (M.subset_closure (X \ {e})
      (sdiff_subset.trans hX.subset_ground) ⟨h, hfe⟩)
  have hecl : e ∈ M.closure Y := by rwa [hY.closure_eq]
  have hi : M.Indep (insert e Y \ {f}) :=
    (hY.indep.mem_fundCircuit_iff hecl he.2).mp hf.1
  refine ⟨f, ⟨hfY, hfX⟩,
    hX.exchange_base_of_notMem_closure he.1 hf.2.2 hf.2.1, ?_⟩
  have hb := hY.exchange_isBase_of_indep' hfY he.2 hi
  simpa only [← insert_sdiff_singleton_comm hfe.symm] using hb


end MatroidSymmetry

open Finset DiscreteConvex.Combinatorial SteinitzExchange.Duality DcaRankIndicator DcaRankCore

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma lifted_rank_eq (F : Finset (Finset V)) (hne : F.Nonempty) (X : Finset V) :
    (liftFamily F).sup' ((liftFamily_nonempty_iff F).mpr hne) (fun x => sumOn x X) =
      RankOfFamily F X := by
  classical
  have hcast := Finset.apply_sup'_eq_sup'_comp hne
    (f := fun J : Finset V => (X ∩ J).card) (fun n : ℕ => (n : ℤ))
    (fun a b => Nat.cast_max a b)
  rw [Finset.sup'_eq_sup] at hcast
  calc
    (liftFamily F).sup' ((liftFamily_nonempty_iff F).mpr hne) (fun x => sumOn x X) =
        F.sup' hne (fun J => sumOn (indicator J) X) := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro x hx
        obtain ⟨J, hJ, hJx⟩ := (mem_liftFamily F x).mp hx
        rw [← hJx]
        exact Finset.le_sup' (fun J => sumOn (indicator J) X) hJ
      · apply Finset.sup'_le
        intro J hJ
        exact Finset.le_sup' (fun x => sumOn x X)
          ((indicator_mem_liftFamily_iff F J).mpr hJ)
    _ = F.sup' hne (fun J => ((X ∩ J).card : ℤ)) := by
      exact Finset.sup'_congr hne rfl (fun J _ => subset_sum_indicator J X)
    _ = RankOfFamily F X := hcast.symm

lemma indicator_system_iff (ρ : Finset V → ℤ) (hρ : RankAxioms ρ) (J : Finset V) :
    BaseSystem ρ (indicator J) ↔ J ∈ FamilyOfRank ρ := by
  constructor
  · intro h
    have hJ := h.1 J
    rw [subset_sum_indicator, inter_self] at hJ
    have hr := (hρ.1 J).2
    have ht := h.2
    rw [total_sum_indicator] at ht
    exact Finset.mem_filter.mpr ⟨mem_univ _, le_antisymm hr hJ, ht⟩
  · intro hJ
    refine ⟨fun X => ?_, ?_⟩
    · rw [subset_sum_indicator]
      exact inter_card_le_of_mem_family ρ hρ J hJ X
    · rw [total_sum_indicator]
      exact (Finset.mem_filter.mp hJ).2.2

lemma eq_indicator_of_binary (x : V → ℤ) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    ∃ J : Finset V, indicator J = x := by
  let J := Finset.univ.filter (fun i => x i = 1)
  refine ⟨J, ?_⟩
  funext i
  rcases hx i with hi | hi <;> simp [indicator, J, hi]

lemma lifted_family_representation (ρ : Finset V → ℤ) (hρ : RankAxioms ρ) (x : V → ℤ) :
    x ∈ liftFamily (FamilyOfRank ρ) ↔ BaseSystem ρ x := by
  constructor
  · intro hx
    obtain ⟨J, hJ, rfl⟩ := (mem_liftFamily (FamilyOfRank ρ) x).mp hx
    exact (indicator_system_iff ρ hρ J).mpr hJ
  · intro hx
    obtain ⟨J, hJx⟩ := eq_indicator_of_binary x (binary_of_baseSystem ρ hρ x hx)
    have hJS : BaseSystem ρ (indicator J) := by rw [hJx]; exact hx
    exact (mem_liftFamily (FamilyOfRank ρ) x).mpr
      ⟨J, (indicator_system_iff ρ hρ J).mp hJS, hJx⟩

lemma familyOfRank_nonempty [Nonempty V] (ρ : Finset V → ℤ) (hρ : RankAxioms ρ) :
    (FamilyOfRank ρ).Nonempty := by
  obtain ⟨x, hx⟩ := exists_baseSystem ρ hρ
  exact (liftFamily_nonempty_iff _).mp
    ⟨x, (lifted_family_representation ρ hρ x).mpr hx⟩

lemma lifted_family_isBase [Nonempty V] (ρ : Finset V → ℤ) (hρ : RankAxioms ρ) :
    IsIntegralBaseSet (liftFamily (FamilyOfRank ρ)) := by
  have hne := (liftFamily_nonempty_iff _).mpr (familyOfRank_nonempty ρ hρ)
  apply (baseSet_iff_submodular_system _ hne).1.mpr
  refine ⟨ρ, hρ.2.2, rank_empty ρ hρ, ?_⟩
  intro x
  exact lifted_family_representation ρ hρ x

/-- The binary base predicate gives a genuine matroid, whose circuit/cocircuit exchange is symmetric. -/
theorem exchangeFamily_of_liftBase (F : Finset (Finset V))
    (hF : IsIntegralBaseSet (liftFamily F)) : ExchangeFamily F := by
  classical
  have hsingle := one_sided_exchange_of_liftFamily_isBase F hF
  let P : Set V → Prop := fun S => ∃ J ∈ F, (J : Set V) = S
  have he : Matroid.ExchangeProperty P := by
    intro X Y hX hY i hi
    obtain ⟨J, hJ, rfl⟩ := hX
    obtain ⟨K, hK, rfl⟩ := hY
    have hi' : i ∈ J \ K := by simpa only [Finset.mem_sdiff, Set.mem_diff, Finset.mem_coe] using hi
    obtain ⟨j, hj, hnew⟩ := hsingle J hJ K hK i hi'
    refine ⟨j, ?_, insert j (J.erase i), hnew, ?_⟩
    · simpa only [Finset.mem_sdiff, Set.mem_diff, Finset.mem_coe] using hj
    · simp only [Finset.coe_insert, Finset.coe_erase]
  obtain ⟨J₀, hJ₀⟩ := (liftFamily_nonempty_iff F).mp hF.1
  let M : Matroid V := Matroid.ofExistsFiniteIsBase Set.univ P
    ⟨(J₀ : Set V), ⟨J₀, hJ₀, rfl⟩, J₀.finite_toSet⟩ he (fun _ _ => Set.subset_univ _)
  have hmem (J : Finset V) (hJ : M.IsBase (J : Set V)) : J ∈ F := by
    change P (J : Set V) at hJ
    obtain ⟨K, hK, hKJ⟩ := hJ
    exact Finset.coe_injective hKJ ▸ hK
  intro J hJ K hK i hi
  have hJM : M.IsBase (J : Set V) := ⟨J, hJ, rfl⟩
  have hKM : M.IsBase (K : Set V) := ⟨K, hK, rfl⟩
  have hi' : i ∈ (J : Set V) \ (K : Set V) := by
    simpa only [Finset.mem_sdiff, Set.mem_diff, Finset.mem_coe] using hi
  obtain ⟨j, hj, hbJ, hbK⟩ := symmetric_basis_exchange M hJM hKM hi'
  refine ⟨j, ?_, ?_, ?_⟩
  · simpa only [Finset.mem_sdiff, Set.mem_diff, Finset.mem_coe] using hj
  · apply hmem
    simpa only [Finset.coe_insert, Finset.coe_erase] using hbJ
  · apply hmem
    simpa only [Finset.coe_insert, Finset.coe_erase] using hbK

lemma rank_family_inverse [Nonempty V] (ρ : Finset V → ℤ) (hρ : RankAxioms ρ) :
    RankOfFamily (FamilyOfRank ρ) = ρ := by
  funext X
  have hne := familyOfRank_nonempty ρ hρ
  have h := (baseSet_iff_submodular_system (liftFamily (FamilyOfRank ρ))
    ((liftFamily_nonempty_iff _).mpr hne)).2.2.1 ρ hρ.2.2 (rank_empty ρ hρ)
      (lifted_family_representation ρ hρ) X
  exact ((lifted_rank_eq _ hne X).symm.trans h.symm)

theorem family_to_rank [Nonempty V] (F : Finset (Finset V)) (hne : F.Nonempty)
    (hF : ExchangeFamily F) :
    RankAxioms (RankOfFamily F) ∧ FamilyOfRank (RankOfFamily F) = F := by
  have hI : IsIntegralBaseSet (liftFamily F) := liftFamily_isBase F hne hF
  have hIne := (liftFamily_nonempty_iff F).mpr hne
  have hchar := baseSet_iff_submodular_system (liftFamily F) hIne
  obtain ⟨f, hf, hf0, hrep⟩ := hchar.1.mp hI
  have hcanon := hchar.2.2.1 f hf hf0 hrep
  have hfr : f = RankOfFamily F := by
    funext X
    exact (hcanon X).trans (lifted_rank_eq F hne X)
  have hr : RankAxioms (RankOfFamily F) := by
    refine ⟨rankOfFamily_bounds F, rankOfFamily_mono F, ?_⟩
    rw [← hfr]
    exact hf
  refine ⟨hr, ?_⟩
  ext J
  rw [← indicator_system_iff _ hr J, ← indicator_mem_liftFamily_iff F J]
  rw [hfr] at hrep
  exact (hrep (indicator J)).symm

theorem rank_to_family [Nonempty V] (ρ : Finset V → ℤ) (hρ : RankAxioms ρ) :
    (FamilyOfRank ρ).Nonempty ∧ ExchangeFamily (FamilyOfRank ρ) ∧
      RankOfFamily (FamilyOfRank ρ) = ρ := by
  exact ⟨familyOfRank_nonempty ρ hρ,
    exchangeFamily_of_liftBase _ (lifted_family_isBase ρ hρ), rank_family_inverse ρ hρ⟩

#print axioms family_to_rank
#print axioms rank_to_family

end DcaRankFamily


set_option autoImplicit false

namespace DcaRankFinal
open Finset DiscreteConvex.Combinatorial DcaRankCore DcaRankFamily

theorem correspondence {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ F : Finset (Finset V), F.Nonempty → ExchangeFamily F →
        RankAxioms (RankOfFamily F) ∧ FamilyOfRank (RankOfFamily F) = F) ∧
    (∀ ρ : Finset V → ℤ, RankAxioms ρ →
        (FamilyOfRank ρ).Nonempty ∧ ExchangeFamily (FamilyOfRank ρ) ∧
          RankOfFamily (FamilyOfRank ρ) = ρ) := by
  classical
  by_cases hV : Nonempty V
  · letI : Nonempty V := hV
    exact ⟨family_to_rank, rank_to_family⟩
  · letI : IsEmpty V := not_nonempty_iff.mp hV
    have hs : ∀ J : Finset V, J = ∅ := Finset.eq_empty_of_isEmpty
    have hFempty (F : Finset (Finset V)) (hne : F.Nonempty) : F = {∅} := by
      ext J
      simp only [Finset.mem_singleton]
      constructor
      · intro _
        exact hs J
      · intro hJ
        subst J
        obtain ⟨K, hK⟩ := hne
        simpa only [hs K] using hK
    have hzero (ρ : Finset V → ℤ) (hρ : RankAxioms ρ) : ρ = fun _ => 0 := by
      funext J
      rw [hs J]
      exact rank_empty ρ hρ
    have hfamily : FamilyOfRank (fun _ : Finset V => (0 : ℤ)) = {∅} := by
      ext J
      simp only [FamilyOfRank, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rw [hs J]
      simp
    have hrank : RankOfFamily ({∅} : Finset (Finset V)) = fun _ => 0 := by
      funext X
      simp [RankOfFamily]
    have haxioms : RankAxioms (fun _ : Finset V => (0 : ℤ)) := by
      refine ⟨fun X => ⟨le_rfl, Int.natCast_nonneg _⟩, ?_, ?_⟩
      · intro X Y hXY
        exact le_rfl
      · intro X Y
        exact le_rfl
    have hexchange : ExchangeFamily ({∅} : Finset (Finset V)) := by
      intro J hJ K hK i hi
      have hJ' : J = ∅ := Finset.mem_singleton.mp hJ
      simp [hJ'] at hi
    constructor
    · intro F hne hF
      rw [hFempty F hne, hrank, hfamily]
      exact ⟨haxioms, rfl⟩
    · intro ρ hρ
      rw [hzero ρ hρ, hfamily, hrank]
      exact ⟨Finset.singleton_nonempty _, hexchange, rfl⟩

#print axioms correspondence
end DcaRankFinal

open DiscreteConvex.Combinatorial

theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ 𝓑 : Finset (Finset V), 𝓑.Nonempty → ExchangeFamily 𝓑 →
        RankAxioms (RankOfFamily 𝓑) ∧ FamilyOfRank (RankOfFamily 𝓑) = 𝓑) ∧
    (∀ ρ : Finset V → ℤ, RankAxioms ρ →
        (FamilyOfRank ρ).Nonempty ∧ ExchangeFamily (FamilyOfRank ρ) ∧
          RankOfFamily (FamilyOfRank ρ) = ρ) := by
  exact DcaRankFinal.correspondence

#print axioms solution
