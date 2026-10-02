-- Prove2me | solution 1 for DiscreteConvex.Combinatorial.valuated_matroid_characterization
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T02:20:27.155986+00:00
-- url     : https://prove2.me/submissions/e1c12af5-7266-4c1b-ba38-d09496009c14

import Definitions.Def_DiscreteConvex_Combinatorial_ExchangeFamily
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega
import Definitions.Def_DiscreteConvex_Combinatorial_IsValuation
import Definitions.Def_DiscreteConvex_Combinatorial_MaximizerFamily
import Definitions.Def_DiscreteConvex_Combinatorial_PerturbedValuation
import Theorems.Thm_SteinitzExchange_Extension_exc_iff_argmax_isIntegralBaseSet
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

set_option autoImplicit false

/- Component: Solutions/DcaIndicatorEmbedding.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace DcaValuatedIndicator

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

end DcaValuatedIndicator
end

/- Component: Solutions/DcaValuationCharacterization.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace DcaValuation
open DcaValuatedIndicator DiscreteConvex.Combinatorial
open SteinitzExchange.Extension

/-- Keep the original bounded-forall decision procedure before introducing a finite ground type. -/
lemma mem_maximizers {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (ω : Finset α → ℝ) (J : Finset α) :
    J ∈ MaximizerFamily F ω ↔ J ∈ F ∧ ∀ K ∈ F, ω K ≤ ω J := by
  classical
  exact Finset.mem_filter

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def decode (x : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => x v = 1)

lemma decode_indicator (J : Finset V) : decode (indicator J) = J := by
  classical
  ext v
  by_cases hv : v ∈ J <;> simp [decode, indicator, hv]

noncomputable def liftedWeight (ω : Finset V → ℝ) (x : V → ℤ) : ℝ := ω (decode x)

lemma liftedWeight_indicator (ω : Finset V → ℝ) (J : Finset V) :
    liftedWeight ω (indicator J) = ω J := by rw [liftedWeight, decode_indicator]

lemma indicator_reverse_exchange (K : Finset V) (i j : V) (hj : j ∈ K) (hi : i ∉ K) :
    indicator (insert i (K.erase j)) = indicator K + chi i - chi j := by
  rw [indicator_exchange K j i hj hi]
  abel

lemma valuation_iff_exc (F : Finset (Finset V)) (ω : Finset V → ℝ) :
    IsValuation F ω ↔ SatisfiesEXC (liftFamily F) (liftedWeight ω) := by
  classical
  constructor
  · intro hω x hx y hy i hi
    obtain ⟨J,hJ,rfl⟩ := (mem_liftFamily F x).mp hx
    obtain ⟨K,hK,rfl⟩ := (mem_liftFamily F y).mp hy
    have hiJK := (positive_difference_iff J K i).mp hi
    obtain ⟨j,hjKJ,hJ',hK',hineq⟩ := hω J hJ K hK i hiJK
    have hleft := indicator_exchange J i j (Finset.mem_sdiff.mp hiJK).1
      (Finset.mem_sdiff.mp hjKJ).2
    have hright := indicator_reverse_exchange K i j (Finset.mem_sdiff.mp hjKJ).1
      (Finset.mem_sdiff.mp hiJK).2
    refine ⟨j,(negative_difference_iff J K j).mpr hjKJ,?_,?_,?_⟩
    · rw [← hleft]; exact (indicator_mem_liftFamily_iff F _).mpr hJ'
    · rw [← hright]; exact (indicator_mem_liftFamily_iff F _).mpr hK'
    · simpa only [← hleft,← hright,liftedWeight_indicator] using hineq
  · intro hω J hJ K hK i hiJK
    obtain ⟨j,hj,hJ',hK',hineq⟩ := hω (indicator J)
      ((indicator_mem_liftFamily_iff F J).mpr hJ) (indicator K)
      ((indicator_mem_liftFamily_iff F K).mpr hK) i ((positive_difference_iff J K i).mpr hiJK)
    have hjKJ := (negative_difference_iff J K j).mp hj
    have hleft := indicator_exchange J i j (Finset.mem_sdiff.mp hiJK).1
      (Finset.mem_sdiff.mp hjKJ).2
    have hright := indicator_reverse_exchange K i j (Finset.mem_sdiff.mp hjKJ).1
      (Finset.mem_sdiff.mp hiJK).2
    refine ⟨j,hjKJ,?_,?_,?_⟩
    · apply (indicator_mem_liftFamily_iff F _).mp; simpa only [hleft] using hJ'
    · apply (indicator_mem_liftFamily_iff F _).mp; simpa only [hright] using hK'
    · simpa only [← hleft,← hright,liftedWeight_indicator] using hineq

lemma pairing_indicator (p : V → ℝ) (J : Finset V) :
    pairing p (toReal (indicator J)) = ∑ v ∈ J, p v := by
  classical
  simp [pairing,toReal,indicator,mul_ite,Finset.sum_ite_mem]

lemma perturb_liftedWeight (ω : Finset V → ℝ) (p : V → ℝ) (J : Finset V) :
    perturb (liftedWeight ω) p (indicator J) = PerturbedValuation ω (-p) J := by
  simp [perturb,liftedWeight_indicator,pairing_indicator,PerturbedValuation,Finset.sum_neg_distrib]

lemma argmax_lift (F : Finset (Finset V)) (ω : Finset V → ℝ) (p : V → ℝ) :
    argmaxB (liftFamily F) (perturb (liftedWeight ω) p) =
      liftFamily (MaximizerFamily F (PerturbedValuation ω (-p))) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hxF,hmax⟩ := Finset.mem_filter.mp hx
    obtain ⟨J,hJ,rfl⟩ := (mem_liftFamily F x).mp hxF
    apply (mem_liftFamily _ _).mpr
    refine ⟨J,(mem_maximizers _ _ _).mpr ⟨hJ,?_⟩,rfl⟩
    intro K hK
    simpa only [perturb_liftedWeight] using hmax (indicator K)
      ((indicator_mem_liftFamily_iff F K).mpr hK)
  · intro hx
    obtain ⟨J,hJ,rfl⟩ := (mem_liftFamily _ x).mp hx
    obtain ⟨hJF,hmax⟩ := (mem_maximizers _ _ _).mp hJ
    apply Finset.mem_filter.mpr
    refine ⟨(indicator_mem_liftFamily_iff F J).mpr hJF,?_⟩
    intro y hy
    obtain ⟨K,hK,rfl⟩ := (mem_liftFamily F y).mp hy
    simpa only [perturb_liftedWeight] using hmax K hK

lemma sum_exchange (p : V → ℝ) (J : Finset V) (i j : V)
    (hi : i ∈ J) (hj : j ∉ J) :
    (∑ v ∈ insert j (J.erase i), p v) = (∑ v ∈ J, p v) - p i + p j := by
  rw [Finset.sum_insert (fun h => hj (Finset.mem_of_mem_erase h))]
  have h := Finset.sum_erase_add J p hi
  linarith

lemma valuation_perturb (F : Finset (Finset V)) (ω : Finset V → ℝ)
    (hω : IsValuation F ω) (p : V → ℝ) : IsValuation F (PerturbedValuation ω p) := by
  intro J hJ K hK i hi
  obtain ⟨j,hj,hJ',hK',hineq⟩ := hω J hJ K hK i hi
  refine ⟨j,hj,hJ',hK',?_⟩
  have hleft := sum_exchange p J i j (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).2
  have hright := sum_exchange p K j i (Finset.mem_sdiff.mp hj).1 (Finset.mem_sdiff.mp hi).2
  unfold PerturbedValuation
  linarith

lemma maximizers_nonempty (F : Finset (Finset V)) (hne : F.Nonempty) (ω : Finset V → ℝ) :
    (MaximizerFamily F ω).Nonempty := by
  classical
  obtain ⟨J,hJ,hmax⟩ := Finset.exists_max_image F ω hne
  exact ⟨J,(mem_maximizers _ _ _).mpr ⟨hJ,hmax⟩⟩

lemma maximizers_exchange (F : Finset (Finset V)) (ω : Finset V → ℝ)
    (hω : IsValuation F ω) : ExchangeFamily (MaximizerFamily F ω) := by
  classical
  intro J hJ K hK i hi
  obtain ⟨hJF,hJmax⟩ := (mem_maximizers _ _ _).mp hJ
  obtain ⟨hKF,hKmax⟩ := (mem_maximizers _ _ _).mp hK
  obtain ⟨j,hj,hJ',hK',hineq⟩ := hω J hJF K hKF i hi
  have hleJ := hJmax _ hJ'
  have hleK := hKmax _ hK'
  refine ⟨j,hj,(mem_maximizers _ _ _).mpr ⟨hJ',?_⟩,(mem_maximizers _ _ _).mpr ⟨hK',?_⟩⟩
  · intro L hL; have hLJ := hJmax L hL; linarith
  · intro L hL; have hLK := hKmax L hL; linarith

theorem valuated_matroid_characterization_checked (F : Finset (Finset V))
    (hne : F.Nonempty) (hF : ExchangeFamily F) (ω : Finset V → ℝ) :
    IsValuation F ω ↔ ∀ p : V → ℝ,
      (MaximizerFamily F (PerturbedValuation ω p)).Nonempty ∧
      ExchangeFamily (MaximizerFamily F (PerturbedValuation ω p)) := by
  classical
  constructor
  · intro hω p
    exact ⟨maximizers_nonempty F hne _,maximizers_exchange F _ (valuation_perturb F ω hω p)⟩
  · intro hmax
    by_cases hV : Nonempty V
    · letI := hV
      apply (valuation_iff_exc F ω).mpr
      apply (SteinitzExchange.Extension.exc_iff_argmax_isIntegralBaseSet
        (liftFamily F) (liftFamily_isBase F hne hF) (liftedWeight ω)).mpr
      intro p
      rw [argmax_lift]
      exact liftFamily_isBase _ (hmax (-p)).1 (hmax (-p)).2
    · intro J hJ K hK i hi
      exact False.elim (hV ⟨i⟩)

#print axioms valuation_iff_exc
#print axioms argmax_lift
#print axioms valuation_perturb
#print axioms maximizers_exchange
#print axioms valuated_matroid_characterization_checked

end DcaValuation
end

section
open DiscreteConvex.Combinatorial

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (𝓑 : Finset (Finset V)) (hne : 𝓑.Nonempty) (hexch : ExchangeFamily 𝓑) (ω : Finset V → ℝ) :
    IsValuation 𝓑 ω ↔
      ∀ p : V → ℝ, (MaximizerFamily 𝓑 (PerturbedValuation ω p)).Nonempty ∧
        ExchangeFamily (MaximizerFamily 𝓑 (PerturbedValuation ω p)) := by
  exact DcaValuation.valuated_matroid_characterization_checked 𝓑 hne hexch ω


#print axioms solution
end
