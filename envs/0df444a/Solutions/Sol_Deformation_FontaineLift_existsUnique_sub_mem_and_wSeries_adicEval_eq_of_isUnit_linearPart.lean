-- Prove2me | solution 1 for Deformation.FontaineLift.existsUnique_sub_mem_and_wSeries_adicEval_eq_of_isUnit_linearPart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/61529e6e-dbc0-50ad-b75d-a3066e854207

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_Dieudonne_FontaineFunctor
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_Deformation_PLoc_wPartialSum_adicEval_add_sub_sub_algebraMap_mul_sum_mem_powSub
import Theorems.Thm_Deformation_PLoc_wPartialSum_adicEval_add_sub_sub_algebraMap_mul_add_mem_powSub_two
import Theorems.Thm_Matrix_isUnit_of_isUnit_map_of_le_jacobson_bot
import Theorems.Thm_Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent
import Theorems.Thm_Deformation_FontaineLift_isPadicLimit_wPartialSum_adicEval
import Theorems.Thm_Deformation_FontaineLift_wSeries_adicEval_sub_wSeries_adicEval_mem_powSub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_FontaineLift_existsUnique_sub_mem_and_wSeries_adicEval_eq_of_isUnit_linearPart

universe u v

set_option autoImplicit false

open MvPowerSeries

namespace Deformation
p2m_export "Deformation" "PLoc.invPow_zero PLoc.powSub PLoc.pSub PLoc.mem_powSub_iff PLoc.algebraMap_mem_powSub_of_mem PLoc.powSub_le_powSub_of_le PLoc.mem_span_pow_of_invPow_mul_algebraMap_mem_powSub PLoc.eq_zero_of_forall_mem_powSub PLoc.wPartialSum PLoc.wSeries PLoc.wPartialSum_adicEval_add_sub_sub_algebraMap_mul_sum_mem_powSub PLoc.wPartialSum_adicEval_add_sub_sub_algebraMap_mul_add_mem_powSub_two FontaineLift.isPadicLimit_wPartialSum_adicEval FontaineLift.wSeries_adicEval_sub_wSeries_adicEval_mem_powSub"
namespace FontaineLift
p2m_export "Deformation.FontaineLift" "isPadicLimit_wPartialSum_adicEval wSeries_adicEval_sub_wSeries_adicEval_mem_powSub"
namespace HeartC12
p2m_open "Deformation.FontaineLift Deformation"

section Series

variable {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}

private theorem mem_pow_span_X_of_forall_le_degree (e : ℕ) :
    ∀ f : MvPowerSeries (Fin d) 𝓞, (∀ μ : Fin d →₀ ℕ, MvPowerSeries.coeff μ f ≠ 0 → e ≤ μ.degree) →
      f ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) ^ e := by
  classical
  induction e with
  | zero => intro f _; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ e ih =>
    intro f hf
    let g : Fin d → MvPowerSeries (Fin d) 𝓞 := fun t μ' =>
      if ∀ t' : Fin d, t' < t → μ' t' = 0 then MvPowerSeries.coeff (μ' + Finsupp.single t 1) f else 0
    have hg : ∀ t μ', MvPowerSeries.coeff μ' (g t) =
        if ∀ t' : Fin d, t' < t → μ' t' = 0 then MvPowerSeries.coeff (μ' + Finsupp.single t 1) f else 0 :=
      fun _ _ => rfl
    have hdec : f = ∑ t : Fin d, X t * g t := by
      ext μ
      rw [map_sum]
      have hterm : ∀ t : Fin d, MvPowerSeries.coeff μ (X t * g t) =
          if 1 ≤ μ t ∧ ∀ t' : Fin d, t' < t → μ t' = 0 then MvPowerSeries.coeff μ f else 0 := by
        intro t
        rw [X_def, coeff_monomial_mul, one_mul]
        by_cases h1 : 1 ≤ μ t
        · have hle : Finsupp.single t 1 ≤ μ := Finsupp.single_le_iff.2 h1
          rw [if_pos hle, hg, tsub_add_cancel_of_le hle]
          have hiff : (∀ t' : Fin d, t' < t → (μ - Finsupp.single t 1 : Fin d →₀ ℕ) t' = 0) ↔
              (∀ t' : Fin d, t' < t → μ t' = 0) := by
            refine forall₂_congr fun t' ht' => ?_
            rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (ne_of_lt ht').symm, tsub_zero]
          by_cases hc : ∀ t' : Fin d, t' < t → μ t' = 0
          · rw [if_pos (hiff.2 hc), if_pos ⟨h1, hc⟩]
          · rw [if_neg (fun h => hc (hiff.1 h)), if_neg (fun h => hc h.2)]
        · have hle : ¬ Finsupp.single t 1 ≤ μ := fun h => h1 (Finsupp.single_le_iff.1 h)
          rw [if_neg hle, if_neg (fun h => h1 h.1)]
      simp_rw [hterm]
      by_cases hμ : μ = 0
      · subst hμ
        have h0 : MvPowerSeries.coeff (0 : Fin d →₀ ℕ) f = 0 := by
          by_contra h
          have := hf 0 h
          simp at this
        simp [h0]
      · have hne : μ.support.Nonempty := Finsupp.support_nonempty_iff.2 hμ
        let t₀ := μ.support.min' hne
        have ht₀ : μ t₀ ≠ 0 := Finsupp.mem_support_iff.1 (Finset.min'_mem _ _)
        have hmin : ∀ t' : Fin d, t' < t₀ → μ t' = 0 := by
          intro t' ht'
          by_contra h
          exact absurd (Finset.min'_le μ.support t' (Finsupp.mem_support_iff.2 h)) (not_le.2 ht')
        rw [Finset.sum_eq_single t₀]
        · rw [if_pos ⟨Nat.one_le_iff_ne_zero.2 ht₀, hmin⟩]
        · intro t _ ht
          rw [if_neg]
          rintro ⟨h1, h2⟩
          rcases lt_or_gt_of_ne ht with hlt | hgt
          · exact absurd (hmin t hlt) (Nat.one_le_iff_ne_zero.1 h1)
          · exact ht₀ (h2 t₀ hgt)
        · intro h; exact absurd (Finset.mem_univ t₀) h
    rw [hdec]
    refine Ideal.sum_mem _ fun t _ => ?_
    rw [pow_succ']
    refine Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_range_self t)) (ih (g t) fun μ' hμ' => ?_)
    rw [hg] at hμ'
    split_ifs at hμ' with hcond
    · have := hf _ hμ'
      rw [map_add, Finsupp.degree_single] at this
      omega
    · exact absurd rfl hμ'

private theorem mem_span_X_of_constantCoeff_eq_zero (f : MvPowerSeries (Fin d) 𝓞)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) := by
  have := mem_pow_span_X_of_forall_le_degree 1 f fun μ hμ => by
    rw [Nat.one_le_iff_ne_zero]
    intro hdeg
    rw [Finsupp.degree_eq_zero_iff] at hdeg
    subst hdeg
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hμ
    exact hμ hf
  rwa [pow_one] at this

end Series

section Eval

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {d : ℕ}
  {g : Type v} [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
  (x : Fin d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical)

include hx in

private theorem adicEval_mem_span_range (f : MvPowerSeries (Fin d) 𝓞) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvFormalGroup.adicEval (Ideal.span {(p : g)}) x f ∈ Ideal.span (Set.range x) := by
  have hmem := mem_span_X_of_constantCoeff_eq_zero f hf
  have h := Ideal.mem_map_of_mem (MvFormalGroup.adicEvalAlgHom (R := 𝓞) (Ideal.span {(p : g)}) hx) hmem
  rw [Ideal.map_span, ← Set.range_comp] at h
  have hfun : (⇑(MvFormalGroup.adicEvalAlgHom (R := 𝓞) (Ideal.span {(p : g)}) hx) ∘
      (X : Fin d → MvPowerSeries (Fin d) 𝓞)) = x := by
    funext s
    rw [Function.comp_apply, MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_X]
  rw [hfun, MvFormalGroup.coe_adicEvalAlgHom] at h
  exact h

include hx in

private theorem adicEval_sub_algebraMap_mem_span_range (f : MvPowerSeries (Fin d) 𝓞) :
    MvFormalGroup.adicEval (Ideal.span {(p : g)}) x f - algebraMap 𝓞 g (MvPowerSeries.constantCoeff f) ∈
      Ideal.span (Set.range x) := by
  have h := adicEval_mem_span_range p x hx (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f))
    (by rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self])
  rw [← MvFormalGroup.coe_adicEvalAlgHom (Ideal.span {(p : g)}) hx, map_sub] at h
  rw [← MvFormalGroup.coe_adicEvalAlgHom (Ideal.span {(p : g)}) hx]
  convert h using 2
  rw [show MvPowerSeries.C (MvPowerSeries.constantCoeff f) =
    algebraMap 𝓞 (MvPowerSeries (Fin d) 𝓞) (MvPowerSeries.constantCoeff f) from rfl, AlgHom.commutes]

include hx in
omit [IsAdicComplete (Ideal.span {(p : g)}) g] in

private theorem exists_pow_span_range_le :
    ∃ K : ℕ, 1 ≤ K ∧ Ideal.span (Set.range x) ^ K ≤ Ideal.span {(p : g)} := by
  obtain ⟨K₀, hK₀⟩ : ∃ K : ℕ, Ideal.span (Set.range x) ^ K ≤ Ideal.span {(p : g)} :=
    Ideal.exists_pow_le_of_le_radical_of_fg (Ideal.span_le.2 (Set.range_subset_iff.2 hx))
      (Submodule.fg_span (Set.finite_range x))
  exact ⟨max K₀ 1, le_max_right _ _, le_trans (Ideal.pow_le_pow_right (le_max_left _ _)) hK₀⟩

end Eval

section Objects

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {d : ℕ} (a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞)
  {g : Type v} [CommRing g] [Algebra 𝓞 g]

private noncomputable def Da (i : Fin d) (n : ℕ) (j : Fin d) : MvPowerSeries (Fin d) 𝓞 :=
  fun m => ((m j + 1 : ℕ) : 𝓞) * MvPowerSeries.coeff (m + Finsupp.single j 1) (a i n)

private theorem coeff_Da (i : Fin d) (n : ℕ) (j : Fin d) (m : Fin d →₀ ℕ) :
    (Da a i n j).coeff m = ((m j + 1 : ℕ) : 𝓞) * (a i n).coeff (m + Finsupp.single j 1) := rfl

private theorem constantCoeff_Da (i : Fin d) (n : ℕ) (j : Fin d) :
    MvPowerSeries.constantCoeff (Da a i n j) = (a i n).coeff (Finsupp.single j 1) := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Da, zero_add, Finsupp.coe_zero, Pi.zero_apply,
    zero_add, Nat.cast_one, one_mul]

private noncomputable def uu (x : Fin d → g) (i : Fin d) (n : ℕ) : g :=
  MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a i n)

private noncomputable def DD (x : Fin d → g) (i : Fin d) (n : ℕ) (j : Fin d) : g :=
  MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (Da a i n j)

private noncomputable def Lmat (x : Fin d → g) (N : ℕ) : Matrix (Fin d) (Fin d) g :=
  Matrix.of fun i j => ∑ n ∈ Finset.range N, uu p a x i n ^ (p ^ n - 1) * DD p a x i n j

private noncomputable def Qmat (x : Fin d → g) (N : ℕ) : Matrix (Fin d) (Fin d) g :=
  Matrix.of fun i j => ∑ n ∈ Finset.Ico 1 N, uu p a x i n ^ (p ^ n - 2) * DD p a x i n j ^ 2

private noncomputable def α (x : Fin d → g) (i : Fin d) : Localization.Away (p : g) :=
  Deformation.PLoc.wSeries p fun n => uu p a x i n

private noncomputable def S (x : Fin d → g) (i : Fin d) (N : ℕ) : Localization.Away (p : g) :=
  Deformation.PLoc.wPartialSum p (fun n => uu p a x i n) N

end Objects

section Step

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] {d : ℕ} (a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞)
  (ha : ∀ i n, MvPowerSeries.constantCoeff (a i n) = 0)
  {g : Type v} [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
  (x : Fin d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical)
  (K : ℕ) (hK : Ideal.span (Set.range x) ^ K ≤ Ideal.span {(p : g)})
  (Ns : ℕ) (hNs : K + 2 ≤ p ^ Ns)

omit [Fact p.Prime] in
include hx ha in
private theorem uu_mem (i : Fin d) (n : ℕ) : uu p a x i n ∈ Ideal.span (Set.range x) :=
  adicEval_mem_span_range p x hx (a i n) (ha i n)

include hx ha hK hNs in

private theorem uu_pow_mem (i : Fin d) (n : ℕ) (hn : Ns ≤ n) (e : ℕ) (he : p ^ n - 2 ≤ e) :
    uu p a x i n ^ e ∈ Ideal.span {(p : g)} := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h1 : p ^ Ns ≤ p ^ n := Nat.pow_le_pow_right hp1 hn
  have hKe : K ≤ e := by omega
  exact hK (Ideal.pow_le_pow_right hKe (Ideal.pow_mem_pow (uu_mem p a ha x hx i n) e))

include hx ha hK hNs in

private theorem Lmat_sub_Lmat_mem (N : ℕ) (hN : Ns ≤ N) (i j : Fin d) :
    Lmat p a x N i j - Lmat p a x Ns i j ∈ Ideal.span {(p : g)} := by
  simp only [Lmat, Matrix.of_apply]
  rw [← Finset.sum_range_add_sum_Ico _ hN, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun n hn => ?_
  rw [Finset.mem_Ico] at hn
  exact Ideal.mul_mem_right _ _ (uu_pow_mem p a ha x hx K hK Ns hNs i n hn.1 _ (by omega))

include hx ha hK hNs in

private theorem Qmat_sub_Qmat_mem (N : ℕ) (hN : Ns ≤ N) (i j : Fin d) :
    Qmat p a x N i j - Qmat p a x Ns i j ∈ Ideal.span {(p : g)} := by
  have hNs1 : 1 ≤ Ns := by
    rcases Nat.eq_zero_or_pos Ns with h | h
    · subst h; simp at hNs
    · exact h
  simp only [Qmat, Matrix.of_apply]
  rw [← Finset.sum_Ico_consecutive _ hNs1 hN, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun n hn => ?_
  rw [Finset.mem_Ico] at hn
  exact Ideal.mul_mem_right _ _ (uu_pow_mem p a ha x hx K hK Ns hNs i n hn.1 _ le_rfl)

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : g)}) g] in

private theorem algebraMap_pow_mul_mem_powSub (r : ℕ) (z : g) (hz : z ∈ Ideal.span {(p : g)}) :
    algebraMap g (Localization.Away (p : g)) ((p : g) ^ r * z) ∈ Deformation.PLoc.powSub p g (r + 1) := by
  refine Deformation.PLoc.algebraMap_mem_powSub_of_mem p ?_
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  exact Ideal.mem_span_singleton'.2 ⟨c, by rw [pow_succ]; ring⟩

include ha hx hK hNs in

private theorem step_mem (r : ℕ) (hr : 1 ≤ r) (h2 : p ≠ 2 ∨ 2 ≤ r) (y : Fin d → g) (i : Fin d) :
    α p a (fun j => x j + (p : g) ^ r * y j) i - α p a x i -
        algebraMap g (Localization.Away (p : g)) ((p : g) ^ r * (Lmat p a x Ns).mulVec y i) ∈
      Deformation.PLoc.powSub p g (r + 1) := by
  set x' : Fin d → g := fun j => x j + (p : g) ^ r * y j with hx'def
  have hx' : ∀ j, x' j ∈ (Ideal.span {(p : g)}).radical := fun j =>
    Ideal.add_mem _ (hx j) (Ideal.le_radical (Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) r hr)))

  obtain ⟨n₁, h₁⟩ := Deformation.FontaineLift.isPadicLimit_wPartialSum_adicEval p (a i) (ha i) g x hx (r + 1)
  obtain ⟨n₂, h₂⟩ := Deformation.FontaineLift.isPadicLimit_wPartialSum_adicEval p (a i) (ha i) g x' hx' (r + 1)
  set M := max (max n₁ n₂) Ns with hMdef
  have hM1 : n₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : n₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hMs : Ns ≤ M := le_max_right _ _
  have e1 : S p a x i M - α p a x i ∈ Deformation.PLoc.powSub p g (r + 1) := h₁ M hM1
  have e2 : S p a x' i M - α p a x' i ∈ Deformation.PLoc.powSub p g (r + 1) := h₂ M hM2

  have e3 : S p a x' i M - S p a x i M -
      algebraMap g (Localization.Away (p : g)) ((p : g) ^ r * (Lmat p a x M).mulVec y i) ∈
      Deformation.PLoc.powSub p g (r + 1) := by
    have h := Deformation.PLoc.wPartialSum_adicEval_add_sub_sub_algebraMap_mul_sum_mem_powSub p d a ha
      (Da a) (fun i n j m => coeff_Da a i n j m) g x hx r hr h2 y i M
    simp only [S, Lmat, Matrix.mulVec, dotProduct, Matrix.of_apply, uu, DD]
    exact h

  have e4 : algebraMap g (Localization.Away (p : g))
      ((p : g) ^ r * ((Lmat p a x M).mulVec y i - (Lmat p a x Ns).mulVec y i)) ∈
      Deformation.PLoc.powSub p g (r + 1) := by
    refine algebraMap_pow_mul_mem_powSub p r _ ?_
    rw [← Pi.sub_apply, ← Matrix.sub_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.sub_apply]
    exact Lmat_sub_Lmat_mem p a ha x hx K hK Ns hNs M hMs i j

  have key := add_mem (add_mem (sub_mem e1 e2) e3) e4
  have : S p a x i M - α p a x i - (S p a x' i M - α p a x' i) +
      (S p a x' i M - S p a x i M -
        algebraMap g (Localization.Away (p : g)) ((p : g) ^ r * (Lmat p a x M).mulVec y i)) +
      algebraMap g (Localization.Away (p : g))
        ((p : g) ^ r * ((Lmat p a x M).mulVec y i - (Lmat p a x Ns).mulVec y i)) =
      α p a x' i - α p a x i -
        algebraMap g (Localization.Away (p : g)) ((p : g) ^ r * (Lmat p a x Ns).mulVec y i) := by
    rw [mul_sub, map_sub]; ring
  rw [this] at key
  exact key

include ha hx hK hNs in

private theorem step_mem_two (hp2 : p = 2) (y : Fin d → g) (i : Fin d) :
    α p a (fun j => x j + (p : g) * y j) i - α p a x i -
        algebraMap g (Localization.Away (p : g)) ((p : g) *
          ((Lmat p a x Ns).mulVec y i + (Qmat p a x Ns).mulVec (fun j => y j ^ 2) i)) ∈
      Deformation.PLoc.powSub p g 2 := by
  set x' : Fin d → g := fun j => x j + (p : g) * y j with hx'def
  have hx' : ∀ j, x' j ∈ (Ideal.span {(p : g)}).radical := fun j =>
    Ideal.add_mem _ (hx j) (Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
  obtain ⟨n₁, h₁⟩ := Deformation.FontaineLift.isPadicLimit_wPartialSum_adicEval p (a i) (ha i) g x hx 2
  obtain ⟨n₂, h₂⟩ := Deformation.FontaineLift.isPadicLimit_wPartialSum_adicEval p (a i) (ha i) g x' hx' 2
  set M := max (max n₁ n₂) Ns with hMdef
  have hM1 : n₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : n₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hMs : Ns ≤ M := le_max_right _ _
  have e1 : S p a x i M - α p a x i ∈ Deformation.PLoc.powSub p g 2 := h₁ M hM1
  have e2 : S p a x' i M - α p a x' i ∈ Deformation.PLoc.powSub p g 2 := h₂ M hM2
  have e3 : S p a x' i M - S p a x i M -
      algebraMap g (Localization.Away (p : g)) ((p : g) *
        ((Lmat p a x M).mulVec y i + (Qmat p a x M).mulVec (fun j => y j ^ 2) i)) ∈
      Deformation.PLoc.powSub p g 2 := by
    have h := Deformation.PLoc.wPartialSum_adicEval_add_sub_sub_algebraMap_mul_add_mem_powSub_two p hp2 d a ha
      (Da a) (fun i n j m => coeff_Da a i n j m) g x hx y i M
    simp only [S, Lmat, Qmat, Matrix.mulVec, dotProduct, Matrix.of_apply, uu, DD]
    exact h
  have e4 : algebraMap g (Localization.Away (p : g)) ((p : g) *
      (((Lmat p a x M).mulVec y i + (Qmat p a x M).mulVec (fun j => y j ^ 2) i) -
        ((Lmat p a x Ns).mulVec y i + (Qmat p a x Ns).mulVec (fun j => y j ^ 2) i))) ∈
      Deformation.PLoc.powSub p g 2 := by
    have h := algebraMap_pow_mul_mem_powSub p (g := g) 1
      (((Lmat p a x M).mulVec y i + (Qmat p a x M).mulVec (fun j => y j ^ 2) i) -
        ((Lmat p a x Ns).mulVec y i + (Qmat p a x Ns).mulVec (fun j => y j ^ 2) i)) ?_
    · rwa [pow_one] at h
    rw [add_sub_add_comm, ← Pi.sub_apply, ← Matrix.sub_mulVec, ← Pi.sub_apply, ← Matrix.sub_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_)
      (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_)
    · rw [Matrix.sub_apply]; exact Lmat_sub_Lmat_mem p a ha x hx K hK Ns hNs M hMs i j
    · rw [Matrix.sub_apply]; exact Qmat_sub_Qmat_mem p a ha x hx K hK Ns hNs M hMs i j
  have key := add_mem (add_mem (sub_mem e1 e2) e3) e4
  have : S p a x i M - α p a x i - (S p a x' i M - α p a x' i) +
      (S p a x' i M - S p a x i M -
        algebraMap g (Localization.Away (p : g)) ((p : g) *
          ((Lmat p a x M).mulVec y i + (Qmat p a x M).mulVec (fun j => y j ^ 2) i))) +
      algebraMap g (Localization.Away (p : g)) ((p : g) *
        (((Lmat p a x M).mulVec y i + (Qmat p a x M).mulVec (fun j => y j ^ 2) i) -
          ((Lmat p a x Ns).mulVec y i + (Qmat p a x Ns).mulVec (fun j => y j ^ 2) i))) =
      α p a x' i - α p a x i -
        algebraMap g (Localization.Away (p : g)) ((p : g) *
          ((Lmat p a x Ns).mulVec y i + (Qmat p a x Ns).mulVec (fun j => y j ^ 2) i)) := by
    rw [mul_sub, map_sub]; ring
  rw [this] at key
  exact key

end Step

section ModP

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] {d : ℕ} (a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞)
  (ha : ∀ i n, MvPowerSeries.constantCoeff (a i n) = 0)
  {g : Type v} [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
  (x : Fin d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical)
  (K : ℕ) (hK : Ideal.span (Set.range x) ^ K ≤ Ideal.span {(p : g)})

private def nn : Ideal (g ⧸ Ideal.span {(p : g)}) :=
  Ideal.map (Ideal.Quotient.mk (Ideal.span {(p : g)})) (Ideal.span (Set.range x))

omit [Fact p.Prime] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g] in
include hK in
private theorem nn_pow_eq_bot : nn p x ^ K = ⊥ := by
  rw [nn, ← Ideal.map_pow, eq_bot_iff, ← Ideal.map_quotient_self (Ideal.span {(p : g)})]
  exact Ideal.map_mono hK

omit [Fact p.Prime] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g] in
include hK in
private theorem nn_le_jacobson : nn p x ≤ (⊥ : Ideal (g ⧸ Ideal.span {(p : g)})).jacobson := by
  intro z hz
  rw [Ideal.mem_jacobson_bot]
  intro w
  have hn : IsNilpotent (z * w) := ⟨K, by
    have h := Ideal.pow_mem_pow (Ideal.mul_mem_right w _ hz) K
    rw [nn_pow_eq_bot p x K hK, Ideal.mem_bot] at h
    exact h⟩
  exact hn.isUnit_add_one

omit [Fact p.Prime] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g] in
private theorem mk_mem_nn {z : g} (hz : z ∈ Ideal.span (Set.range x)) :
    Ideal.Quotient.mk (Ideal.span {(p : g)}) z ∈ nn p x :=
  Ideal.mem_map_of_mem _ hz

omit [Fact p.Prime] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g] in

private theorem nn_eq_of_sub_mem (x' : Fin d → g) (h : ∀ j, x' j - x j ∈ Ideal.span {(p : g)}) :
    nn p x' = nn p x := by
  show Ideal.map _ (Ideal.span (Set.range x')) = Ideal.map _ (Ideal.span (Set.range x))
  have hfun : (⇑(Ideal.Quotient.mk (Ideal.span {(p : g)})) ∘ x') = (⇑(Ideal.Quotient.mk (Ideal.span {(p : g)})) ∘ x) :=
    funext fun j => (Ideal.Quotient.eq).2 (h j)
  rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp, hfun]

include ha hx in

private theorem Lmat_sub_algebraMap_mem (N : ℕ) (hN : 1 ≤ N) (i j : Fin d) :
    Lmat p a x N i j - algebraMap 𝓞 g ((a i 0).coeff (Finsupp.single j 1)) ∈ Ideal.span (Set.range x) := by
  simp only [Lmat, Matrix.of_apply]
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ', pow_zero, Nat.sub_self, pow_zero, one_mul, add_sub_assoc]
  refine Ideal.add_mem _ (Ideal.sum_mem _ fun n _ => Ideal.mul_mem_right _ _ ?_) ?_
  · have h1 : 1 ≤ p ^ (n + 1) - 1 := by
      have : 2 ≤ p ^ (n + 1) := le_trans (Fact.out : p.Prime).two_le
        (Nat.le_self_pow (Nat.succ_ne_zero n) p)
      omega
    exact Ideal.pow_le_self (by omega) (Ideal.pow_mem_pow (uu_mem p a ha x hx i (n + 1)) _)
  · have h := adicEval_sub_algebraMap_mem_span_range p x hx (Da a i 0 j)
    rwa [constantCoeff_Da] at h

omit [Fact p.Prime] in
include ha hx in

private theorem Qmat_mem_of_le (hp2 : p = 2)
    (hlow : ∀ i j : Fin d, j ≤ i → (a i 1).coeff (Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞)})
    (N : ℕ) (i j : Fin d) (hji : j ≤ i) :
    Qmat p a x N i j ∈ Ideal.span (Set.range x) ⊔ Ideal.span {(p : g)} := by
  simp only [Qmat, Matrix.of_apply]
  refine Ideal.sum_mem _ fun n hn => ?_
  rw [Finset.mem_Ico] at hn
  rcases Nat.lt_or_ge 1 n with h1 | h1
  ·
    have h2 : 1 ≤ p ^ n - 2 := by
      have : 4 ≤ p ^ n := by
        rw [hp2]; exact le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) h1)
      omega
    exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _
      (Ideal.pow_le_self (by omega) (Ideal.pow_mem_pow (uu_mem p a ha x hx i n) _)))
  ·
    have hn1 : n = 1 := by omega
    subst hn1
    rw [show p ^ 1 - 2 = 0 by rw [pow_one, hp2], pow_zero, one_mul]
    set c := (a i 1).coeff (Finsupp.single j 1) with hcdef
    have hD : DD p a x i 1 j - algebraMap 𝓞 g c ∈ Ideal.span (Set.range x) := by
      have h := adicEval_sub_algebraMap_mem_span_range p x hx (Da a i 1 j)
      rwa [constantCoeff_Da] at h
    have hsq : DD p a x i 1 j ^ 2 - algebraMap 𝓞 g c ^ 2 ∈ Ideal.span (Set.range x) := by
      rw [sq_sub_sq]
      exact Ideal.mul_mem_left _ _ hD
    have hc : algebraMap 𝓞 g c ^ 2 ∈ Ideal.span {(p : g)} := by
      rw [← map_pow]
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hlow i j hji)
      rw [sq, hcdef, ← ht, map_mul, map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    have := Submodule.add_mem_sup hsq hc
    rwa [sub_add_cancel] at this

variable (hJ : IsUnit ((MvFormalGroup.linearPart fun i => a i 0).map
      (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))))

private def θbar : 𝓞 ⧸ Ideal.span {(p : 𝓞)} →+* (g ⧸ Ideal.span {(p : g)}) ⧸ nn p x :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (nn p x)).comp ((Ideal.Quotient.mk (Ideal.span {(p : g)})).comp
    (algebraMap 𝓞 g))) fun c hc => by
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hc
      simp only [RingHom.comp_apply, map_mul, map_natCast]
      have hp0 : ((p : (g ⧸ Ideal.span {(p : g)}) ⧸ nn p x)) = 0 := by
        rw [← map_natCast ((Ideal.Quotient.mk (nn p x)).comp (Ideal.Quotient.mk (Ideal.span {(p : g)}))) p,
          RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self (p : g)), map_zero]
      rw [hp0, mul_zero]

include ha hx in

private theorem Lmat_map_map (N : ℕ) (hN : 1 ≤ N) :
    ((Lmat p a x N).map (Ideal.Quotient.mk (Ideal.span {(p : g)}))).map (Ideal.Quotient.mk (nn p x)) =
      ((MvFormalGroup.linearPart fun i => a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).map
        (θbar p x) := by
  ext i j
  simp only [Matrix.map_apply, MvFormalGroup.linearPart, Matrix.of_apply, θbar, Ideal.Quotient.lift_mk,
    RingHom.comp_apply]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact mk_mem_nn p x (Lmat_sub_algebraMap_mem p a ha x hx N hN i j)

include ha hx hK hJ in

private theorem isUnit_Lmat_map (N : ℕ) (hN : 1 ≤ N) :
    IsUnit ((Lmat p a x N).map (Ideal.Quotient.mk (Ideal.span {(p : g)}))) := by
  classical
  refine Matrix.isUnit_of_isUnit_map_of_le_jacobson_bot (nn p x) (nn_le_jacobson p x K hK) _ ?_
  rw [Lmat_map_map p a ha x hx N hN, ← RingHom.mapMatrix_apply]
  exact hJ.map _

end ModP

section Newton

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] {d : ℕ} (a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞)
  (ha : ∀ i n, MvPowerSeries.constantCoeff (a i n) = 0)
  (hJ : IsUnit ((MvFormalGroup.linearPart fun i => a i 0).map
      (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))))
  {g : Type v} [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
  (x : Fin d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical)
  (K : ℕ) (hK : Ideal.span (Set.range x) ^ K ≤ Ideal.span {(p : g)})
  (Ns : ℕ) (hNs : K + 2 ≤ p ^ Ns)

omit [Fact p.Prime] in
include hNs in
private theorem one_le_Ns : 1 ≤ Ns := by
  rcases Nat.eq_zero_or_pos Ns with h | h
  · subst h; simp at hNs
  · exact h

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : g)}) g] [Algebra 𝓞 g] in

private theorem exists_lift (v : Fin d → g ⧸ Ideal.span {(p : g)}) :
    ∃ y : Fin d → g, (⇑(Ideal.Quotient.mk (Ideal.span {(p : g)})) ∘ y) = v := by
  choose y hy using fun j => Ideal.Quotient.mk_surjective (v j)
  exact ⟨y, funext hy⟩

include ha hJ hx hK hNs in

private theorem newton_step (ξ : Fin d → Localization.Away (p : g)) (r : ℕ) (h2 : p ≠ 2 ∨ 2 ≤ r + 1)
    (hξ : ∀ i, ξ i - α p a x i ∈ Deformation.PLoc.powSub p g (r + 1)) :
    ∃ y : Fin d → g, ∀ i, ξ i - α p a (fun j => x j + (p : g) ^ (r + 1) * y j) i ∈
      Deformation.PLoc.powSub p g (r + 2) := by
  classical
  have hNs1 := one_le_Ns p K Ns hNs
  set Λ := Lmat p a x Ns with hΛ
  set mkg := Ideal.Quotient.mk (Ideal.span {(p : g)}) with hmkg
  set Λb := Λ.map mkg with hΛb
  have hu : IsUnit Λb := isUnit_Lmat_map p a ha x hx K hK hJ Ns hNs1
  have hdet : IsUnit Λb.det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  choose c hc using fun i => (Deformation.PLoc.mem_powSub_iff p).1 (hξ i)
  obtain ⟨y, hy⟩ := exists_lift p (Λb⁻¹.mulVec (mkg ∘ c))
  have hLy : ∀ i, c i - Λ.mulVec y i ∈ Ideal.span {(p : g)} := by
    intro i
    rw [← Ideal.Quotient.eq, ← hmkg, RingHom.map_mulVec, hy, Matrix.mulVec_mulVec, ← hΛb,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, Function.comp_apply]
  refine ⟨y, fun i => ?_⟩
  have e1 := step_mem p a ha x hx K hK Ns hNs (r + 1) (by omega) h2 y i
  have e2 : ξ i - α p a x i -
      algebraMap g (Localization.Away (p : g)) ((p : g) ^ (r + 1) * Λ.mulVec y i) ∈
      Deformation.PLoc.powSub p g (r + 1 + 1) := by
    rw [← hc i, ← map_sub, ← mul_sub]
    exact algebraMap_pow_mul_mem_powSub p (r + 1) _ (hLy i)
  have key := sub_mem e2 e1
  have : ξ i - α p a x i - algebraMap g (Localization.Away (p : g)) ((p : g) ^ (r + 1) * Λ.mulVec y i) -
      (α p a (fun j => x j + (p : g) ^ (r + 1) * y j) i - α p a x i -
        algebraMap g (Localization.Away (p : g)) ((p : g) ^ (r + 1) * (Lmat p a x Ns).mulVec y i)) =
      ξ i - α p a (fun j => x j + (p : g) ^ (r + 1) * y j) i := by rw [hΛ]; ring
  rw [this] at key
  exact key

include ha hJ hx hK in

private theorem twisted_data (hp2 : p = 2)
    (hJ1 : (MvFormalGroup.linearPart fun i => a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) = 1)
    (hlow : ∀ i j : Fin d, j ≤ i → (a i 1).coeff (Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞)})
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ U : Matrix (Fin d) (Fin d) (g ⧸ Ideal.span {(p : g)}),
      U * (Lmat p a x N).map (Ideal.Quotient.mk (Ideal.span {(p : g)})) = 1 ∧
      (Lmat p a x N).map (Ideal.Quotient.mk (Ideal.span {(p : g)})) * U = 1 ∧
      ∀ i j : Fin d, j ≤ i →
        (U * (Qmat p a x N).map (Ideal.Quotient.mk (Ideal.span {(p : g)}))) i j ∈ nn p x := by
  classical
  set mkg := Ideal.Quotient.mk (Ideal.span {(p : g)}) with hmkg
  set Λb := (Lmat p a x N).map mkg with hΛb
  set Θb := (Qmat p a x N).map mkg with hΘb
  have hu : IsUnit Λb := isUnit_Lmat_map p a ha x hx K hK hJ N hN
  have hdet : IsUnit Λb.det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  refine ⟨Λb⁻¹, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet, fun i j hji => ?_⟩

  have hΛ1 : Λb.map (Ideal.Quotient.mk (nn p x)) = 1 := by
    rw [hΛb, hmkg, Lmat_map_map p a ha x hx N hN, hJ1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hU1 : (Λb⁻¹).map (Ideal.Quotient.mk (nn p x)) = 1 := by
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) (g ⧸ Ideal.span {(p : g)}) =>
      M.map (Ideal.Quotient.mk (nn p x))) (Matrix.nonsing_inv_mul Λb hdet)
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hΛ1, mul_one,
      Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hUe : ∀ i l, Λb⁻¹ i l - (1 : Matrix (Fin d) (Fin d) (g ⧸ Ideal.span {(p : g)})) i l ∈ nn p x := by
    intro i l
    rw [← Ideal.Quotient.eq]
    have h := congrFun (congrFun hU1 i) l
    rw [Matrix.map_apply] at h
    rw [h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hΘ : ∀ l, j ≤ l → Θb l j ∈ nn p x := by
    intro l hjl
    rw [hΘb, Matrix.map_apply, hmkg]
    have h := Qmat_mem_of_le p a ha x hx hp2 hlow N l j hjl
    have h' := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {(p : g)})) h
    rw [Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq] at h'
    exact h'

  rw [Matrix.mul_apply]
  have hsplit : ∑ l, Λb⁻¹ i l * Θb l j =
      ∑ l, (Λb⁻¹ i l - (1 : Matrix (Fin d) (Fin d) (g ⧸ Ideal.span {(p : g)})) i l) * Θb l j + Θb i j := by
    simp only [sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_add_cancel]
  rw [hsplit]
  exact Ideal.add_mem _ (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hUe i l)) (hΘ i hji)

include ha hJ hx hK hNs in

private theorem newton_step_two [CharP (g ⧸ Ideal.span {(p : g)}) p] (hp2 : p = 2)
    (hJ1 : (MvFormalGroup.linearPart fun i => a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) = 1)
    (hlow : ∀ i j : Fin d, j ≤ i → (a i 1).coeff (Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞)})
    (ξ : Fin d → Localization.Away (p : g))
    (hξ : ∀ i, ξ i - α p a x i ∈ Deformation.PLoc.powSub p g 1) :
    ∃ y : Fin d → g, ∀ i, ξ i - α p a (fun j => x j + (p : g) * y j) i ∈ Deformation.PLoc.powSub p g 2 := by
  classical
  subst hp2
  have hNs1 := one_le_Ns 2 K Ns hNs
  set mkg := Ideal.Quotient.mk (Ideal.span {((2 : ℕ) : g)}) with hmkg
  set Λ := Lmat 2 a x Ns with hΛ
  set Q := Qmat 2 a x Ns with hQ
  obtain ⟨U, hUl, hUr, hD⟩ := twisted_data 2 a ha hJ x hx K hK rfl hJ1 hlow Ns hNs1
  choose c hc using fun i => (Deformation.PLoc.mem_powSub_iff 2).1 (hξ i)

  have hnil : IsNilpotent (nn 2 x) := ⟨K, (nn_pow_eq_bot 2 x K hK).trans Submodule.zero_eq_bot.symm⟩
  obtain ⟨yb, hyb, -⟩ := Matrix.existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent 2 (nn 2 x) hnil
    (U * Q.map mkg) hD (U.mulVec (mkg ∘ c))
  obtain ⟨y, hy⟩ := exists_lift 2 yb
  have hy2 : (⇑mkg ∘ fun j => y j ^ 2) = fun j => yb j ^ 2 := by
    funext j
    have h := congrFun hy j
    simp only [Function.comp_apply] at h ⊢
    rw [map_pow, h]

  have hsol : (Λ.map mkg).mulVec yb + (Q.map mkg).mulVec (fun j => yb j ^ 2) = mkg ∘ c := by
    have h := congrArg ((Λ.map mkg).mulVec) hyb
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mul_assoc, hUr, one_mul, Matrix.one_mulVec]
      at h
    exact h
  have hLQ : ∀ i, c i - (Λ.mulVec y i + Q.mulVec (fun j => y j ^ 2) i) ∈ Ideal.span {((2 : ℕ) : g)} := by
    intro i
    rw [← Ideal.Quotient.eq, ← hmkg, map_add, RingHom.map_mulVec, RingHom.map_mulVec, hy, hy2]
    have h := congrFun hsol i
    rw [Pi.add_apply, Function.comp_apply] at h
    exact h.symm
  refine ⟨y, fun i => ?_⟩
  have e1 := step_mem_two 2 a ha x hx K hK Ns hNs rfl y i
  have e2 : ξ i - α 2 a x i - algebraMap g (Localization.Away ((2 : ℕ) : g))
      (((2 : ℕ) : g) * (Λ.mulVec y i + Q.mulVec (fun j => y j ^ 2) i)) ∈ Deformation.PLoc.powSub 2 g 2 := by
    rw [← hc i, pow_one, ← map_sub, ← mul_sub]
    have h := algebraMap_pow_mul_mem_powSub 2 (g := g) 1 _ (hLQ i)
    rwa [pow_one] at h
  have key := sub_mem e2 e1
  have : ξ i - α 2 a x i - algebraMap g (Localization.Away ((2 : ℕ) : g))
        (((2 : ℕ) : g) * (Λ.mulVec y i + Q.mulVec (fun j => y j ^ 2) i)) -
      (α 2 a (fun j => x j + ((2 : ℕ) : g) * y j) i - α 2 a x i -
        algebraMap g (Localization.Away ((2 : ℕ) : g)) (((2 : ℕ) : g) *
          ((Lmat 2 a x Ns).mulVec y i + (Qmat 2 a x Ns).mulVec (fun j => y j ^ 2) i))) =
      ξ i - α 2 a (fun j => x j + ((2 : ℕ) : g) * y j) i := by rw [hΛ, hQ]; ring
  rw [this] at key
  exact key

end Newton

end Deformation.FontaineLift.HeartC12

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (d : ℕ)
    (a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞)
    (ha : ∀ i n, MvPowerSeries.constantCoeff (a i n) = 0)
    (hJ : IsUnit ((MvFormalGroup.linearPart fun i => a i 0).map
      (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))))
    (h2 : p ≠ 2 ∨
      ((MvFormalGroup.linearPart fun i => a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) = 1 ∧
        ∀ i j : Fin d, j ≤ i →
          MvFormalGroup.linearPart (fun i => a i 1) i j ∈ Ideal.span {(p : 𝓞)}))
    (g : Type v) [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
    [IsAdicComplete (Ideal.span {(p : g)}) g]
    (x₀ : Fin d → g) (hx₀ : ∀ j, x₀ j ∈ (Ideal.span {(p : g)}).radical)
    (ξ : Fin d → Localization.Away (p : g))
    (hξ : ∀ i, ξ i - Deformation.PLoc.wSeries p
      (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x₀ (a i n)) ∈ Deformation.PLoc.pSub p g) :
    ∃! x : Fin d → g, (∀ j, x j - x₀ j ∈ Ideal.span {(p : g)}) ∧
      ∀ i, Deformation.PLoc.wSeries p
        (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a i n)) = ξ i := by
  classical
  have hpp : p.Prime := Fact.out

  rcases subsingleton_or_nontrivial g with hg | hg
  · haveI : Subsingleton (Localization.Away (p : g)) := subsingleton_of_zero_eq_one
      (by rw [← map_zero (algebraMap g (Localization.Away (p : g))), Subsingleton.elim (0 : g) 1, map_one])
    refine ⟨fun _ => 0, ⟨fun j => by rw [Subsingleton.elim (0 - x₀ j) 0]; exact Ideal.zero_mem _,
      fun i => Subsingleton.elim _ _⟩, fun x' _ => funext fun j => Subsingleton.elim _ _⟩

  haveI hH : IsHausdorff (Ideal.span {(p : g)}) g := IsAdicComplete.toIsHausdorff
  have hpnu : (p : g) ∈ nonunits g := by
    intro hu
    have htop : Ideal.span {(p : g)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
    have h1 : (1 : g) = 0 := IsHausdorff.haus hH 1 fun n => by
      rw [htop, Ideal.top_pow, smul_eq_mul, Ideal.top_mul]
      exact SModEq.top
    exact one_ne_zero h1
  haveI : CharP (g ⧸ Ideal.span {(p : g)}) p := CharP.quotient g p hpnu

  set J : Ideal g := Ideal.span {(p : g)} with hJg
  have hrad_add : ∀ (x : Fin d → g), (∀ j, x j ∈ J.radical) → ∀ (t : g) (y : Fin d → g), t ∈ J →
      ∀ j, x j + t * y j ∈ J.radical := fun x hx t y ht j =>
    Ideal.add_mem _ (hx j) (Ideal.le_radical (Ideal.mul_mem_right _ _ ht))

  have step : ∀ (r : ℕ) (x : Fin d → g), (∀ j, x j ∈ J.radical) →
      (∀ i, ξ i - Deformation.FontaineLift.HeartC12.α p a x i ∈ Deformation.PLoc.powSub p g (r + 1)) →
      ∃ x' : Fin d → g, (∀ j, x' j - x j ∈ Ideal.span {(p : g) ^ (r + 1)}) ∧ (∀ j, x' j ∈ J.radical) ∧
        ∀ i, ξ i - Deformation.FontaineLift.HeartC12.α p a x' i ∈ Deformation.PLoc.powSub p g (r + 2) := by
    intro r x hx hξx
    obtain ⟨K, -, hK⟩ := Deformation.FontaineLift.HeartC12.exists_pow_span_range_le p x hx
    have hNs : K + 2 ≤ p ^ (K + 2) := (Nat.lt_pow_self hpp.one_lt).le
    by_cases hc : p ≠ 2 ∨ 2 ≤ r + 1
    · obtain ⟨y, hy⟩ := Deformation.FontaineLift.HeartC12.newton_step p a ha hJ x hx K hK (K + 2) hNs ξ r hc hξx
      refine ⟨fun j => x j + (p : g) ^ (r + 1) * y j, fun j => ?_,
        hrad_add x hx _ y (Ideal.pow_mem_of_mem J (Ideal.mem_span_singleton_self _) _ (Nat.succ_pos r)), hy⟩
      rw [add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rw [not_or, not_ne_iff, not_le] at hc
      obtain ⟨hp2, hr⟩ := hc
      have hr0 : r = 0 := by omega
      subst hr0
      have h2' := h2.resolve_left (not_not.2 hp2)
      obtain ⟨y, hy⟩ := Deformation.FontaineLift.HeartC12.newton_step_two p a ha hJ x hx K hK (K + 2) hNs hp2
        h2'.1 h2'.2 ξ hξx
      refine ⟨fun j => x j + (p : g) * y j, fun j => ?_, hrad_add x hx _ y (Ideal.mem_span_singleton_self _), hy⟩
      rw [add_sub_cancel_left, zero_add, pow_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

  let T : ℕ → Type v := fun r => {x : Fin d → g // (∀ j, x j ∈ J.radical) ∧ (∀ j, x j - x₀ j ∈ J) ∧
    ∀ i, ξ i - Deformation.FontaineLift.HeartC12.α p a x i ∈ Deformation.PLoc.powSub p g (r + 1)}
  have hξ0 : ∀ i, ξ i - Deformation.FontaineLift.HeartC12.α p a x₀ i ∈ Deformation.PLoc.powSub p g (0 + 1) :=
    fun i => hξ i
  let base : T 0 := ⟨x₀, hx₀, fun j => by rw [sub_self]; exact Ideal.zero_mem _, hξ0⟩
  let next : (r : ℕ) → T r → T (r + 1) := fun r xr =>
    ⟨Classical.choose (step r xr.1 xr.2.1 xr.2.2.2),
      (Classical.choose_spec (step r xr.1 xr.2.1 xr.2.2.2)).2.1,
      fun j => by
        have h1 := (Classical.choose_spec (step r xr.1 xr.2.1 xr.2.2.2)).1 j
        have h2 := xr.2.2.1 j
        have h3 := Ideal.add_mem _ ((Ideal.span_singleton_le_span_singleton.2
          (dvd_pow_self (p : g) (Nat.succ_ne_zero r))) h1) h2
        rwa [sub_add_sub_cancel] at h3,
      (Classical.choose_spec (step r xr.1 xr.2.1 xr.2.2.2)).2.2⟩
  let seq : (r : ℕ) → T r := fun r => Nat.rec (motive := T) base next r
  have hseq_succ : ∀ r, seq (r + 1) = next r (seq r) := fun _ => rfl
  set xs : ℕ → Fin d → g := fun r => (seq r).1 with hxs
  have hlink : ∀ r j, xs (r + 1) j - xs r j ∈ Ideal.span {(p : g) ^ (r + 1)} := by
    intro r j
    show (seq (r + 1)).1 j - (seq r).1 j ∈ _
    rw [hseq_succ]
    exact (Classical.choose_spec (step r (seq r).1 (seq r).2.1 (seq r).2.2.2)).1 j
  have hxs_rad : ∀ r j, xs r j ∈ J.radical := fun r => (seq r).2.1
  have hxs_ξ : ∀ r i, ξ i - Deformation.FontaineLift.HeartC12.α p a (xs r) i ∈
      Deformation.PLoc.powSub p g (r + 1) := fun r => (seq r).2.2.2
  have hxs0 : xs 0 = x₀ := rfl

  have hcauchy : ∀ (j : Fin d) {m n : ℕ}, m ≤ n → xs m j ≡ xs n j [SMOD J ^ m • (⊤ : Submodule g g)] := by
    intro j m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hJg, Ideal.span_singleton_pow]
    induction n, hmn using Nat.le_induction with
    | base => rw [sub_self]; exact Ideal.zero_mem _
    | succ n hmn ih =>
      have h := (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (p : g) (Nat.le_succ_of_le hmn)))
        (hlink n j)
      have := Ideal.sub_mem _ ih h
      rwa [sub_sub_sub_cancel_right] at this

  have hlim : ∀ j, ∃ L : g, ∀ n, xs n j ≡ L [SMOD J ^ n • (⊤ : Submodule g g)] := fun j =>
    IsPrecomplete.prec IsAdicComplete.toIsPrecomplete (hcauchy j)
  choose X hX using hlim
  have hX' : ∀ n j, xs n j - X j ∈ Ideal.span {(p : g) ^ n} := by
    intro n j
    have h := hX j n
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hJg, Ideal.span_singleton_pow] at h
  have hX0 : ∀ j, X j - x₀ j ∈ J := by
    intro j
    have h1 := hX' 1 j
    rw [pow_one] at h1
    have h2 : xs 1 j - x₀ j ∈ J := (seq 1).2.2.1 j
    have := Ideal.sub_mem _ h2 h1
    rwa [sub_sub_sub_cancel_left] at this
  have hXrad : ∀ j, X j ∈ J.radical := by
    intro j
    have : X j = x₀ j + (X j - x₀ j) * 1 := by ring
    rw [this]
    exact hrad_add x₀ hx₀ _ (fun _ => 1) (hX0 j) j

  have hαX : ∀ i, Deformation.FontaineLift.HeartC12.α p a X i = ξ i := by
    intro i
    rw [← sub_eq_zero]
    refine Deformation.PLoc.eq_zero_of_forall_mem_powSub p hpg fun s => ?_
    have h1 := Deformation.FontaineLift.wSeries_adicEval_sub_wSeries_adicEval_mem_powSub p (a i) (ha i) g hpg
      X (xs (s + 1)) hXrad (hxs_rad (s + 1)) (s + 1) (Nat.succ_pos s)
      (fun j => by rw [← neg_sub]; exact Ideal.neg_mem_iff _ |>.2 (hX' (s + 1) j))
    have h2 := hxs_ξ (s + 1) i
    have h3 := Deformation.PLoc.powSub_le_powSub_of_le p (Nat.le_succ s) (sub_mem h1
      (Deformation.PLoc.powSub_le_powSub_of_le p (Nat.le_succ (s + 1)) h2))
    have : Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) X (a i n)) -
        Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (xs (s + 1)) (a i n)) -
        (ξ i - Deformation.FontaineLift.HeartC12.α p a (xs (s + 1)) i) =
      Deformation.FontaineLift.HeartC12.α p a X i - ξ i := by
      simp only [Deformation.FontaineLift.HeartC12.α, Deformation.FontaineLift.HeartC12.uu]; ring
    rw [this] at h3
    exact h3
  refine ⟨X, ⟨hX0, hαX⟩, ?_⟩

  rintro X' ⟨hX'0, hαX'⟩
  have hX'rad : ∀ j, X' j ∈ J.radical := by
    intro j
    have : X' j = x₀ j + (X' j - x₀ j) * 1 := by ring
    rw [this]
    exact hrad_add x₀ hx₀ _ (fun _ => 1) (hX'0 j) j

  have hclose : ∀ r : ℕ, 1 ≤ r → ∀ j, X' j - X j ∈ Ideal.span {(p : g) ^ r} := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base =>
      intro j
      rw [pow_one]
      have := Ideal.sub_mem _ (hX'0 j) (hX0 j)
      rwa [sub_sub_sub_cancel_right] at this
    | succ r hr ih =>

      choose y hy using fun j => Ideal.mem_span_singleton'.1 (ih j)
      have hXy : X' = fun j => X j + (p : g) ^ r * y j := by
        funext j; rw [mul_comm, hy, add_sub_cancel]
      obtain ⟨K, -, hK⟩ := Deformation.FontaineLift.HeartC12.exists_pow_span_range_le p X hXrad
      have hNs : K + 2 ≤ p ^ (K + 2) := (Nat.lt_pow_self hpp.one_lt).le
      have hNs1 : 1 ≤ K + 2 := by omega
      set mkg := Ideal.Quotient.mk (Ideal.span {(p : g)}) with hmkg
      have hu := Deformation.FontaineLift.HeartC12.isUnit_Lmat_map p a ha X hXrad K hK hJ (K + 2) hNs1
      have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hu

      have hdiff : ∀ i, Deformation.FontaineLift.HeartC12.α p a X' i - Deformation.FontaineLift.HeartC12.α p a X i = 0 := by
        intro i
        have h1 := hαX' i
        rw [hJg] at h1
        have h2 := hαX i
        simp only [Deformation.FontaineLift.HeartC12.α, Deformation.FontaineLift.HeartC12.uu] at h2 ⊢
        rw [h1, h2, sub_self]

      have hcancel : ∀ (z : g), algebraMap g (Localization.Away (p : g)) ((p : g) ^ r * z) ∈
          Deformation.PLoc.powSub p g (r + 1) → z ∈ Ideal.span {(p : g)} := by
        intro z hz
        have h := Deformation.PLoc.mem_span_pow_of_invPow_mul_algebraMap_mem_powSub p hpg (m := 0) (s := r + 1)
          (a := (p : g) ^ r * z) (by rwa [Deformation.PLoc.invPow_zero, one_mul])
        rw [zero_add] at h
        obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h
        have hreg : IsRegular ((p : g) ^ r) := (isRegular_iff_mem_nonZeroDivisors.2 hpg).pow r
        refine Ideal.mem_span_singleton'.2 ⟨t, hreg.left ?_⟩
        show (p : g) ^ r * (t * (p : g)) = (p : g) ^ r * z
        rw [← ht, pow_succ]; ring

      have hy0 : ∀ j, y j ∈ Ideal.span {(p : g)} := by
        by_cases hc : p ≠ 2 ∨ 2 ≤ r
        ·
          have hΛy : ∀ i, (Deformation.FontaineLift.HeartC12.Lmat p a X (K + 2)).mulVec y i ∈ Ideal.span {(p : g)} := by
            intro i
            refine hcancel _ ?_
            have e := Deformation.FontaineLift.HeartC12.step_mem p a ha X hXrad K hK (K + 2) hNs r hr hc y i
            rw [← hXy, hdiff i, zero_sub] at e
            exact (Submodule.neg_mem_iff _).1 e

          have hyb : (⇑mkg ∘ y) = 0 := by
            have h1 : ((Deformation.FontaineLift.HeartC12.Lmat p a X (K + 2)).map mkg).mulVec (⇑mkg ∘ y) = 0 := by
              funext i
              rw [← RingHom.map_mulVec, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
              exact hΛy i
            have h2 := congrArg (((Deformation.FontaineLift.HeartC12.Lmat p a X (K + 2)).map mkg)⁻¹.mulVec) h1
            rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
          intro j
          have := congrFun hyb j
          rw [Function.comp_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
          exact this
        ·
          rw [not_or, not_ne_iff, not_le] at hc
          obtain ⟨hp2, hr2⟩ := hc
          have hr1 : r = 1 := by omega
          subst hr1
          have h2' := h2.resolve_left (not_not.2 hp2)
          obtain ⟨U, hUl, hUr, hD⟩ := Deformation.FontaineLift.HeartC12.twisted_data p a ha hJ X hXrad K hK hp2
            h2'.1 h2'.2 (K + 2) hNs1
          set Λ := Deformation.FontaineLift.HeartC12.Lmat p a X (K + 2) with hΛ
          set Q := Deformation.FontaineLift.HeartC12.Qmat p a X (K + 2) with hQ
          have hΛQ : ∀ i, Λ.mulVec y i + Q.mulVec (fun j => y j ^ 2) i ∈ Ideal.span {(p : g)} := by
            intro i
            refine hcancel _ ?_
            have e := Deformation.FontaineLift.HeartC12.step_mem_two p a ha X hXrad K hK (K + 2) hNs hp2 y i
            rw [pow_one] at hXy
            rw [← hXy, hdiff i, zero_sub] at e
            have e' : -(algebraMap g (Localization.Away (p : g)))
                ((p : g) ^ 1 * (Λ.mulVec y i + Q.mulVec (fun j => y j ^ 2) i)) ∈ Deformation.PLoc.powSub p g (1 + 1) := by
              rw [pow_one]; exact e
            exact (Submodule.neg_mem_iff _).1 e'

          have hnil : IsNilpotent (Deformation.FontaineLift.HeartC12.nn p X) :=
            ⟨K, (Deformation.FontaineLift.HeartC12.nn_pow_eq_bot p X K hK).trans Submodule.zero_eq_bot.symm⟩
          obtain ⟨z, -, hzu⟩ := Matrix.existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent p
            (Deformation.FontaineLift.HeartC12.nn p X) hnil (U * Q.map mkg) hD 0
          have hzero : (0 : Fin d → g ⧸ Ideal.span {(p : g)}) +
              (U * Q.map mkg).mulVec (fun j => (0 : Fin d → g ⧸ Ideal.span {(p : g)}) j ^ p) = 0 := by
            rw [zero_add]
            have : (fun j => (0 : Fin d → g ⧸ Ideal.span {(p : g)}) j ^ p) = 0 := by
              funext j; rw [Pi.zero_apply, zero_pow hpp.ne_zero]
            rw [this, Matrix.mulVec_zero]
          have hyb : (⇑mkg ∘ y) + (U * Q.map mkg).mulVec (fun j => (⇑mkg ∘ y) j ^ p) = 0 := by
            have h1 : (Λ.map mkg).mulVec (⇑mkg ∘ y) + (Q.map mkg).mulVec (fun j => (⇑mkg ∘ y) j ^ p) = 0 := by
              funext i
              have hsq : (fun j => (⇑mkg ∘ y) j ^ p) = ⇑mkg ∘ fun j => y j ^ 2 := by
                funext j; simp only [Function.comp_apply, map_pow, hp2]
              rw [hsq, Pi.add_apply, ← RingHom.map_mulVec, ← RingHom.map_mulVec, ← map_add, Pi.zero_apply,
                Ideal.Quotient.eq_zero_iff_mem]
              exact hΛQ i
            have h2 := congrArg U.mulVec h1
            rwa [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hUl, Matrix.one_mulVec,
              Matrix.mulVec_zero] at h2
          have hy' : (⇑mkg ∘ y) = 0 := (hzu _ hyb).trans (hzu _ hzero).symm
          intro j
          have := congrFun hy' j
          rw [Function.comp_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
          exact this

      intro j
      rw [← hy j, mul_comm]
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hy0 j)
      exact Ideal.mem_span_singleton'.2 ⟨t, by rw [← ht, pow_succ]; ring⟩

  funext j
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hH (X' j - X j) fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, hJg, Ideal.span_singleton_pow]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top
  · exact hclose n hn j

end S_Deformation_FontaineLift_existsUnique_sub_mem_and_wSeries_adicEval_eq_of_isUnit_linearPart
end P2MW
export P2MW.S_Deformation_FontaineLift_existsUnique_sub_mem_and_wSeries_adicEval_eq_of_isUnit_linearPart (solution)
