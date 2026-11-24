-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.slope_bound_saturation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:46.638376+00:00
-- url     : https://prove2.me/submissions/ca8b2c42-5517-46df-a7c5-b73b411e49fa

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_tri_integral
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_coeff_prod_rename
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_bidet_reindex
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_satEmb_inj
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_minorProd_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_map_bidet
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSIdxFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (d N0 : ℕ) [NeZero d]
    (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0), SBSat K colN p hp := by
  intro K _ _ d N0 _ colN p hp P hP hint
  classical
  have hb := fun s : ZMod d => sSBasis (unitBall K) N0 N0 (shapeDeg (p s))
  choose b hb1 hb2 using hb
  have : ∀ s : ZMod d, Fintype (ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ)) :=
    fun s => (sSIdxFinite N0 N0 (shapeDeg (p s))).fintype
  let φ : unitBall K →+* K := (unitBall K).subtype
  let B : (∀ s : ZMod d, ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ)) →
      MvPolynomial (ZMod d × Fin N0 × Fin N0) K :=
    fun M => ∏ s, rename (satEmb d N0 s) (map φ (b s (M s)))

  have hBx : ∀ M, B M ∈ xMinors (K := K) colN p hp := by
    intro M
    have h1 : ∀ s, ∃ A : ∀ c, Fin (p s c) → Fin N0, b s (M s) = bideterminant (unitBall K) (p s) (hp s) A := by
      intro s
      obtain ⟨-, -, k, sz, hsz, I, hsh, -, hbI⟩ := hb2 s (M s)
      obtain ⟨A, hA⟩ := sat_bidet_reindex (unitBall K) sz hsz (p s) (hp s) hsh I
      exact ⟨A, hbI.trans hA⟩
    choose A hA using h1
    refine ⟨A, Finset.prod_congr rfl fun s _ => ?_⟩
    rw [sat_minorProd_eq, hA s, sat_map_bidet]

  have hspan : ∀ Q ∈ xMinors (K := K) colN p hp, Q ∈ Submodule.span K (Set.range B) := by
    rintro Q ⟨A, rfl⟩
    have h1 : ∀ s, ∃ a : ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ) → unitBall K,
        ∑ m, a m • b s m = bideterminant (unitBall K) (p s) (hp s) (A s) := by
      intro s
      have h2 := bidetMem (unitBall K) N0 N0 (colN s) (p s) (hp s) (A s)
      rw [← (hb1 s).2.1] at h2
      exact (Submodule.mem_span_range_iff_exists_fun _).mp h2
    choose a ha using h1
    have h3 : ∀ s, minorProd (fun (i a : Fin N0) =>
        (X (s, i, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) K)) (p s) (hp s) (A s) =
        ∑ m, φ (a s m) • rename (satEmb d N0 s) (map φ (b s m)) := by
      intro s
      rw [sat_minorProd_eq, ← sat_map_bidet φ, ← ha s, map_sum, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_eq_C_mul, map_mul, map_C, map_mul, rename_C, ← smul_eq_C_mul]
    simp_rw [h3]
    rw [Finset.prod_univ_sum]
    refine Submodule.sum_mem _ fun M _ => ?_
    rw [Finset.prod_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨M, rfl⟩)
  have hP' : P ∈ Submodule.span K (Set.range B) := Submodule.span_le.mpr hspan hP
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hP'

  let f : (∀ s : ZMod d, ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ)) → (ZMod d → (colLex N0 N0).syn) :=
    fun M s => (colLex N0 N0).toSyn (M s).1
  have hf : Function.Injective f := by
    intro M M' h
    funext s
    exact Subtype.ext ((colLex N0 N0).toSyn.injective (congrFun h s))
  let _ : PartialOrder (∀ s : ZMod d, ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ)) := PartialOrder.lift f hf
  let E : (∀ s : ZMod d, ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ)) → (ZMod d × Fin N0 × Fin N0 →₀ ℕ) :=
    fun M => ∑ s, ((M s).1).mapDomain (satEmb d N0 s)
  have hT : ∀ M' M, coeff (E M') (B M) = ∏ s, φ (coeff (M' s).1 (b s (M s))) := by
    intro M' M
    simp only [E, B]
    rw [sat_coeff_prod_rename (satEmb d N0) (satEmb_inj d N0)]
    simp only [coeff_map]
  have hcint : ∀ M, ‖c M‖ ≤ 1 := by
    refine sat_tri_integral (fun M' M => coeff (E M') (B M)) ?_ ?_ ?_ c ?_
    · intro M' M
      rw [hT, norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun s _ => (coeff (M' s).1 (b s (M s))).2
    · intro M
      rw [hT]
      refine Finset.prod_eq_one fun s _ => ?_
      have h1 := (hb2 s (M s)).2.1
      rw [MonomialOrder.leadingCoeff, (hb2 s (M s)).1] at h1
      rw [h1, map_one]
    · intro M' M hle
      rw [hT]
      have h1 : ∃ s, ¬ f M' s ≤ f M s := by
        by_contra hcon
        push Not at hcon
        exact hle hcon
      obtain ⟨s, hs⟩ := h1
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      rw [MonomialOrder.coeff_eq_zero_of_lt, map_zero]
      rw [(hb2 s (M s)).1]
      exact not_le.mp hs
    · intro M'
      have h1 : ∑ M, c M * coeff (E M') (B M) = coeff (E M') P := by
        rw [← hc, coeff_sum]
        exact Finset.sum_congr rfl fun M _ => by rw [coeff_smul, smul_eq_mul]
      rw [h1]
      exact hint _
  rw [← hc]
  refine Submodule.sum_mem _ fun M _ => ?_
  exact Submodule.smul_mem _ (⟨c M, hcint M⟩ : unitBall K) (Submodule.subset_span (hBx M))
end Formalism.DworkPowerSeriesWeights
