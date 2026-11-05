-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_local_continuous_HJB_drift_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:31:04.510907+00:00
-- url     : https://prove2.me/submissions/0c0e5a6a-a82d-4c6e-bea2-14ce148651c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_predictable_continuous_HJB_drift_L1
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Classical
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A compact-band continuous HJB residual admits a globally measurable clamped extension. -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (hq : 0 ≤ q)
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hUpm : Measurable (fun p : ℝ≥0 × Ω => Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
(a b : ℝ) (hab : a ≤ b)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b)
(H : ℝ → ℝ) (hHcont : ContinuousOn H (Set.Icc a b)) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by
  let Upre : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1
  let J : ℝ → ℝ := fun y => H (max a (min y b))
  have hClamp : Continuous (fun y : ℝ => max a (min y b)) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hClamp_mem (y : ℝ) : max a (min y b) ∈ Set.Icc a b := by
    exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hJcont : Continuous J := by
    exact hHcont.comp_continuous hClamp hClamp_mem
  have hJint : Integrable
      (fun p : ℝ≥0 × Ω => if p ∈ E then
        Real.exp (-(q * (p.1 : ℝ))) * J (Upre p) else 0)
      ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) :=
    avram_p3_e_compensator_original_predictable_continuous_HJB_drift_L1
      X T x D q hq E hEm hUpm a b hab hEregion
      J hJcont.measurable hJcont.continuousOn
  have hEq : (fun p : ℝ≥0 × Ω =>
      if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * J (Upre p) else 0) =
      (fun p : ℝ≥0 × Ω =>
      if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Upre p) else 0) := by
    funext p
    by_cases hp : p ∈ E
    · have hpBand := hEregion p hp
      have hc : max a (min (Upre p) b) = Upre p := by
        rw [min_eq_left hpBand.2, max_eq_right hpBand.1]
      simp only [if_pos hp, J, hc]
    · simp only [if_neg hp]
  rw [hEq] at hJint
  exact hJint
