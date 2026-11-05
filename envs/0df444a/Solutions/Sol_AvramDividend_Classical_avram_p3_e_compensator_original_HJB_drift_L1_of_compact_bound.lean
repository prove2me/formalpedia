-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:42:49.202477+00:00
-- url     : https://prove2.me/submissions/aa93ed73-8860-488d-81f8-fb72157ab28a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_horizon_drift_L1_of_uniform_bound
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Classical
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
(q : ℝ) (hq : 0 ≤ q) (E : Set (ℝ≥0 × Ω))
(a b K : ℝ) (hK : 0 ≤ K) (H : ℝ → ℝ)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b)
(hHbound : ∀ y ∈ Set.Icc a b, |H y| ≤ K)
(hFm : AEStronglyMeasurable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by
  apply avram_p3_e_compensator_original_horizon_drift_L1_of_uniform_bound X T _ hFm K
  intro p
  by_cases hp : p ∈ E
  · simp only [if_pos hp]
    have hloc : |H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)| ≤ K :=
      hHbound _ (hEregion p hp)
    have ht : 0 ≤ (p.1 : ℝ) := p.1.property
    have hqt : 0 ≤ q * (p.1 : ℝ) := mul_nonneg hq ht
    have hepos : 0 ≤ Real.exp (-(q * (p.1 : ℝ))) :=
      le_of_lt (Real.exp_pos _)
    have hele : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr hqt)
    calc
      |Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)| =
          Real.exp (-(q * (p.1 : ℝ))) * |H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)| := by
            rw [abs_mul, abs_of_nonneg hepos]
      _ ≤ Real.exp (-(q * (p.1 : ℝ))) * K :=
        mul_le_mul_of_nonneg_left hloc hepos
      _ ≤ 1 * K := mul_le_mul_of_nonneg_right hele hK
      _ = K := one_mul K
  · simpa [hp] using hK
