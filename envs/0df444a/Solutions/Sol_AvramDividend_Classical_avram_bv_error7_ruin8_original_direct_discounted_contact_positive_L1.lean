-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_original_direct_discounted_contact_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:14:02.854319+00:00
-- url     : https://prove2.me/submissions/d7c875d6-dffb-4ee6-a3b2-86ace92a161d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_uniform_continuity_on_nonnegative_compact_contact_band
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_uniform_contact_value_differences_vanish
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_constant_domination
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_discounted_final_contact_constant_DCT

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- BV stopped-grid discounted final contact has vanishing expected positive
error on compact nonnegative reserves, without a zero-derivative bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hMesh : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       ∀ δ : ℝ, 0 < δ → ∀ᶠ m in Filter.atTop,
         ∀ i, i < k m ω →
           |Y (u m (i + 1)) - Y (u m i)| < δ))
    (B : ℝ) (hB : 0 ≤ B) (z c : ℕ → Ω → ℝ)
    (hzSource : ∀ m ω, z m ω =
      if k m ω = 0 then 0 else
        x + X.X (u m (k m ω - 1)) ω -
          rightLimit D (u m (k m ω - 1)) ω)
    (hcSource : ∀ m ω, c m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       if k m ω = 0 then 0 else
         Y (u m (k m ω)) - Y (u m (k m ω - 1))))
    (hBand : ∀ m ω, z m ω ∈ Set.Icc 0 B ∧ z m ω + c m ω ∈ Set.Icc 0 B)
    (Err Disc : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω))
    (hDiscSource : ∀ m ω, Disc m ω =
      Real.exp (-(q * (u m (k m ω - 1) : ℝ))) * Err m ω)
    (hDiscMeas : ∀ m, AEStronglyMeasurable (Disc m) P) :
    (∀ m, Integrable (fun ω => max (Disc m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Disc m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hUC := avram_bv_error7_ruin8_vcstar_uniform_continuity_on_nonnegative_compact_contact_band
      X hX q hq W hW hc hBV B
  have hInc := avram_bv_error7_original_final_contact_compensated_increment_ae_zero X u k hMesh
  have hRawAE : ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)) := by
    filter_upwards [hInc] with ω hω
    have hcTo : Tendsto (fun m => c m ω) atTop (nhds (0 : ℝ)) := by
      convert hω using 1
      funext m
      exact hcSource m ω
    have hraw := avram_bv_error7_ruin8_uniform_contact_value_differences_vanish
      (vcstar W) (Set.Icc 0 B) hUC
      (fun m => z m ω) (fun m => c m ω)
      (fun m => (hBand m ω).1) (fun m => (hBand m ω).2) hcTo
    convert hraw using 1
    funext m
    exact hErrSource m ω
  obtain ⟨M, hM, hDom⟩ :=
    avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_constant_domination
      X hX hBV q hq W hW hc B z c hBand Err hErrSource
  exact avram_bv_error7_ruin8_original_discounted_final_contact_constant_DCT
    X hX q (le_of_lt hq) u k (2 * M) (by positivity)
    Err Disc hRawAE (fun m => Filter.Eventually.of_forall (hDom m))
    hDiscSource hDiscMeas
