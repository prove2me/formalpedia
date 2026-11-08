-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_original_ruin_crossing_raw_positive_contact_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:12:14.946209+00:00
-- url     : https://prove2.me/submissions/ba4295d9-32c0-461a-a4ec-d8379b250df0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_without_smoothness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A genuine stopped-grid contact cell crossing ruin has no positive raw
barrier-value error: the value is zero below ruin and nonnegative before it. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (z c : ℕ → Ω → ℝ)
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
    (Err : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω)) :
    ∀ m ω, 0 ≤ z m ω → z m ω + c m ω < 0 →
      max (Err m ω) 0 = 0 := by
  intro m ω hz hcross
  have hneg : vcstar W (z m ω + c m ω) = 0 :=
    vcstar_eq_zero_of_neg W _ hcross
  have hnonneg : 0 ≤ vcstar W (z m ω) :=
    avram_sweep17_vcstar_nonnegative_without_smoothness
      X hX q hq W hW hc (z m ω) hz
  have hErr : Err m ω ≤ 0 := by
    rw [hErrSource m ω, hneg]
    simpa using (neg_nonpos.mpr hnonneg)
  exact max_eq_right hErr
