-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_original_stopped_ruin_clipped_positive_contact_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:33:48.347596+00:00
-- url     : https://prove2.me/submissions/ce40ae48-25d4-4a54-96c8-553ea1cbe595

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_stopped_ruin_clipped_positive_raw_contact_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_ruin_clipped_raw_contact_constant_domination
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_probability_constant_dom_positive_DCT

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- Full original stopped BV ruin-clipped final-cell positive error L1
absorption from independent a.e. geometry and probability domination. -/
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
    (B : ℝ) (z c : ℕ → Ω → ℝ)
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
    (hClipBand : ∀ m ω, z m ω ∈ Set.Icc 0 B ∧
      max (z m ω + c m ω) 0 ∈ Set.Icc 0 B)
    (Err : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω))
    (hPosMeas : ∀ m, AEStronglyMeasurable (fun ω => max (Err m ω) 0) P) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hAE := avram_bv_error7_ruin8_original_stopped_ruin_clipped_positive_raw_contact_ae_zero
    X hX hBV q hq W hW hc x C D hD u k hMesh B z c hzSource hcSource
    hClipBand Err hErrSource
  obtain ⟨M, hM, hDom⟩ :=
    avram_bv_error7_ruin8_original_ruin_clipped_raw_contact_constant_domination
      X hX hBV q hq W hW hc B z c hClipBand Err hErrSource
  have hPosDom : ∀ m, ∀ᵐ ω ∂P, ‖max (Err m ω) 0‖ ≤ 2 * M := by
    intro m
    filter_upwards [] with ω
    have hmax : 0 ≤ max (Err m ω) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hmax]
    calc
      max (Err m ω) 0 ≤ |Err m ω| :=
        max_le (le_abs_self _) (abs_nonneg _)
      _ = ‖Err m ω‖ := (Real.norm_eq_abs _).symm
      _ ≤ 2 * M := hDom m ω
  have hL1 := avram_bv_error7_ruin8_original_probability_constant_dom_positive_DCT
    X hX (2 * M) (by positivity)
    (fun m ω => max (Err m ω) 0) hPosMeas hAE hPosDom
  simpa [max_assoc] using hL1
