-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward81_original_trueclock_HJB_B_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:10:27.142835+00:00
-- url     : https://prove2.me/submissions/3ac30a5f-ae8d-4884-96e9-64dfbf3c0a79

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u δ v : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (huv : u + δ < v) (hvCap : v < C.toReal)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (Y : ℝ≥0 × Ω → ℝ) (ρ : Ω → ℝ≥0) :
    ∀ ω : Ω,
      (∫ t : ℝ≥0,
        (if t ≤ ρ ω then
          Real.exp (-(q * (t : ℝ))) *
            ((if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) *
             (if Y (t, ω) ∈ Icc (u + δ) v then
                X.generator w (Y (t, ω)) - q * w (Y (t, ω))
              else 0))
         else 0)
         ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) ≤ 0 := by
  intro ω
  apply integral_nonpos_of_ae
  filter_upwards [] with t
  by_cases ht : t ≤ ρ ω
  · simp only [if_pos ht]
    have hKernel :
        (if Y (t, ω) ∈ Icc (u + δ) v then
           X.generator w (Y (t, ω)) - q * w (Y (t, ω))
         else 0) ≤ 0 := by
      split_ifs with hBand
      · obtain ⟨hLo, hHi⟩ := mem_Icc.mp hBand
        have hPos : 0 < Y (t, ω) := by linarith
        have hCap : ENNReal.ofReal (Y (t, ω)) < C :=
          (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hPos) hCfinite).2 (by linarith)
        exact (hw_gen _ hPos hCap).2
      · exact le_refl _
    have hMask :
        0 ≤ (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _))
      (mul_nonpos_of_nonneg_of_nonpos hMask hKernel)
  · simp [ht]
