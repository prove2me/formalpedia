-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_killed_scale_window_pointwise_kernel_identity_no_standing
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T15:49:25.96259+00:00
-- url     : https://prove2.me/submissions/8a4631ea-1b04-4a26-84b2-5ec4b13d3f9a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
attribute [local instance] Classical.propDecidable

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (_hW : IsScaleFunction X q W)
    (x : ℝ) (s : ℝ≥0) (T : ℝ≥0)
    (u : ℝ≥0) (_hsu : s ≤ u)
    (hTu : s + T = u) (hTcu : (T : ℝ) = (u : ℝ) - (s : ℝ))
    (hEvent : ∀ ω : Ω, (∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)) ↔ ω ∈
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)})
    (A : Set Ω) :
    ∀ ω : Ω,
      (if ∀ v : ℝ≥0, v ≤ T →
        0 ≤ (if ω ∈ A then x + X.X s ω else -1) +
          (X.X (s + v) ω - X.X s ω)
        then ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
          W ((if ω ∈ A then x + X.X s ω else -1) +
            (X.X (s + T) ω - X.X s ω))) else (0 : ℝ≥0∞)) =
      ENNReal.ofReal (A.indicator (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) ω) := by
  intro ω
  by_cases hA : ω ∈ A
  · simp only [if_pos hA, Set.indicator_of_mem hA]
    have hTerminal : (x + X.X s ω) + (X.X u ω - X.X s ω) = x + X.X u ω := by ring
    by_cases hCross : ∀ v : ℝ≥0, v ≤ T →
        0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)
    · simp only [if_pos hCross, Set.indicator_of_mem ((hEvent ω).mp hCross),
        hTu, hTerminal, hTcu]
    · have hHistory := mt (hEvent ω).mpr hCross
      simp only [if_neg hCross, Set.indicator_of_notMem hHistory, ENNReal.ofReal_zero]
  · simp only [if_neg hA, Set.indicator_of_notMem hA, ENNReal.ofReal_zero]
    apply if_neg
    intro hCross
    have hZero := hCross 0 zero_le
    norm_num at hZero
