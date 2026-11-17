-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_clipped_Hessian_K_from_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:02:01.191241+00:00
-- url     : https://prove2.me/submissions/6979af37-019e-4794-b735-02878dd933b8

import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_clip_second_deriv_continuousOn
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_true_stopped_finitecap_Hessian_uniform_of_band
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (n j : ℕ)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (ω : Ω) (i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      i < m → s < ρ ω → s + Δ ≤ ρ ω →
      |Real.exp (-(q * (s : ℝ))) *
        (if x + X.X s ω - rightLimit D s ω ≤ b
        then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
        else 0)| ≤ K  := by
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hCont : ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b) := by
    simpa only [a, b] using
      (avram_ga_original_finitecap_clip_second_deriv_continuousOn
        w C hC hFiniteCap hw δ hδ j)
  have hFloorA : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      a ≤ riskProcess X x D t ω := by
    intro ω t ht hρ
    have hf := hFloor ω t ht hρ
    dsimp [a]
    linarith
  simpa only [a, b] using
    (avram_ga_original_true_stopped_finitecap_Hessian_uniform_of_band
      X x D hD ρ a b q hq w hFloorA hCont n)
