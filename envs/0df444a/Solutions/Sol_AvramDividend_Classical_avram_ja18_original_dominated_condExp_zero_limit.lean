-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_dominated_condExp_zero_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:47:26.697201+00:00
-- url     : https://prove2.me/submissions/4f877f3b-6f62-4f6a-b596-490b2da7fade

import Mathlib.Probability.Process.Filtration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- An integrable original-path envelope transports finite-grid
conditional centring through an almost-sure stopping limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (J : ℕ → Ω → ℝ) (Z B : Ω → ℝ)
    (hInt : ∀ k, Integrable (J k) P)
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (Z ω)))
    (hBInt : Integrable B P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ B ω)
    (hZero : ∀ k, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (J k) ω = 0) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P Z ω = 0 := by
  have hzInt : Integrable (fun _ : Ω => (0 : ℝ)) P := by simp
  have hzConv : ∀ᵐ ω ∂P,
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with ω
    exact tendsto_const_nhds
  have hzDom : ∀ k : ℕ, ∀ᵐ ω ∂P,
      ‖(0 : ℝ)‖ ≤ (0 : ℝ) := by
    intro k
    filter_upwards [] with ω
    norm_num
  have hZeroCE : ∀ k,
      (P[J k | 𝓕.rightCont 0]) =ᵐ[P]
        (P[(fun _ : Ω => (0 : ℝ)) | 𝓕.rightCont 0]) := by
    intro k
    filter_upwards [hZero k] with ω hω
    simpa using hω
  have h := tendsto_condExp_unique
    (fs := J) (gs := fun _ _ => (0 : ℝ))
    (f := Z) (g := fun _ => (0 : ℝ))
    hInt (fun _ => hzInt) hConv hzConv
    B hBInt (fun _ => (0 : ℝ)) hzInt hDom hzDom hZeroCE
  filter_upwards [h] with ω hω
  simpa using hω
