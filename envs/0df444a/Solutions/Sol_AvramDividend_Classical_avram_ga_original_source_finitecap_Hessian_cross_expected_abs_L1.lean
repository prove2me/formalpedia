-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_source_finitecap_Hessian_cross_expected_abs_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:36:52.575761+00:00
-- url     : https://prove2.me/submissions/607eb008-80fd-4ba0-b70a-eaeef274573e

import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_clipped_Hessian_K_from_source
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_physical_Hessian_cross_L1
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
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (j : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (Finset.range m).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (if x + X.X s ω - rightLimit D s ω ≤ b
             then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
             else 0) / 2 * (R ^ 2 - Z ^ 2)
        else 0)
    (∀ m, Integrable (fun ω => |B m ω|) P) →
    Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (nhds (0 : ℝ))  := by
  intro b B hBI
  obtain ⟨K, hK, hCoeff⟩ :=
    avram_ga_original_finitecap_clipped_Hessian_K_from_source
      X x D hD w C hC hFiniteCap hw q hq n j ρ δ hδ hFloor
  simpa only [b, B] using
    (avram_ga_original_finitecap_physical_Hessian_cross_L1
      X hNuZero n ρ hρstop x D w b q
      ⟨K, hK, hCoeff⟩ hBI)
