-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerF_ae_liminf_localised_budget_to_full_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:09:42.977904+00:00
-- url     : https://prove2.me/submissions/40ea4dc9-786c-4ba8-adcb-6ad430cc41c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → ℝ≥0∞) (F : Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hAm : ∀ j, Measurable (A j))
    (hBound : ∀ j, (∫⁻ ω, A j ω ∂P) ≤ B)
    (hlim : ∀ᵐ ω ∂P,
      F ω ≤ liminf (fun j => A j ω) atTop) :
    (∫⁻ ω, F ω ∂P) ≤ B := by
  have hBLim :
      liminf (fun j : ℕ => ∫⁻ ω, A j ω ∂P) atTop ≤ B :=
    liminf_le_of_frequently_le'
      (Filter.Eventually.frequently
        (Filter.Eventually.of_forall hBound))
  calc
    (∫⁻ ω, F ω ∂P) ≤
        (∫⁻ ω, liminf (fun j => A j ω) atTop ∂P) :=
      lintegral_mono_ae hlim
    _ ≤ liminf (fun j : ℕ => ∫⁻ ω, A j ω ∂P) atTop :=
      lintegral_liminf_le' (fun j => (hAm j).aemeasurable)
    _ ≤ B := hBLim
