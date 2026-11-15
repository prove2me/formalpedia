-- Prove2me | solution 1 for AvramDividend.Classical.avram_b25_geometric_integrable_signed_error_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:11:30.706968+00:00
-- url     : https://prove2.me/submissions/271a4120-a722-4a0e-85bf-8427a6584172

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_b24_generic_geometric_L1_gain_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Ω → ℝ)
    (hEI : ∀ k, Integrable (E k) P)
    (hEgeom : ∀ k, (∫ ω, ‖E k ω‖ ∂P)
      ≤ ((1 : ℝ) / 2) ^ k) :
    ∀ᵐ ω ∂P, Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)) := by
  let Z : ℕ → Ω → ℝ := fun _ _ => 0
  have hZI (k : ℕ) : Integrable (Z k) P := by
    simpa [Z] using (integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) P)
  have hZstepI (k : ℕ) :
      Integrable (fun ω => Z (k + 1) ω - Z k ω) P := by
    simpa [Z] using (integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) P)
  have hZgeom (k : ℕ) :
      (∫ ω, ‖Z (k + 1) ω - Z k ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k := by
    simp [Z]
  obtain ⟨MG,MJ,BG,BJ,hGconv,hJconv,hEconv,hBGI,hBJI,hGB,hJB⟩ :=
    AvramDividend.Classical.avram_b24_generic_geometric_L1_gain_domination
      (P := P) Z Z E (hZI 0) (hZI 0)
      hZstepI hZstepI hEI hZgeom hZgeom hEgeom
  exact hEconv
