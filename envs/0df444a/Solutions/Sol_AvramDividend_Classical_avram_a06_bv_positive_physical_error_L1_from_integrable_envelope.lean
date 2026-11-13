-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_bv_positive_physical_error_L1_from_integrable_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:33:13.13911+00:00
-- url     : https://prove2.me/submissions/3474655d-ddac-4b1c-b068-1e28e5ab7c59

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Err : ℕ → Ω → ℝ)
    (hErrMeas : ∀ n, AEStronglyMeasurable (Err n) P)
    (hErrAE : ∀ᵐ ω ∂P, Tendsto (fun n => Err n ω) atTop (𝓝 (0 : ℝ)))
    (H : Ω → ℝ) (hHI : Integrable H P)
    (hDom : ∀ n, ∀ᵐ ω ∂P, ‖Err n ω‖ ≤ H ω) :
    (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
    Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))  := by
  have hErrInt (n : ℕ) : Integrable (Err n) P :=
    hHI.mono' (hErrMeas n) (hDom n)
  have hPosInt (n : ℕ) :
      Integrable (fun ω => max (Err n ω) 0) P := by
    have hAbs : Integrable (fun ω => |Err n ω|) P :=
      (hErrInt n).abs
    have hPlus : Integrable (fun ω => Err n ω + |Err n ω|) P :=
      (hErrInt n).add hAbs
    have hHalf : Integrable
        (fun ω => (1 / 2 : ℝ) * (Err n ω + |Err n ω|)) P :=
      hPlus.const_mul (1 / 2 : ℝ)
    have hrepr : (fun ω => max (Err n ω) 0) =
        (fun ω => (1 / 2 : ℝ) * (Err n ω + |Err n ω|)) := by
      funext ω
      rcases le_total (Err n ω) 0 with hn | hp
      · rw [max_eq_right hn, abs_of_nonpos hn]
        ring
      · rw [max_eq_left hp, abs_of_nonneg hp]
        ring
    rw [hrepr]
    exact hHalf
  have hPosDom (n : ℕ) :
      ∀ᵐ ω ∂P, ‖max (Err n ω) 0‖ ≤ H ω := by
    filter_upwards [hDom n] with ω hω
    have hnorm : ‖max (Err n ω) 0‖ ≤ ‖Err n ω‖ := by
      rcases le_total (Err n ω) 0 with hn | hp
      · rw [max_eq_right hn]
        simp
      · rw [max_eq_left hp]
    exact hnorm.trans hω
  have hPosAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => max (Err n ω) 0) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hErrAE] with ω hω
    simpa using hω.max (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  refine ⟨hPosInt, ?_⟩
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    H (fun n => (hPosInt n).aestronglyMeasurable) hHI hPosDom hPosAE
  simpa using hDCT
