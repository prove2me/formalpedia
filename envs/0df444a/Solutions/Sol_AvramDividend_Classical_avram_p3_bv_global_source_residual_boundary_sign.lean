-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_global_source_residual_boundary_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:16:15.93258+00:00
-- url     : https://prove2.me/submissions/5dcad053-9248-484e-b000-aa7ff5ffc9ad

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- On the genuine source's common full-measure event, the unassigned BV
    downward residual always helps the capped candidate, including boundaries. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal)) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
        (∑ i : Fin n,
          Real.exp (-(q * (u i : ℝ))) *
            (V (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))) -
              V (riskProcess X x D (u i) ω))) ≤ 0 := by
  have hmono : Monotone V :=
    avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
      C hC w V hw_cont hw0 hw_neg hw_smooth hw_grad hVtop hVfinite
  have hsource :=
    avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos
      X hBV x D V hmono q
  filter_upwards [hsource] with ω hω
  obtain ⟨R, hR, hRm, _, hsum⟩ := hω
  exact ⟨R, hR, hRm, hsum⟩
