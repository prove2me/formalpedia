-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb39_fourth_lintegral_bound_gives_real_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:41:15.7891+00:00
-- url     : https://prove2.me/submissions/27971638-3346-4f06-8a4c-3fdf5f43d70c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Convert a finite fourth-moment ENNReal lintegral bound to a real expectation
bound on the same probability space. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → ℝ) (hZ : Measurable Z) (B : ℝ) (hB : 0 ≤ B)
    (hFourth : (∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P) ≤ ENNReal.ofReal B) :
    Integrable (fun ω => Z ω ^ 4) P ∧
      (∫ ω, Z ω ^ 4 ∂P) ≤ B := by
  have hMeas : Measurable (fun ω => ENNReal.ofReal (Z ω ^ 4)) :=
    ENNReal.measurable_ofReal.comp (hZ.pow_const 4)
  have hFinite : (∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hFourth ENNReal.ofReal_lt_top)
  have hToReal : Integrable
      (fun ω => (ENNReal.ofReal (Z ω ^ 4)).toReal) P :=
    integrable_toReal_of_lintegral_ne_top
      hMeas.aemeasurable hFinite
  have hI : Integrable (fun ω => Z ω ^ 4) P := by
    convert hToReal using 1
    funext ω
    first
    | rfl
    | exact (ENNReal.toReal_ofReal (by positivity)).symm
  have hNonneg : 0 ≤ᵐ[P] (fun ω => Z ω ^ 4) :=
    Filter.Eventually.of_forall (fun ω => by positivity)
  have hEq := ofReal_integral_eq_lintegral_ofReal hI hNonneg
  have hBound : ENNReal.ofReal (∫ ω, Z ω ^ 4 ∂P) ≤ ENNReal.ofReal B :=
    hEq.le.trans hFourth
  have hMeanNonneg : 0 ≤ ∫ ω, Z ω ^ 4 ∂P :=
    integral_nonneg (fun ω => by positivity)
  refine ⟨hI, ?_⟩
  have hReal := ENNReal.toReal_mono
    (by simp : ENNReal.ofReal B ≠ ⊤) hBound
  simpa only [ENNReal.toReal_ofReal hMeanNonneg,
    ENNReal.toReal_ofReal hB] using hReal
