-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_C1_stopped_signed_HJB_nonpos_auto_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:41:30.837783+00:00
-- url     : https://prove2.me/submissions/9d6b4e8b-e5ee-4de6-9ee2-0919abd997d5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_C1_auto_bounded_signed_HJB_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_strict_cap_C1_Lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_negative_jump_halfline_bound_of_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_admissible_HJB_drift_L1_from_source
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Original stopped signed BV HJB bound with finite-horizon integrability discharged. -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T) (hτ : IsStoppingTime 𝓕.rightCont
(fun ω => (τ ω : WithTop ℝ≥0))) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ)
(hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
(ha : 0 < a) (hab : a ≤ b) (E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
(hbC : ENNReal.ofReal b < C)
(hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
(hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
  X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
:
  let Upre : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    Function.leftLim (fun v : ℝ≥0 =>
      x + X.X v p.2 - rightLimit D v p.2) p.1);
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := (fun p : (ℝ≥0 × Ω) × ℝ =>
    if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
       (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
    else 0);
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0;
  let F : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1) +
       (∫ z in Iio (0 : ℝ),
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
       q * w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1))
    else 0);
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  let M : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  let B : Ω → ℝ := fun ω => (∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  Integrable (fun ω => M ω + B ω) P ∧
  (∫ ω, M ω + B ω ∂P) ≤ 0 := by
  let a0 : ℝ := min a 1
  have ha0 : 0 < a0 := lt_min ha zero_lt_one
  have ha02 : a0 ≤ 2 := (min_le_right a 1).trans (by norm_num)
  have hab0 : a0 ≤ b := (min_le_left a 1).trans hab
  have hEregion0 : ∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a0 b := by
    intro p hp
    exact ⟨(min_le_left a 1).trans (hEregion p hp).1, (hEregion p hp).2⟩
  obtain ⟨L, hL, hLip⟩ :=
    avram_p3_e_compensator_original_strict_cap_C1_Lipschitz
      C w a0 b ha0 hab0 hbC hw_smooth
  obtain ⟨R, hR, hWbound⟩ :=
    avram_p3_e_compensator_negative_jump_halfline_bound_of_continuity
      w hw_cont hw_neg b
  obtain ⟨A, hA, hDeriv⟩ :=
    avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
      C w a0 b ha0 hab0 hbC hw_smooth
  have hFint :=
    avram_p3_e_compensator_original_BV_admissible_HJB_drift_L1_from_source
      X hBV T x C D hD w hw_cont hw_neg q hq
      a0 b L R A ha0 ha02 hab0 hL hR hA
      hLip hWbound hDeriv E hEm hEregion0
  have hEcap : ∀ p ∈ E, ENNReal.ofReal (Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) < C := by
    intro p hp
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (hEregion p hp).2) hbC
  exact avram_p3_e_compensator_original_C1_auto_bounded_signed_HJB_nonpos
    X hBV T τ hτBound hτ x D hD.1.1 w hw_cont hw_neg
    q hq a0 b ha0 ha02 hab0 E hEm hEregion0 C hbC
    hw_smooth hw_gen hEcap hFint
