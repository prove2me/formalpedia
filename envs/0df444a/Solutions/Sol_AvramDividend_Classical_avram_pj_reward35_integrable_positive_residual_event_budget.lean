-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward35_integrable_positive_residual_event_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:17:51.311226+00:00
-- url     : https://prove2.me/submissions/7fcf5eac-06d2-4cf0-9fc9-b35bc4f498ce

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (A : Set Ω) (G H : Ω → ℝ)
    (a ε : ℝ) (hG : Integrable G P) (hH : Integrable H P)
    (hres : (∫ ω in A, max (0 : ℝ) (G ω - a - H ω) ∂P) ≤ ε) :
    (∫ ω in A, G ω ∂P) ≤ a * (P A).toReal +
      (∫ ω in A, H ω ∂P) + ε := by
  classical
  let Q : Ω → ℝ := fun ω => G ω - a - H ω
  have hQ : Integrable Q P := (hG.sub (integrable_const (μ := P) a)).sub hH
  have hP : Integrable (fun ω => max (0 : ℝ) (Q ω)) P :=
    (integrable_const (μ := P) (0 : ℝ)).sup hQ
  have hs : (∫ ω in A, max (0 : ℝ) (Q ω) ∂P) ≤ ε := by
    simpa only [Q] using hres
  have hh : (∫ ω in A, Q ω ∂P) ≤ ε :=
    (integral_mono_ae hQ.integrableOn hP.integrableOn
      (Filter.Eventually.of_forall (fun ω =>
        le_max_right (0 : ℝ) (Q ω)))).trans hs
  have hGOn : IntegrableOn G A P := hG.integrableOn
  have hHOn : IntegrableOn H A P := hH.integrableOn
  have hCOn : IntegrableOn (fun _ : Ω => a) A P :=
    (integrable_const (μ := P) a).integrableOn
  have heq : (∫ ω in A, Q ω ∂P) =
      (∫ ω in A, G ω ∂P) - a * (P A).toReal -
      (∫ ω in A, H ω ∂P) := by
    calc
      (∫ ω in A, Q ω ∂P)
          = (∫ ω in A, (G ω - a) - H ω ∂P) := rfl
      _ = (∫ ω in A, G ω - a ∂P) -
          (∫ ω in A, H ω ∂P) :=
        integral_sub (hGOn.sub hCOn) hHOn
      _ = ((∫ ω in A, G ω ∂P) - (∫ ω in A, a ∂P)) -
          (∫ ω in A, H ω ∂P) := by
        rw [integral_sub hGOn hCOn]
      _ = _ := by simp [Measure.real, mul_comm]
  rw [heq] at hh
  linarith
