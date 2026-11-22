-- Prove2me | solution 1 for AvramDividend.Classical.avram_original_masked_three_martingales_positiveclock_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:25:45.086521+00:00
-- url     : https://prove2.me/submissions/cebf18d9-cf04-446f-a714-210d9d8fab8a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_positive_clock_mask_residual_identity
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The three centred original stopped noises imply an eventwise mean bound,
with no compensated martingale assumed to vanish off the event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ρ : Ω → ℝ≥0) (hρmeas : Measurable ρ)
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ)
    (Mc Ms Ml G R : Ω → ℝ)
    (hMcI : Integrable Mc P) (hMsI : Integrable Ms P)
    (hMlI : Integrable Ml P)
    (hMc0 : (∫ ω, Mc ω ∂P) = 0)
    (hMs0 : (∫ ω, Ms ω ∂P) = 0)
    (hMl0 : (∫ ω, Ml ω ∂P) = 0)
    (hG : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hSigned : ∀ᵐ ω ∂P,
      (if ρ ω = 0 then b else F ω) ≤
        b + Mc ω + Ms ω + Ml ω + G ω + R ω) :
    (∫ ω in {ω : Ω | ρ ω ≠ 0}, F ω ∂P) ≤
      b * (P {ω : Ω | ρ ω ≠ 0}).toReal := by
  classical
  let A : Set Ω := {ω : Ω | ρ ω = 0}
  have hA : MeasurableSet A :=
    measurableSet_eq_fun hρmeas measurable_const
  have hMaskI :
      Integrable (fun ω => if ρ ω = 0 then b else F ω) P := by
    have hParts :=
      ((integrable_const b).indicator hA).add
        (hFI.indicator hA.compl)
    have hEq : (fun ω => if ρ ω = 0 then b else F ω) =
        (A.indicator (fun _ : Ω => b) + Aᶜ.indicator F) := by
      funext ω
      by_cases hz : ρ ω = 0 <;> simp [A, Set.indicator, hz]
    rw [hEq]
    exact hParts
  have hRhsI : Integrable
      (fun ω => b + Mc ω + Ms ω + Ml ω) P :=
    (((integrable_const b).add hMcI).add hMsI).add hMlI
  have hDom : ∀ᵐ ω ∂P,
      (if ρ ω = 0 then b else F ω) ≤
        b + Mc ω + Ms ω + Ml ω := by
    filter_upwards [hSigned, hG, hR] with ω hs hg hr
    linarith
  have hMaskMean :
      (∫ ω, (if ρ ω = 0 then b else F ω) ∂P) ≤ b := by
    have hLe := integral_mono_ae hMaskI hRhsI hDom
    simpa [integral_add, integral_const, hMcI, hMsI, hMlI,
      hMc0, hMs0, hMl0, measure_univ, smul_eq_mul] using hLe
  have hResid :
      (∫ ω, (if ρ ω = 0 then b else F ω) - b ∂P) ≤ 0 := by
    rw [integral_sub hMaskI (integrable_const b)]
    simpa [integral_const, Measure.real_def, measure_univ, smul_eq_mul]
      using (sub_nonpos.mpr hMaskMean)
  have hPosResid : (∫ ω in Aᶜ, F ω - b ∂P) ≤ 0 := by
    rw [← avram_p4_f12_positive_clock_mask_residual_identity P A hA F hFI b]
    simpa only [A, Set.mem_setOf_eq] using hResid
  have hPosBound :
      (∫ ω in Aᶜ, F ω ∂P) ≤ b * (P Aᶜ).toReal := by
    have hConst : (∫ ω in Aᶜ, b ∂P) =
        b * (P Aᶜ).toReal := by
      simp [integral_const, Measure.real_def, smul_eq_mul, mul_comm]
    rw [integral_sub hFI.integrableOn (integrable_const b), hConst] at hPosResid
    linarith only [hPosResid]
  simpa only [A, Set.compl_setOf] using hPosBound
