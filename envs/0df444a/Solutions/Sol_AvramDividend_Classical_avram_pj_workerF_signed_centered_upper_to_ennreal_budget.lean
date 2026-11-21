-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerF_signed_centered_upper_to_ennreal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T22:56:54.890439+00:00
-- url     : https://prove2.me/submissions/6c28046d-b96c-4f75-9fa0-0a6955a29236

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F M G R : Ω → ℝ) (b : ℝ)
    (hFmeas : AEStronglyMeasurable F P)
    (hFpos : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hMI : Integrable M P) (hM0 : (∫ ω, M ω ∂P) = 0)
    (hG : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P, F ω ≤ b + M ω + G ω + R ω) :
    (∫⁻ ω, ENNReal.ofReal (F ω) ∂P) ≤ ENNReal.ofReal b := by
  have hIto' : ∀ᵐ ω ∂P,
      F ω ≤ b + M ω + (0 : ℝ) + 0 + G ω + R ω := by
    filter_upwards [hIto] with ω hω
    simpa only [add_zero, zero_add] using hω
  obtain ⟨hFI, hMean⟩ :=
    avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
      F M (fun _ => 0) (fun _ => 0) G R b hFmeas hFpos
      hMI (integrable_zero Ω ℝ P) (integrable_zero Ω ℝ P)
      hM0 (integral_zero Ω ℝ) (integral_zero Ω ℝ)
      hG hR hIto'
  have hFin :
      (∫⁻ ω, ENNReal.ofReal (F ω) ∂P) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hFmeas hFpos).2 hFI
  have hEq :
      (∫ ω, F ω ∂P) =
        (∫⁻ ω, ENNReal.ofReal (F ω) ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae hFpos hFmeas
  calc
    (∫⁻ ω, ENNReal.ofReal (F ω) ∂P) =
        ENNReal.ofReal ((∫⁻ ω, ENNReal.ofReal (F ω) ∂P).toReal) := by
      exact (ENNReal.ofReal_toReal hFin).symm
    _ = ENNReal.ofReal (∫ ω, F ω ∂P) := by rw [hEq]
    _ ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal hMean
