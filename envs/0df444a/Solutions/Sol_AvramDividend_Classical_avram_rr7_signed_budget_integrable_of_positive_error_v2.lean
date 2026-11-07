-- Prove2me | solution 1 for AvramDividend.Classical.avram_rr7_signed_budget_integrable_of_positive_error_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:26:37.666194+00:00
-- url     : https://prove2.me/submissions/abcf72f7-58d2-4e7b-9ac0-2fb816612048

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- An integrable upper-budget error bounds the negative signed source in L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (F M B E : Ω → ℝ) (c : ℝ)
    (hF : Integrable F P) (hM : Integrable M P)
    (hB_meas : AEStronglyMeasurable B P)
    (hB_nonpos : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hE : Integrable E P)
    (hBudget : ∀ᵐ ω ∂P, F ω ≤ c + (M ω + B ω) + E ω) :
    Integrable B P := by
  have hC : Integrable (fun _ : Ω => |c|) P := integrable_const _
  have hTop : Integrable (fun ω => |F ω| + |M ω| + |E ω| + |c|) P :=
    ((hF.abs.add hM.abs).add hE.abs).add hC
  apply Integrable.mono hTop hB_meas
  filter_upwards [hB_nonpos, hBudget] with ω hn hb
  change ‖B ω‖ ≤ ‖|F ω| + |M ω| + |E ω| + |c|‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos hn]
  have hAbs : 0 ≤ |F ω| + |M ω| + |E ω| + |c| := by positivity
  rw [abs_of_nonneg hAbs]
  have hf := neg_le_abs (F ω)
  have hm := le_abs_self (M ω)
  have he := le_abs_self (E ω)
  have hc := le_abs_self c
  linarith
