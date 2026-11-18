-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva44_probability_signed_B_integrable_of_one_sided_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:16:20.063181+00:00
-- url     : https://prove2.me/submissions/3b825c29-a940-475d-b795-bb0e74309a76

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F M B E : Ω → ℝ) (a : ℝ)
    (hFI : Integrable F P)
    (hMI : Integrable M P)
    (hEI : Integrable (fun ω => max (E ω) 0) P)
    (hBmeas : AEStronglyMeasurable B P)
    (hBnonpos : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hBound : ∀ᵐ ω ∂P,
      F ω ≤ a + M ω + B ω + max (E ω) 0) :
    Integrable B P := by
  have hG : Integrable
      (fun ω => a + M ω + max (E ω) 0 - F ω) P :=
    (((integrable_const a).add hMI).add hEI).sub hFI
  have hNeg : Integrable (fun ω => -B ω) P := by
    apply Integrable.mono_nonneg hG hBmeas.neg
    · filter_upwards [hBnonpos] with ω hω
      change 0 ≤ -B ω
      linarith
    · filter_upwards [hBound] with ω hω
      change -B ω ≤ a + M ω + max (E ω) 0 - F ω
      linarith
  have hNegNeg : Integrable (fun ω => -(-B ω)) P := by
    convert hNeg.neg using 1
    funext ω
    simp
  simpa only [neg_neg] using hNegNeg
