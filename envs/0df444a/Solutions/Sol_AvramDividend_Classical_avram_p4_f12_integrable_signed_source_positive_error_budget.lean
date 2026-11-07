-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f12_integrable_signed_source_positive_error_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:41:55.514196+00:00
-- url     : https://prove2.me/submissions/d3cc09b7-1106-41aa-8ede-d98feb003904

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- A centred martingale and nonpositive drift leave only the positive error. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F M G E : Ω → ℝ)
    (hF : Integrable F P) (hM : Integrable M P)
    (hG : Integrable G P) (hE : Integrable E P)
    (b : ℝ) (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGnonpos : (∫ ω, G ω ∂P) ≤ 0)
    (hSource : ∀ᵐ ω ∂P, F ω ≤ b + M ω + G ω + E ω) :
    (∫ ω, F ω ∂P) ≤ b + ∫ ω, max (E ω) 0 ∂P := by
  have hb : Integrable (fun _ : Ω => b) P := integrable_const b
  have hmaxeq (z : ℝ) : max z 0 = (z + |z|) / 2 := by
    by_cases hz : 0 ≤ z
    · rw [max_eq_left hz, abs_of_nonneg hz]
      ring
    · have hzle : z ≤ 0 := le_of_lt (lt_of_not_ge hz)
      rw [max_eq_right hzle, abs_of_nonpos hzle]
      ring
  have hEpos : Integrable (fun ω => max (E ω) 0) P := by
    have heq : (fun ω => max (E ω) 0) =
        (fun ω => (E ω + |E ω|) / 2) := by
      funext ω
      exact hmaxeq (E ω)
    rw [heq]
    exact (hE.add hE.abs).div_const (2 : ℝ)
  have hbM : Integrable (fun ω => b + M ω) P := hb.add hM
  have hbMG : Integrable (fun ω => b + M ω + G ω) P := hbM.add hG
  have hbMGE : Integrable
      (fun ω => b + M ω + G ω + max (E ω) 0) P :=
    hbMG.add hEpos
  have hPoint : ∀ᵐ ω ∂P,
      F ω ≤ b + M ω + G ω + max (E ω) 0 := by
    filter_upwards [hSource] with ω hω
    have hmax : E ω ≤ max (E ω) 0 := le_max_left _ _
    linarith
  have hbound := integral_mono_ae hF hbMGE hPoint
  have hI1 := integral_add hbMG hEpos
  have hI2 := integral_add hbM hG
  have hI3 := integral_add hb hM
  have hConst : (∫ _ω : Ω, b ∂P) = b := by simp
  linarith
