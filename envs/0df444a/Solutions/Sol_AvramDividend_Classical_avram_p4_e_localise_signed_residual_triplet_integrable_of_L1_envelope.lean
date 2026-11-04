-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_signed_residual_triplet_integrable_of_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:39:06.912658+00:00
-- url     : https://prove2.me/submissions/8e54e085-50e3-4ff1-9dc3-3f297980d397

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- An L1 envelope simultaneously bounds the three signed terms in the genuine residual budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (M G H E : Ω → ℝ)
    (hE : Integrable E P)
    (hM : AEStronglyMeasurable M P)
    (hG : AEStronglyMeasurable G P)
    (hH : AEStronglyMeasurable H P)
    (hDom : ∀ᵐ ω ∂P, |M ω| + |G ω| + |H ω| ≤ |E ω|) :
    Integrable M P ∧ Integrable G P ∧ Integrable H P := by
  have hMdom : ∀ᵐ ω ∂P, ‖M ω‖ ≤ ‖E ω‖ := by
    filter_upwards [hDom] with ω h
    have hnonneg : 0 ≤ |G ω| + |H ω| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hm : |M ω| ≤ |E ω| := by linarith
    simpa only [Real.norm_eq_abs] using hm
  have hGdom : ∀ᵐ ω ∂P, ‖G ω‖ ≤ ‖E ω‖ := by
    filter_upwards [hDom] with ω h
    have hm : |G ω| ≤ |E ω| := by
      have h0m : 0 ≤ |M ω| := abs_nonneg _
      have h0h : 0 ≤ |H ω| := abs_nonneg _
      linarith
    simpa only [Real.norm_eq_abs] using hm
  have hHdom : ∀ᵐ ω ∂P, ‖H ω‖ ≤ ‖E ω‖ := by
    filter_upwards [hDom] with ω h
    have hm : |H ω| ≤ |E ω| := by
      have h0m : 0 ≤ |M ω| := abs_nonneg _
      have h0g : 0 ≤ |G ω| := abs_nonneg _
      linarith
    simpa only [Real.norm_eq_abs] using hm
  exact ⟨Integrable.mono hE hM hMdom,
    Integrable.mono hE hG hGdom,
    Integrable.mono hE hH hHdom⟩
