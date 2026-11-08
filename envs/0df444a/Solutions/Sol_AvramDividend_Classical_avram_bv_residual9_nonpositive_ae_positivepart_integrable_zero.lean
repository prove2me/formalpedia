-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_nonpositive_ae_positivepart_integrable_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:56:19.862493+00:00
-- url     : https://prove2.me/submissions/e613bd36-b72f-40fb-95fa-0f15c2f3cbaf

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-- An almost-everywhere nonpositive random source has zero integrable positive part. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (f : Ω → ℝ) (hf : ∀ᵐ ω ∂P, f ω ≤ 0) :
    Integrable (fun ω => max (f ω) 0) P ∧
      (∫ ω, max (f ω) 0 ∂P) = 0 := by
  have hzero : (fun ω => max (f ω) 0) =ᵐ[P] (fun _ : Ω => (0 : ℝ)) :=
    hf.mono (by
      intro ω hω
      exact max_eq_right hω)
  have hInt0 : Integrable (fun _ : Ω => (0 : ℝ)) P := by simp
  have hInt : Integrable (fun ω => max (f ω) 0) P :=
    hInt0.congr hzero.symm
  refine ⟨hInt, ?_⟩
  rw [integral_congr_ae hzero]
  simp
