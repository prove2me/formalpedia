-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_dense_elementary_l2_isometry_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:21:09.512579+00:00
-- url     : https://prove2.me/submissions/74747806-0625-4574-97cf-a6227cc9a6ea

import Mathlib
import Mathlib.Analysis.Normed.Operator.Extend

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- A linear elementary stochastic-integral operator, norm-preserving on a
dense real submodule of L² kernels, extends uniquely by L² continuity to the
entire Hilbert input as a norm-preserving continuous linear operator into the
complete L² random variables. This is an abstract completion theorem; the
source process must still supply the elementary map and its isometry. -/
theorem solution
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W]
    (S : Submodule ℝ V)
    (f : S →ₗ[ℝ] W)
    (hDense : DenseRange S.subtype)
    (hIsom : ∀ x : S, ‖f x‖ = ‖(x : V)‖) :
    ∃ I : V →L[ℝ] W,
      (∀ x : S, I (x : V) = f x) ∧
      ∀ v : V, ‖I v‖ = ‖v‖ := by
  have hBound :
      ∀ x : S, ‖f x‖ ≤ (1 : ℝ) * ‖S.subtype x‖ := by
    intro x
    simpa [hIsom x] using (le_refl ‖(x : V)‖)
  let I : V →L[ℝ] W := f.extendOfNorm S.subtype
  have hAgree (x : S) : I (x : V) = f x := by
    change (f.extendOfNorm S.subtype) (S.subtype x) = f x
    exact LinearMap.extendOfNorm_eq hDense ⟨1, hBound⟩ x
  refine ⟨I, hAgree, ?_⟩
  intro v
  refine hDense.induction ?_ ?_ v
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    calc
      ‖I (S.subtype y)‖ = ‖f y‖ := congrArg norm (hAgree y)
      _ = ‖S.subtype y‖ := hIsom y
  · exact isClosed_eq (continuous_norm.comp I.continuous) continuous_norm
