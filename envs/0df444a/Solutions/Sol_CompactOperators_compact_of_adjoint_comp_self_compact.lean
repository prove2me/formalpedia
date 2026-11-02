-- Prove2me | solution 1 for CompactOperators.compact_of_adjoint_comp_self_compact
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:20:52.350555+00:00
-- url     : https://prove2.me/submissions/0242c44d-8afb-4196-84dd-05a6e613120c

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

universe u v w
open Set Metric
open scoped InnerProductSpace

theorem solution {𝕜 : Type v} [RCLike 𝕜]
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : IsCompactOperator (T.adjoint ∘L T)) :
    IsCompactOperator T := by
  classical
  let A := T.adjoint ∘L T
  let S : Set E := closedBall 0 1
  have hA : TotallyBounded (A '' S) := by
    apply (hT.isCompact_closure_image_closedBall 1).totallyBounded.subset
    exact subset_closure
  have hineq : ∀ x ∈ S, ∀ y ∈ S, ‖T x - T y‖ ^ 2 ≤ 2 * ‖A x - A y‖ := by
    intro x hx y hy
    have hx' : ‖x‖ ≤ 1 := by simpa [S, mem_closedBall, dist_zero_right] using hx
    have hy' : ‖y‖ ≤ 1 := by simpa [S, mem_closedBall, dist_zero_right] using hy
    have hxy : ‖x - y‖ ≤ 2 := by
      calc
        ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    calc
      ‖T x - T y‖ ^ 2 = RCLike.re ⟪A (x - y), x - y⟫_𝕜 := by
        simpa [A, map_sub] using T.apply_norm_sq_eq_inner_adjoint_left (x - y)
      _ ≤ ‖A (x - y)‖ * ‖x - y‖ := re_inner_le_norm _ _
      _ ≤ 2 * ‖A x - A y‖ := by
        rw [map_sub]
        nlinarith [norm_nonneg (A x - A y)]
  have hcompact : TotallyBounded (T '' S) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨s, hsS, hsfin, hcover⟩ := Metric.finite_approx_of_totallyBounded hA (ε^2 / 4) (by positivity)
    choose f hf using fun z : s => hsS z.property
    have : Finite s := hsfin.to_subtype
    refine ⟨(fun z : s => T (f z)) '' univ, Set.finite_univ.image _, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxA : A x ∈ A '' S := ⟨x, hx, rfl⟩
    have hxcover := hcover hxA
    simp only [mem_iUnion, mem_ball] at hxcover ⊢
    obtain ⟨z, hz, hdist⟩ := hxcover
    let z' : s := ⟨z, hz⟩
    refine ⟨T (f z'), ⟨z', mem_univ _, rfl⟩, ?_⟩
    have hfz : f z' ∈ S ∧ A (f z') = z := hf z'
    have hi := hineq x hx (f z') hfz.1
    have hd : ‖A x - A (f z')‖ < ε^2 / 4 := by
      simpa [dist_eq_norm, hfz.2] using hdist
    rw [dist_eq_norm]
    nlinarith [sq_nonneg (‖T x - T (f z')‖ - ε)]
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall T.toLinearMap (by norm_num : (0:ℝ) < 1)).2
  exact (totallyBounded_closure.mpr hcompact).isCompact_of_isClosed isClosed_closure

