-- Prove2me | solution 1 for BianchiIX.exists_scalar_event_branch_two
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:59:44.1101+00:00
-- url     : https://prove2.me/submissions/226dc159-15fd-4a5f-99e8-77d81cce7c2a

import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology


/-- A transverse scalar equation gives a locally unique C2 branch with its actual derivative. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Q : E × ℝ → ℝ} {x : E} {t a : ℝ}
    (hQ : ContDiffAt ℝ 2 Q (x, t))
    (hd : HasDerivAt (fun u => Q (x, u)) a t) (ha : a ≠ 0) :
    ∃ τ : E → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
      HasFDerivAt τ (-a⁻¹ • (fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x ∧
      (∀ᶠ y in 𝓝 x, Q (y, τ y) = Q (x, t)) ∧
      (∀ᶠ z in 𝓝 (x, t), Q z = Q (x, t) ↔ τ z.1 = z.2) := by
  have htime : (fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
      a • ContinuousLinearMap.id ℝ ℝ := by
    have H := ((hQ.differentiableAt (by norm_num)).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_right x t)).unique hd.hasFDerivAt
    rw [H]
    ext
    simp [mul_comm]
  have hright : (a • ContinuousLinearMap.id ℝ ℝ).comp (a⁻¹ • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [ha]
  have hleft : (a⁻¹ • ContinuousLinearMap.id ℝ ℝ).comp (a • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [ha]
  have hinv : ((fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    rw [htime]
    exact ContinuousLinearMap.IsInvertible.of_inverse hright hleft
  let τ := hQ.implicitFunction (by norm_num) hinv
  refine ⟨τ, hQ.implicitFunction_apply_self (by norm_num) hinv,
    hQ.contDiffAt_implicitFunction (by norm_num) hinv, ?_,
    hQ.eventually_apply_implicitFunction (by norm_num) hinv,
    hQ.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv⟩
  have H := (hQ.hasStrictFDerivAt_implicitFunction (by norm_num) hinv).hasFDerivAt
  rw [htime, ContinuousLinearMap.inverse_eq hright hleft] at H
  convert! H using 1
  ext v
  simp
