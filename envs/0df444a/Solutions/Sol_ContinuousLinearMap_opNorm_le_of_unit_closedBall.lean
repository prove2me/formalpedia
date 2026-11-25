-- Prove2me | solution 1 for ContinuousLinearMap.opNorm_le_of_unit_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:22:59.209165+00:00
-- url     : https://prove2.me/submissions/c21bc227-d839-4c63-bfea-af2d700e291e

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Definitions.Def_SNumbers_QuotientMapNorms

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap
variable {𝕜' : Type*} [DenselyNormedField 𝕜']
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜' E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜' F]
namespace ContinuousLinearMap
theorem _root_.solution (f : E →L[𝕜'] F) {C : ℝ}
    (h : ∀ x : E, ‖x‖ ≤ 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [← f.sSup_unitClosedBall_eq_norm]
  refine csSup_le ((Metric.nonempty_closedBall.2 zero_le_one).image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact h x (mem_closedBall_zero_iff.mp hx)
end ContinuousLinearMap
