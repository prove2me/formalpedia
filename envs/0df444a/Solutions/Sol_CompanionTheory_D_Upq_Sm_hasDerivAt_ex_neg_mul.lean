-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.hasDerivAt_ex_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:11.242197+00:00
-- url     : https://prove2.me/submissions/e8c0bd2c-8242-4074-8353-f19f0fa772b7

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_mulR_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution (X g : Mat n) (t : ℝ) :
    HasDerivAt (fun s => ex X (-s) * g) (-(X * (ex X (-t) * g))) t := by
  have h0 : HasDerivAt (ex X) X 0 := by simpa using hasDerivAt_mul_ex 1 X
  have h1 : HasDerivAt (fun s : ℝ => t - s) (-1) t := (hasDerivAt_id t).const_sub t
  have h2 : HasDerivAt (fun s => ex X (t - s)) ((-1 : ℝ) • X) t :=
    HasDerivAt.scomp_of_eq t h0 h1 (sub_self t).symm
  have h3 := (mulR (ex X (-t) * g)).hasFDerivAt.comp_hasDerivAt t h2
  have e : (fun s => ex X (-s) * g) = mulR (ex X (-t) * g) ∘ fun s => ex X (t - s) := by
    ext1 s
    rw [Function.comp, mulR_apply, ← Matrix.mul_assoc, ← ex_add]
    congr 2; ring
  rw [e]
  exact h3.congr_deriv ((mulR_apply _ _).trans (by simp))
end CompanionTheory.D.Upq.Sm
