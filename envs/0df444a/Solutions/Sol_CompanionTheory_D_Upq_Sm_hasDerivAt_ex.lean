-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.hasDerivAt_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:00:12.091821+00:00
-- url     : https://prove2.me/submissions/62676660-fe44-4f9c-8b2b-70374489b855

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_add

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
theorem _root_.solution (X : Mat n) (t : ℝ) : HasDerivAt (ex X) (ex X t * X) t := by
  have h1 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h2 := HasDerivAt.scomp_of_eq t (hasDerivAt_mul_ex (ex X t) X) h1 (sub_self t).symm
  have e : ex X = (fun s => ex X t * ex X s) ∘ fun s => s - t := by
    ext1 s
    rw [Function.comp, ← ex_add]
    congr 1; ring
  rw [one_smul, ← e] at h2
  exact h2
end CompanionTheory.D.Upq.Sm
