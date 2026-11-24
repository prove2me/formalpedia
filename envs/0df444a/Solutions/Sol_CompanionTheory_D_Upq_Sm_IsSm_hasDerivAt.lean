-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.IsSm.hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:03:41.163009+00:00
-- url     : https://prove2.me/submissions/5fddd574-f0d4-49c6-956a-18786ef6c8c8

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_differentiableAt


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
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace CompanionTheory.D.Upq.Sm
namespace IsSm
theorem _root_.solution (h : RepOn G σ) {u : H} (hu : IsSm G σ u) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) (t : ℝ) :
    HasDerivAt (fun s => σ (ex X s) u) (σ (ex X t) (ds σ X u)) t := by
  have h0 := (hu.differentiableAt h hX).hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h2 := HasDerivAt.scomp_of_eq t h0 h1 (sub_self t).symm
  have h3 := ((σ (ex X t)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h2
  have e : (fun s => σ (ex X s) u) = ((σ (ex X t)).restrictScalars ℝ) ∘
      ((fun t : ℝ => σ (ex X t) u) ∘ fun s => s - t) := by
    ext1 s
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
    rw [← h.apply_mul (hX t) (hX _), ← ex_add]
    congr 3; ring
  rw [e]
  simpa [ds] using h3
end IsSm
end CompanionTheory.D.Upq.Sm
