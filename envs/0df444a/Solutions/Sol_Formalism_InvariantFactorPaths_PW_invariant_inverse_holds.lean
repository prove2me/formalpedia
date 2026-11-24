-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.invariant_inverse_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:39.728617+00:00
-- url     : https://prove2.me/submissions/1b73f2ba-5fa4-4679-8622-2dfafade0601

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_InvOp_comm_out
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_sub_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : InvInv := by
  intro K W ι _ _ _ _ _ E h l NN hN hev L
  induction L with
  | nil =>
    intro _ u hu _
    refine ⟨fun a ha => by simp at ha, ?_, ?_⟩
    · simpa [InvOp] using hu
    · simp [InvOp]
  | cons z L ih =>
    intro hnd u hu hdiag
    rw [List.nodup_cons] at hnd
    obtain ⟨hzL, hnd⟩ := hnd
    obtain ⟨h1, h2, h3⟩ := ih hnd u hu (fun a ha => hdiag a (List.mem_cons_of_mem _ ha))
    have hz : z ∉ L.toFinset := by simpa using hzL
    have hzz : E z z (InvOp E l L u) = 0 := by
      have e1 := DFunLike.congr_fun (InvOp_comm_out h l z L hzL) u
      simp only [Module.End.mul_apply, hdiag z (by simp), map_zero] at e1
      exact e1
    have hS : ∀ a ∈ L.toFinset, ∀ b ∈ L.toFinset, E a b (InvOp E l L u) = 0 := by
      intro a ha b hb
      exact h1 a (by simpa using ha) b (by simpa using hb)
    have key := Pstep_inv h hN hev hz h2 hS hzz
    simp only [InvOp, Module.End.mul_apply]
    refine ⟨fun a ha b hb => key a (by simpa using ha) b (by simpa using hb), Pstep_mem hN _ _ _ _ h2, ?_⟩
    have h4 := Submodule.add_mem _ (Pstep_sub_mem (E := E) hz l (InvOp E l L u)) h3
    simpa using h4
end Formalism.InvariantFactorPaths.PW
