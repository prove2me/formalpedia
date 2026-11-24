-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.matrix_entries_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:31.122395+00:00
-- url     : https://prove2.me/submissions/40cf4829-23f4-4a6d-9ce7-41d14374c634

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.conjTranspose * J * M = J) :
    ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2 = 1 ∧ ‖M 0 1‖ ^ 2 - ‖M 1 1‖ ^ 2 = -1 ∧
      ‖M 0 0‖ * ‖M 0 1‖ = ‖M 1 0‖ * ‖M 1 1‖ := by
  have e00 := congrFun (congrFun hM 0) 0
  have e11 := congrFun (congrFun hM 1) 1
  have e01 := congrFun (congrFun hM 0) 1
  simp [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at e00 e11 e01
  rw [Complex.conj_mul', Complex.conj_mul'] at e00 e11
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast e00
  · exact_mod_cast e11
  · have h : (starRingEnd ℂ) (M 0 0) * M 0 1 = (starRingEnd ℂ) (M 1 0) * M 1 1 := by
      linear_combination e01
    have := congrArg norm h
    simpa [norm_mul] using this
end Formalism.SLP.GlobalBoundRefinements.P
