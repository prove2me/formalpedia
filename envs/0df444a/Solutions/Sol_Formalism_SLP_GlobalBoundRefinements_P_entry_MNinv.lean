-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.entry_MNinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:41.114584+00:00
-- url     : https://prove2.me/submissions/e3685e95-e792-4506-b83a-8fe30b687005

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_inv_eq_J

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
theorem _root_.solution (M N : Matrix (Fin 2) (Fin 2) ℂ) (h : N.conjTranspose * J * N = J) :
    (M * N⁻¹) 1 0 = M 1 0 * (starRingEnd ℂ) (N 0 0) - M 1 1 * (starRingEnd ℂ) (N 0 1) := by
  have j00 : J 0 0 = 1 := by simp [J]
  have j01 : J 0 1 = 0 := by simp [J]
  have j10 : J 1 0 = 0 := by simp [J]
  have j11 : J 1 1 = -1 := by simp [J]
  rw [inv_eq_J N h]
  simp [Matrix.mul_apply, Fin.sum_univ_two, j00, j01, j10, j11, Matrix.conjTranspose_apply]
  ring
end Formalism.SLP.GlobalBoundRefinements.P
