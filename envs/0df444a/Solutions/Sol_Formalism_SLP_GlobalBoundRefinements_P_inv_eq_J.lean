-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.inv_eq_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:30.284294+00:00
-- url     : https://prove2.me/submissions/5dd0054a-fc0d-4461-a44c-4d025dfccd0a

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_JJ

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
theorem _root_.solution (N : Matrix (Fin 2) (Fin 2) ℂ) (h : N.conjTranspose * J * N = J) :
    N⁻¹ = J * N.conjTranspose * J := by
  apply Matrix.inv_eq_left_inv
  calc J * N.conjTranspose * J * N = J * (N.conjTranspose * J * N) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, JJ]
end Formalism.SLP.GlobalBoundRefinements.P
