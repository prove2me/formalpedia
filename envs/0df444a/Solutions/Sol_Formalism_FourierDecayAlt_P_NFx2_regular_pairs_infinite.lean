-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.regular_pairs_infinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:43:48.141925+00:00
-- url     : https://prove2.me/submissions/685079fa-2fda-46ac-9400-21dea8b0f24b

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (P : M.Par) : {Y : ℂ | Reg P Y ∧ Reg P (Y + 1)}.Infinite := by
  apply cofinite_infinite
  have h2 : {Y : ℂ | ¬ Reg P (Y + 1)}.Finite := by
    have := (nreg_finite P).preimage (f := fun Y : ℂ => Y + 1) (add_left_injective 1).injOn
    simpa using this
  refine ((nreg_finite P).union h2).subset ?_
  intro Y hY
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or] at hY
  rcases hY with h | h
  · exact Or.inl h
  · exact Or.inr h
end Formalism.FourierDecayAlt.P.NFx2
