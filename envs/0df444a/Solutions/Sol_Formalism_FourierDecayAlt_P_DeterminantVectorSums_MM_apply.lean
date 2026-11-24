-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantVectorSums.MM_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:56:17.814844+00:00
-- url     : https://prove2.me/submissions/84940900-d358-4bfe-a71d-a3f379107911

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums
theorem _root_.solution (T : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V) (x : Fin (N + 1) → V) (j : Fin (N + 1)) :
    MM T x j = ∑ l, T j l (x l) := by
  simp [MM, LinearMap.sum_apply]
end Formalism.FourierDecayAlt.P.DeterminantVectorSums
