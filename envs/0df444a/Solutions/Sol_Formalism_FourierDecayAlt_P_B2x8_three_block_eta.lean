-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.three_block_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:47:36.766273+00:00
-- url     : https://prove2.me/submissions/2db5c762-7aff-4ff0-bd49-f8dc968eb6d5

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (u : Fin (2 * (1 + r') + k + 1) → ℂ) : mk3 k r' (cF u) (mid u) (cL u) = u := by
  funext i
  have hi := i.isLt
  rw [three_block_apply]
  split_ifs with h1 h2
  · exact congrArg u (Fin.ext (by (try simp only [Fin.val_mk]); omega))
  · exact congrArg u (Fin.ext (by (try simp only [levPos, Fin.val_mk]); omega))
  · exact congrArg u (Fin.ext (by (try simp only [Fin.val_mk]); omega))
end Formalism.FourierDecayAlt.P.B2x8
