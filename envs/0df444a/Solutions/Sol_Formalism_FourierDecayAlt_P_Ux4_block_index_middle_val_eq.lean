-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.block_index_middle_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:26:03.718884+00:00
-- url     : https://prove2.me/submissions/c75e1b32-0c59-40b6-8836-d162116e85d1

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution (v : Fin (2 * ρ + k + 1)) : ((eB k j ρ) (Sum.inl (Sum.inr v))).val = j + v.val := by
  simp [eB]
end Formalism.FourierDecayAlt.P.Ux4
