-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.block3_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:17:38.091136+00:00
-- url     : https://prove2.me/submissions/0ed75ad4-08d6-4db6-957e-572684ec1c0d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_ext_eB

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
theorem _root_.solution : (1 : B.Mat k (j + ρ)) = blk3 (k := k) (j := j) (ρ := ρ) 1 0 0 0 1 0 0 0 1 := by
  apply ext_eB
  intro x y
  rw [block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;>
    simp [Matrix.one_apply, (eB k j ρ).injective.eq_iff]
end Formalism.FourierDecayAlt.P.Ux4
