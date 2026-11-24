-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.block_three_zero_size_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:17:39.401795+00:00
-- url     : https://prove2.me/submissions/8112a098-625e-4a91-9444-2b6428b3b766

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
theorem _root_.solution : blk3 (k := k) (j := j) (ρ := ρ) 0 0 0 0 0 0 0 0 0 = 0 := by
  apply ext_eB
  intro x y
  rw [block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;> simp
end Formalism.FourierDecayAlt.P.Ux4
