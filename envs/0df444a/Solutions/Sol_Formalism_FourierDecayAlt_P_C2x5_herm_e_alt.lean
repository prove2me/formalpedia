-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x5.herm_e_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:17:06.039611+00:00
-- url     : https://prove2.me/submissions/18e899f3-f778-4b21-83be-4258a3799d4c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_bvec_right
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap
import Theorems.Thm_Formalism_QuantumDeterminants_ggHpk_mulVec_Wb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x5
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x5
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Fin (2 * r + k + 1))
    (hx : x.val < r ∨ r + k < x.val) : herm (Hpk k r) (bvec x) z = 0 := by
  rw [ggHerm_swap (Hpk k r) (GBasic.Hpk_herm k r), bvec, ggHerm_bvec_right, ggHpk_mulVec_Wb k r z hz,
    hz x hx, mul_zero, star_zero]
end Formalism.FourierDecayAlt.P.C2x5
