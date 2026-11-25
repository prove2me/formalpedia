-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.directions_in_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:15:00.450492+00:00
-- url     : https://prove2.me/submissions/a1efbf0b-069a-40be-a68d-6ab67c509703

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_lower_blocks_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_hpk_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_inv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_conj_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_lie_Y
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_lie_Q

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Ux4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.DirectionsInP := by
  intro k j ρ x
  have hn := Rn_mul_inv x
  constructor
  · intro Y hY
    refine ⟨conj_lie _ _ _ (Rn_unitary x) (hpk_conjTranspose k (j + ρ)) hn (lie_Y Y hY), ?_⟩
    intro i b hb hi
    rw [Rn_inv_eq]
    unfold RnInv Rn
    rw [block3_mul, block3_mul]
    exact block3_lower_blocks_zero _ _ _ _ _ _ _ _ _ (by simp) (by simp) i b hb hi
  · intro Q
    refine ⟨conj_lie _ _ _ (Rn_unitary x) (hpk_conjTranspose k (j + ρ)) hn (lie_Q Q), ?_⟩
    intro i b hb hi
    rw [Rn_inv_eq]
    unfold RnInv Rn
    rw [block3_mul, block3_mul]
    exact block3_lower_blocks_zero _ _ _ _ _ _ _ _ _ (by simp) (by simp) i b hb hi
end Formalism.FourierDecayAlt.P
