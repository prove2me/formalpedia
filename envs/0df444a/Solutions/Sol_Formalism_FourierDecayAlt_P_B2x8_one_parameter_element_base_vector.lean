-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.one_parameter_element_base_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:12.946104+00:00
-- url     : https://prove2.me/submissions/22518332-f125-4048-934a-15c503628e9c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_herm_zero_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_heis_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_fixes_isotropic_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_levi_fixes_isotropic_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_long_weyl_element_base_vector

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
theorem _root_.solution (x x' : HPar k r') (c : ℂ) (g₁ : Mat k r') :
    oneStep k r' x c g₁ x' *ᵥ e0 k r' = mk3 k r' (c * hb k r' (-x.1) (-x.2)) (c • (-x.1)) c := by
  unfold oneStep
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, heisenberg_fixes_isotropic_vector, levi_fixes_isotropic_vector, long_weyl_element_base_vector, al_heis_inv, heisenberg_three_block]
  dsimp only
  rw [al_herm_zero_left]
  simp
end Formalism.FourierDecayAlt.P.B2x8
