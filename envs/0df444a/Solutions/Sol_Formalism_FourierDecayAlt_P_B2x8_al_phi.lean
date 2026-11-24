-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:04:51.648805+00:00
-- url     : https://prove2.me/submissions/71c407a2-f90d-4b98-98a6-6f91ff843f42

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_split

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
theorem _root_.solution (g : Mat k (1 + r')) (w : Fin (2 * (1 + r') + k + 1) → ℂ) (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (g *ᵥ mk3 k r' a y b) w =
      a * herm (Hpk k (1 + r')) (g *ᵥ e0 k r') w + herm (Hpk k (1 + r')) (g *ᵥ mk3 k r' 0 y 0) w +
        b * herm (Hpk k (1 + r')) (g *ᵥ es0 k r') w := by
  rw [three_block_split a b y]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, herm_add_left, herm_smul_left]
end Formalism.FourierDecayAlt.P.B2x8
