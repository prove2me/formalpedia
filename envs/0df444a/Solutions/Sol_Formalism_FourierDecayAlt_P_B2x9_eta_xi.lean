-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.eta_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:57:47.396156+00:00
-- url     : https://prove2.me/submissions/d67f180e-c46b-4e23-b253-8fa729e6aa3c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_liftVec_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_liftVec_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_levPos_ne_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_levPos_ne_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_first_ne_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_xi_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_hb_im
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_im


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (p : ℂ × HPar k r') (hc : p.1 ≠ 0) : eta k r' (xi k r' p) = p := by
  obtain ⟨c, y, s⟩ := p
  simp only at hc
  have hL : xi k r' (c, y, s) (iL k r') = c := xi_last _
  have hM : ∀ j, xi k r' (c, y, s) (levPos k 1 r' j) = c * y j := by
    intro j
    simp [xi, dual_base_vector_eq_single, e0_eq, liftVec_mid, Pi.single_apply, levPos_ne_first, levPos_ne_last]
  have hF : xi k r' (c, y, s) (iF k r') = c * hb k r' y s := by
    simp [xi, dual_base_vector_eq_single, e0_eq, liftVec_first, Pi.single_apply, first_ne_last]
  simp only [eta, hL, hM, hF]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext j
    show c * y j / c = y j
    rw [mul_comm, mul_div_assoc, div_self hc, mul_one]
  · show (c * hb k r' y s / c).im = s
    rw [mul_comm, mul_div_assoc, div_self hc, mul_one, hb_im]
end Formalism.FourierDecayAlt.P.B2x9
