-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.heisenberg_map_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:27:49.870609+00:00
-- url     : https://prove2.me/submissions/1b08790f-8b00-4335-9ac7-4cdde568d4e3

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_liftVec_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_herm_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_hb_cont

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
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution : Continuous (heisF k r') := by
  have hl : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 := liftVec_cont.comp continuous_fst
  have hb' : Continuous fun x : HPar k r' => hb k r' x.1 x.2 := hb_cont
  apply continuous_pi; intro i; apply continuous_pi; intro j
  have h1 : Continuous fun x : HPar k r' => herm (Hpk k (1 + r')) (bvec j) (liftVec k 1 r' x.1) :=
    (herm_cont (Hpk k (1 + r'))).comp (continuous_const.prodMk hl)
  have h2 : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 i := (continuous_apply i).comp hl
  show Continuous fun x : HPar k r' => heisG k r' (liftVec k 1 r' x.1) (hb k r' x.1 x.2) i j
  simp only [heisG, Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  exact (continuous_const.sub (continuous_const.mul h1)).add ((h2.add (hb'.mul continuous_const)).mul continuous_const)
end Formalism.FourierDecayAlt.P.B2x9
