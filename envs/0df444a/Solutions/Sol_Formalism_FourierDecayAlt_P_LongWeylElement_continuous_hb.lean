-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.continuous_hb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:58.356969+00:00
-- url     : https://prove2.me/submissions/fa194eaf-d954-405c-9a4e-dc6d1d5982a4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_continuous_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_herm


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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (k r' : ℕ) : Continuous fun x : HPar k r' => hb k r' x.1 x.2 := by
  have h1 : Continuous fun x : HPar k r' => herm (Hpk k r') x.1 x.1 := by
    first
      | exact (continuous_herm (Hpk k r')).comp (continuous_fst.prodMk continuous_fst)
      | exact (continuous_herm (Hpk k r')).comp (continuous_fst.prod_mk continuous_fst)
  unfold hb
  first
    | fun_prop
    | exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp h1).neg.div_const 2)).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
end Formalism.FourierDecayAlt.P.LongWeylElement
