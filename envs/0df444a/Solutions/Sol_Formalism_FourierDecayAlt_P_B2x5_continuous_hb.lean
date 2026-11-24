-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.continuous_hb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:11:49.837202+00:00
-- url     : https://prove2.me/submissions/ff625c9f-0f23-40a5-a058-9baf0df763bb

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) : Continuous fun x : HPar k r' => hb k r' x.1 x.2 := by
  have hc : Continuous fun x : HPar k r' => herm (Hpk k r') x.1 x.1 :=
    (continuous_herm (Hpk k r')).comp (continuous_fst.prodMk continuous_fst)
  simp only [hb]
  first
  | fun_prop
  | exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp hc).neg.div_const 2)).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
end Formalism.FourierDecayAlt.P.B2x5
