-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.Hpk_levPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:49:39.555919+00:00
-- url     : https://prove2.me/submissions/52dde36e-7220-440f-805f-a5570eb563aa

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x4
theorem _root_.solution (k r' : ℕ) (i j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') (levPos k 1 r' i) (levPos k 1 r' j) = Hpk k r' i j := by
  have e1 : (levPos k 1 r' i = levPos k 1 r' j) ↔ i.val = j.val := by
    simp only [levPos, Fin.ext_iff]; omega
  have e2 : (i = j) ↔ i.val = j.val := Fin.ext_iff
  have hi : (levPos k 1 r' i).val = i.val + 1 := rfl
  have hj : (levPos k 1 r' j).val = j.val + 1 := rfl
  unfold Hpk
  simp only [e1, e2]
  split_ifs <;> first | rfl | (exfalso; omega)
end Formalism.FourierDecayAlt.P.B2x4
