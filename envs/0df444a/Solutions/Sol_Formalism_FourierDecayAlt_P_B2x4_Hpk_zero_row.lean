-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.Hpk_zero_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:01:28.931706+00:00
-- url     : https://prove2.me/submissions/eb07eafc-8c97-414f-ab0d-fb379c428d14

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
theorem _root_.solution (k r' : ℕ) (j : Fin (2 * (1 + r') + k + 1)) :
    Hpk k (1 + r') (eI k (1 + r') (a0 r')) j = if j.val = 2 * (1 + r') + k then 1 else 0 := by
  have hv : (eI k (1 + r') (a0 r')).val = 0 := rfl
  unfold Hpk
  split_ifs <;> first | rfl | (exfalso; omega)
end Formalism.FourierDecayAlt.P.B2x4
