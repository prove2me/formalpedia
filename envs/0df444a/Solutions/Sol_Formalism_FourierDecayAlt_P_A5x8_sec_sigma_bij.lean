-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_sigma_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:00.920136+00:00
-- url     : https://prove2.me/submissions/ca622912-151b-44e3-9e3d-3c0d9b020750

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_low_bij
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_up_bij

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (h : Point K) (c : Kˣ) :
    Function.Bijective (fun t => toCos R (sec_sigma R h c t)) := by
  have h1 := ((sec_low_bij R h c).prodMap (sec_up_bij R h c)).comp
    (Equiv.prodProdProdComm (Quotient (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2))))
      (upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum)) (Fin h.1.sum → KR R)
      (Fin h.1.sum → KR R)).bijective
  exact h1
end Formalism.FourierDecayAlt.P.A5x8
