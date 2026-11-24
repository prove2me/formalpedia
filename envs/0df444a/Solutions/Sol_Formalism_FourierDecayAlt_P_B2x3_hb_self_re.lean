-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.hb_self_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:24:18.720545+00:00
-- url     : https://prove2.me/submissions/9aa1214c-dd48-4b13-ad4a-b994c2fd292a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_hb_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_normsq_eq

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution (v : Fin (k + 1) → ℂ) :
    (star v ⬝ᵥ (Hb k *ᵥ v)).re = (∑ i : Fin k, ‖v i.castSucc‖ ^ 2) - ‖v (Fin.last k)‖ ^ 2 := by
  rw [hb_form]
  simp only [normsq_eq]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]
end Formalism.FourierDecayAlt.P.B2x3
