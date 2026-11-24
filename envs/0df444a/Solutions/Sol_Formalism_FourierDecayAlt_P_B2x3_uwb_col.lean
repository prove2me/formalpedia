-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.uwb_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:17:29.10802+00:00
-- url     : https://prove2.me/submissions/dcd562a9-b7ac-479d-9ee0-159e63d2d22f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_mulVec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_bvec_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_not_mid_cases

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
theorem _root_.solution {g : Mat k r} (hg : g ∈ UWb k r) (i l : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    g l i = if l = i then 1 else 0 := by
  obtain ⟨a, rfl | rfl⟩ := not_mid_cases i hi
  · rw [← mulVec_bvec g (eI k r a) l, (hg.2 a).1, bvec_apply]
  · rw [← mulVec_bvec g (esI k r a) l, (hg.2 a).2, bvec_apply]
end Formalism.FourierDecayAlt.P.B2x3
