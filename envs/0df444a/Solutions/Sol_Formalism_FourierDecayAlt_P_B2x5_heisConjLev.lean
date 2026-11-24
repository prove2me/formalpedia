-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.heisConjLev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:25:42.152341+00:00
-- url     : https://prove2.me/submissions/caf7e812-5a14-4bfe-bdf8-e0554be283ae

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_isUnit_det_GV
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_isUnit_det_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_heisG

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
theorem _root_.solution : HeisConjLev := by
  intro k r' g hg x
  have hu : IsUnit (ιLev k 1 r' g).det := isUnit_det_lev (isUnit_det_GV hg)
  have hb' : hb k r' (g *ᵥ x.1) x.2 = hb k r' x.1 x.2 := by
    simp only [hb, herm_UH (H := Hpk k r') hg]
  simp only [heis0]
  rw [lev_heisG k r' hg, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hb']
end Formalism.FourierDecayAlt.P.B2x5
