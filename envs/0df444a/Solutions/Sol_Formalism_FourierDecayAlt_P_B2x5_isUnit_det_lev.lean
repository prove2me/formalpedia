-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.isUnit_det_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:05:27.54816+00:00
-- url     : https://prove2.me/submissions/09eba41a-033f-47da-a959-810931858dfa

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_one

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
theorem _root_.solution {k r' : ℕ} {g : Mat k r'} (hg : IsUnit g.det) : IsUnit (ιLev k 1 r' g).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := ιLev k 1 r' g⁻¹)
  rw [lev_mul, Matrix.mul_nonsing_inv _ hg, lev_one]
end Formalism.FourierDecayAlt.P.B2x5
