-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.heisenberg_mul_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:27.081752+00:00
-- url     : https://prove2.me/submissions/80c04a1c-64af-4377-935c-11a3ca28e953

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_neg_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_self_im
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heisMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heisenberg_at_zero

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
theorem _root_.solution (k r' : ℕ) (x : HPar k r') : heis0 k r' x * heis0 k r' (-x.1, -x.2) = 1 := by
  rw [heisMul k r' x (-x.1, -x.2)]
  have h : (herm (Hpk k r') (-x.1) x.1).im = 0 := by
    rw [herm_neg_left, Complex.neg_im, herm_self_im, neg_zero]
  convert heisenberg_at_zero k r' using 2 <;> simp [h]
end Formalism.FourierDecayAlt.P.B2x5
