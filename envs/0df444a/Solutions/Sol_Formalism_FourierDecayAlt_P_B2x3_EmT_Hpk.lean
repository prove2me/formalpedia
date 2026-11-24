-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.EmT_Hpk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:59:56.095613+00:00
-- url     : https://prove2.me/submissions/53db6566-c5c7-4180-a465-5fddf481f097

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Em_conjT
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Hpk_Em
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Hb_conjT
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


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
theorem _root_.solution : (Em k r)ᵀ * Hpk k r = Hb k * (Em k r)ᵀ := by
  have h := congrArg Matrix.conjTranspose (Hpk_Em (k := k) (r := r))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Em_conjT, (hpkFacts k r).1, Hb_conjT] at h
  exact h
end Formalism.FourierDecayAlt.P.B2x3
