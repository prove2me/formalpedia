-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.res_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:11:41.33618+00:00
-- url     : https://prove2.me/submissions/211138c1-d844-4dca-a071-e6c73c36ae99

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_val

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
theorem _root_.solution (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : res k r' (liftVec k 1 r' y) = y := by
  funext j
  show liftVec k 1 r' y (levPos k 1 r' j) = y j
  have hj := j.isLt
  simp only [liftVec]
  split_ifs with h
  · congr 1
  · exfalso
    apply h
    rw [lev_val]
    constructor <;> omega
end Formalism.FourierDecayAlt.P.B2x5
