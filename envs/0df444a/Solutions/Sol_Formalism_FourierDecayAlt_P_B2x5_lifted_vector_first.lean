-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.lifted_vector_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:08.732783+00:00
-- url     : https://prove2.me/submissions/2f6e800b-2956-4c75-9ec7-1541b0679786

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_first_index_val

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
theorem _root_.solution (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (i0 k r') = 0 := by
  simp only [liftVec]
  split_ifs with h
  · have := h.1
    rw [first_index_val] at this
    omega
  · rfl
end Formalism.FourierDecayAlt.P.B2x5
