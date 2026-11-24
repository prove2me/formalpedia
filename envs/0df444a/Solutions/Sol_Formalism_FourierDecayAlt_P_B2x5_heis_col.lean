-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.heis_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:39.417546+00:00
-- url     : https://prove2.me/submissions/fbc3639f-c0c2-4fd1-a46c-8f8f80c54a99

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_dual_base_vector_last_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_restriction_dual_base_vector_zero
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5_heis_act__04df4e81c20a
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_zero_left

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
theorem _root_.solution (k r' : ℕ) (x : HPar k r') (p : Fin (2 * (1 + r') + k + 1)) :
    heis0 k r' x p (iL k r') = (es0 k r' + (liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r')) p := by
  have hcol : heis0 k r' x p (iL k r') = (heis0 k r' x *ᵥ es0 k r') p := by
    simp [dual_base_vector_eq_single, mulVec, dotProduct, Pi.single_apply]
  rw [hcol]
  simp only [heis0]
  rw [heis_act', restriction_dual_base_vector_zero, dual_base_vector_last_one, herm_zero_left]
  simp
end Formalism.FourierDecayAlt.P.B2x5
