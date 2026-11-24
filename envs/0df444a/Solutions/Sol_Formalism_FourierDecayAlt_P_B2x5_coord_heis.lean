-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.coord_heis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:24:52.984464+00:00
-- url     : https://prove2.me/submissions/2dd13a1a-13db-40ac-8d5d-2e53abb17049

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_base_vector_first_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_restriction_base_vector_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_dual_base_vector_first_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_restriction_dual_base_vector_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lifted_vector_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_res_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heis_col

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
theorem _root_.solution (k r' : ℕ) (x : HPar k r') : coord k r' (heis0 k r' x) = x := by
  have h1 : ∀ j, es0 k r' (levPos k 1 r' j) = 0 := fun j => congrFun (restriction_dual_base_vector_zero k r') j
  have h2 : ∀ j, e0 k r' (levPos k 1 r' j) = 0 := fun j => congrFun (restriction_base_vector_zero k r') j
  have h3 : ∀ j, liftVec k 1 r' x.1 (levPos k 1 r' j) = x.1 j := fun j => congrFun (res_lift k r' x.1) j
  simp only [coord, heis_col]
  refine Prod.ext ?_ ?_
  · funext j
    simp [h1, h2, h3]
  · simp [dual_base_vector_first_zero, lifted_vector_first, base_vector_first_one, hb]
end Formalism.FourierDecayAlt.P.B2x5
