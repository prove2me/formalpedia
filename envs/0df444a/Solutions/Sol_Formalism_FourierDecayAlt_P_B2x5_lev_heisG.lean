-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.lev_heisG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:41.646785+00:00
-- url     : https://prove2.me/submissions/0470477d-71ad-43ca-93d7-ce72711a72a4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_mat_ext
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5_heis_act__04df4e81c20a
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_act_iL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_act_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_levi_fixes_base_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_lift

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
theorem _root_.solution (k r' : ℕ) {g : Mat k r'} (hg : g ∈ GV k r') (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) :
    ιLev k 1 r' g * heisG k r' (liftVec k 1 r' y) b = heisG k r' (liftVec k 1 r' (g *ᵥ y)) b * ιLev k 1 r' g := by
  apply mat_ext
  intro u
  rw [← mulVec_mulVec, ← mulVec_mulVec, heis_act', heis_act', lev_act_res, lev_act_iL, herm_UH (H := Hpk k r') hg]
  simp only [mulVec_add, mulVec_sub, mulVec_smul, levi_fixes_base_vector, lev_lift]
end Formalism.FourierDecayAlt.P.B2x5
