-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.norm_orbM_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:56.061316+00:00
-- url     : https://prove2.me/submissions/402f7d04-bede-4cd6-9b8d-5709a313ad47

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_isStrictUpper_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_entry_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_strictUpper_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_matrix_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_shape_of_matrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates
theorem _root_.solution (m : ℕ) (t c : ℂ) (p : BlockCoord (m + 1)) : ‖t‖ ≤ ‖orbM (m + 1) t c p‖ := by
  have hX : IsStrictUpper (Xof t p.2.1) := by
    unfold Xof
    rw [← strictUpper_smul]
    exact isStrictUpper_strictUpper _
  have h := (shape_of_matrix m t (c + p.1 ⬝ᵥ (wMat (m + 1) *ᵥ (t • p.2.2))) (Xof t p.2.1) (t • p.2.2)
    (rhoOf t p.1 p.2.1) hX).2.1 0 ⟨m, by omega⟩ (by simp)
  have e0 : orbM (m + 1) t c p = Mcoord t (Xof t p.2.1) (t • p.2.2) (rhoOf t p.1 p.2.1)
      (c + p.1 ⬝ᵥ (wMat (m + 1) *ᵥ (t • p.2.2))) := matrix_entries (m + 1) t c p
  have e : orbM (m + 1) t c p 0 ⟨m, by omega⟩ = t := by
    rw [e0]; exact h
  calc ‖t‖ = ‖orbM (m + 1) t c p 0 ⟨m, by omega⟩‖ := by rw [e]
    _ ≤ _ := norm_entry_le _ _ _
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
