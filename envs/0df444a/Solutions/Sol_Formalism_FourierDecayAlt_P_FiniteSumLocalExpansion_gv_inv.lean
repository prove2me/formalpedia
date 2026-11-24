-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:04.310988+00:00
-- url     : https://prove2.me/submissions/8b397a7c-1160-4085-9bae-c7efdaf7f121

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
theorem _root_.solution {y : Mat k r} (hy : y ∈ GV k r) : y * y⁻¹ = 1 ∧ y⁻¹ * y = 1 := by
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hl : (Hpk k r * yᴴ * Hpk k r) * y = 1 := by
    calc (Hpk k r * yᴴ * Hpk k r) * y = Hpk k r * (yᴴ * Hpk k r * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hy', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hdet : IsUnit y.det := Matrix.isUnit_det_of_left_inverse hl
  exact ⟨Matrix.mul_nonsing_inv y hdet, Matrix.nonsing_inv_mul y hdet⟩
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
