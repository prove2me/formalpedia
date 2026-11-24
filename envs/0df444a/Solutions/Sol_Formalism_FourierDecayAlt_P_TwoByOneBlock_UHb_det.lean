-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.UHb_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:27:47.5552+00:00
-- url     : https://prove2.me/submissions/716f158f-e099-45df-b6ff-c12baa5edb83

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Hb_unit

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution {a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (ha : a ∈ UH (Hb k)) : ‖a.det‖ = 1 := by
  have h : aᴴ * Hb k * a = Hb k := ha
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
  have h0 : (Hb k).det ≠ 0 := Hb_unit.ne_zero
  have h3 : star a.det * a.det = 1 := by
    have : (star a.det * a.det) * (Hb k).det = 1 * (Hb k).det := by
      rw [one_mul]
      calc (star a.det * a.det) * (Hb k).det = star a.det * (Hb k).det * a.det := by ring
        _ = (Hb k).det := h2
    exact mul_right_cancel₀ h0 this
  have h4 : ‖a.det‖ * ‖a.det‖ = 1 := by
    have := congrArg norm h3
    rwa [norm_mul, norm_star, norm_one] at this
  nlinarith [norm_nonneg a.det]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
