-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.exp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:53:58.647242+00:00
-- url     : https://prove2.me/submissions/7b89f572-bdba-47df-9d0b-c4b45b49b473

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hpk_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {Y : Mat k r} (hY : inLie k r Y) : NormedSpace.exp Y ∈ GV k r := by
  have hU : IsUnit (Hpk k r) := hpk_isUnit
  have hHH : Hpk k r * Hpk k r = 1 := by
    calc Hpk k r * Hpk k r = Hpk k r * (Hpk k r)⁻¹ := by rw [hpk_inv]
      _ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hY' : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    have h1 : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY
    rw [hpk_inv]
    calc Yᴴ = Yᴴ * (Hpk k r * Hpk k r) := by rw [hHH, Matrix.mul_one]
      _ = Yᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc]
      _ = Hpk k r * (-Y) * Hpk k r := by rw [h1, _root_.neg_mul, _root_.mul_neg, _root_.neg_mul]
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  rw [← Matrix.exp_conjTranspose, hY', Matrix.exp_conj _ _ hU, hpk_inv]
  have hE : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)),
      show -Y + Y = (0 : Mat k r) by abel, NormedSpace.exp_zero]
  calc Hpk k r * NormedSpace.exp (-Y) * Hpk k r * Hpk k r * NormedSpace.exp Y
      = Hpk k r * (NormedSpace.exp (-Y) * (Hpk k r * Hpk k r) * NormedSpace.exp Y) := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [hHH, Matrix.mul_one, hE, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.B4
