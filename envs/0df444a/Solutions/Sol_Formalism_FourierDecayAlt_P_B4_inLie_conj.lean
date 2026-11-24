-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.inLie_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:41.225051+00:00
-- url     : https://prove2.me/submissions/8ec4bcdb-1af7-4200-ae17-e709b065cd6a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
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
theorem _root_.solution {a X : Mat k r} (ha : a ∈ GV k r) (hX : inLie k r X) : inLie k r (a⁻¹ * X * a) := by
  have hH : IsUnit (Hpk k r).det := (Matrix.isUnit_iff_isUnit_det _).mp hpk_isUnit
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hdet : IsUnit a.det := by
    have hd := congrArg Matrix.det ha'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at hd
    rw [isUnit_iff_ne_zero] at hH ⊢
    intro h0
    rw [h0, MulZeroClass.mul_zero] at hd
    exact hH hd.symm
  have e1 : aᴴ * Hpk k r = Hpk k r * a⁻¹ := by
    calc aᴴ * Hpk k r = aᴴ * Hpk k r * (a * a⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = Hpk k r * a⁻¹ := by rw [← Matrix.mul_assoc, ha']
  have e2 : (a⁻¹)ᴴ * Hpk k r = Hpk k r * a := by
    calc (a⁻¹)ᴴ * Hpk k r = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) := by rw [ha']
      _ = (a * a⁻¹)ᴴ * Hpk k r * a := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Hpk k r * a := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold inLie at *
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = aᴴ * Xᴴ * ((a⁻¹)ᴴ * Hpk k r) + Hpk k r * a⁻¹ * X * a := by
        simp only [Matrix.mul_assoc]
    _ = aᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * a := by
        rw [e2, ← e1]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX, Matrix.mul_zero, Matrix.zero_mul]
end Formalism.FourierDecayAlt.P.B4
