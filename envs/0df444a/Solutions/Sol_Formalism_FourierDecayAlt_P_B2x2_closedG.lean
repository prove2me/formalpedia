-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.closedG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:11:47.828008+00:00
-- url     : https://prove2.me/submissions/51f18f10-88f5-4064-9077-2c8752c7017a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_hpk_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution : ClosedG := by
  intro k r
  have hH : IsUnit (Hpk k r).det := hpk_unit k r
  have hdet : ∀ a : Mat k r, aᴴ * Hpk k r * a = Hpk k r → IsUnit a.det := by
    intro a ha
    have h2 := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
    refine isUnit_iff_ne_zero.2 fun h0 => hH.ne_zero ?_
    rw [h0, mul_zero] at h2
    exact h2.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  · intro a ha b hb
    change aᴴ * Hpk k r * a = Hpk k r at ha
    change bᴴ * Hpk k r * b = Hpk k r at hb
    show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha, hb]
  · intro a ha
    change aᴴ * Hpk k r * a = Hpk k r at ha
    have hu := hdet a ha
    show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
    calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha]
      _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by
          rw [Matrix.mul_nonsing_inv a hu]
          simp
  · intro a ha
    exact hdet a ha
  · show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
end Formalism.FourierDecayAlt.P.B2x2
