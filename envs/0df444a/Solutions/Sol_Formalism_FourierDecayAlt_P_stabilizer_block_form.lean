-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stabilizer_block_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:18.880654+00:00
-- url     : https://prove2.me/submissions/441ddf33-7c3a-422f-8d17-f4f8b9613ae7

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.StabBlock := by
  intro p s h lh uh gs ls us a b hh hgs
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add]
  rw [Matrix.fromBlocks_inj]
  simp only [Matrix.mul_assoc]
  constructor
  · rintro ⟨e11, e12, e21, e22⟩
    have hb : h * b = 0 := by
      calc h * b = (lh * (h * uh)) * b := by rw [e11]
        _ = lh * (h * (uh * b)) := by simp only [Matrix.mul_assoc]
        _ = 0 := e12
    have hb0 : b = 0 := by
      calc b = h⁻¹ * (h * b) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hh, Matrix.one_mul]
        _ = 0 := by rw [hb, Matrix.mul_zero]
    have ha : a * h = 0 := by
      calc a * h = a * (lh * (h * uh)) := by rw [e11]
        _ = 0 := e21
    have ha0 : a = 0 := by
      calc a = (a * h) * h⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one]
        _ = 0 := by rw [ha, Matrix.zero_mul]
    subst hb0
    subst ha0
    refine ⟨rfl, rfl, e11, ?_⟩
    simpa using e22
  · rintro ⟨rfl, rfl, e1, e2⟩
    simp [e1, e2]
end Formalism.FourierDecayAlt.P
