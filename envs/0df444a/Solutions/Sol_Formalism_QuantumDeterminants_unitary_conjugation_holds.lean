-- Prove2me | solution 1 for Formalism.QuantumDeterminants.unitary_conjugation_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:58.263966+00:00
-- url     : https://prove2.me/submissions/6612f38d-bf24-4fbf-91fe-e2cc35baf9e4

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution : UHConj := by
  intro m ε H P hP hH g
  subst hH
  show gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g = Pᴴ * Formalism.REAL.Jm ε * P ↔
    (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have h3 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have h4 : Pᴴ * (P⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  constructor
  · intro h
    calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
        = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [h]
      _ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
  · intro h
    calc gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g
        = (Pᴴ * (P⁻¹)ᴴ) * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * (P⁻¹ * P) := by
          rw [h4, h2, Matrix.one_mul, Matrix.mul_one]
      _ = Pᴴ * ((P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * Formalism.REAL.Jm ε * P := by rw [h]
end Formalism.QuantumDeterminants
