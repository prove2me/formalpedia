-- Prove2me | solution 1 for Formalism.MainNotions.S.Gauge.Cd.trace_mul_conjTranspose_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:23.148696+00:00
-- url     : https://prove2.me/submissions/15bde489-d15b-42b3-adb2-5b0f25adb9ec

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_TraceMulConjTransposeReal
import Theorems.Thm_Formalism_MainNotions_S_Gauge_Cd_jpq_sq

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
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Gauge Formalism.MainNotions.S.Gauge.Cd
variable {P Q : ℕ}
local notation "ι" => Fin P ⊕ Fin Q
namespace Formalism.MainNotions.S.Gauge.Cd
theorem _root_.solution {a b : Matrix ι ι ℂ} (ha : a ∈ Formalism.BasicNotions.lieU P Q) (hb : b ∈ Formalism.BasicNotions.lieU P Q) :
    star (Matrix.trace (a * bᴴ)) = Matrix.trace (a * bᴴ) := by
  have hb' : bᴴ = -(Formalism.UG.Jpq P Q * b * Formalism.UG.Jpq P Q) := by
    have h : bᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * b = 0 := hb
    have h2 : bᴴ * Formalism.UG.Jpq P Q = -(Formalism.UG.Jpq P Q * b) := eq_neg_of_add_eq_zero_left h
    calc bᴴ = bᴴ * Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q := by rw [Matrix.mul_assoc, jpq_sq, Matrix.mul_one]
      _ = -(Formalism.UG.Jpq P Q * b * Formalism.UG.Jpq P Q) := by rw [h2, Matrix.neg_mul]
  have ha' : aᴴ = -(Formalism.UG.Jpq P Q * a * Formalism.UG.Jpq P Q) := by
    have h : aᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * a = 0 := ha
    have h2 : aᴴ * Formalism.UG.Jpq P Q = -(Formalism.UG.Jpq P Q * a) := eq_neg_of_add_eq_zero_left h
    calc aᴴ = aᴴ * Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q := by rw [Matrix.mul_assoc, jpq_sq, Matrix.mul_one]
      _ = -(Formalism.UG.Jpq P Q * a * Formalism.UG.Jpq P Q) := by rw [h2, Matrix.neg_mul]
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ha', hb']
  simp only [Matrix.mul_neg, Matrix.trace_neg]
  congr 1
  calc (b * (Formalism.UG.Jpq P Q * a * Formalism.UG.Jpq P Q)).trace
      = ((b * Formalism.UG.Jpq P Q) * (a * Formalism.UG.Jpq P Q)).trace := by simp only [Matrix.mul_assoc]
    _ = ((a * Formalism.UG.Jpq P Q) * (b * Formalism.UG.Jpq P Q)).trace := Matrix.trace_mul_comm _ _
    _ = (a * (Formalism.UG.Jpq P Q * b * Formalism.UG.Jpq P Q)).trace := by simp only [Matrix.mul_assoc]
end Formalism.MainNotions.S.Gauge.Cd
