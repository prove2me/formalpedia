-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_Hinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:05:13.571001+00:00
-- url     : https://prove2.me/submissions/207b761f-1d11-4cb6-ac99-b823389333a4

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_REAL_Jm_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants
theorem _root_.solution (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) : H⁻¹ = Q * Jm ε * Qᴴ := by
  apply Matrix.inv_eq_right_inv
  have hc : Pᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one]
  calc H * (Q * Jm ε * Qᴴ) = Pᴴ * (Jm ε * ((P * Q) * (Jm ε * Qᴴ))) := by
        rw [hH]; simp only [Matrix.mul_assoc]
    _ = Pᴴ * Qᴴ := by
        rw [hPQ, Matrix.one_mul, ← Matrix.mul_assoc (Jm ε), Jm_mul_self, Matrix.one_mul]
    _ = 1 := hc
end Formalism.QuantumDeterminants
