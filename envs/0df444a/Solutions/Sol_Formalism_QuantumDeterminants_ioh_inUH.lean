-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_inUH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:42:31.901822+00:00
-- url     : https://prove2.me/submissions/b046b30e-8cf3-4a2c-a1ed-450df5e61f55

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated

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
theorem _root_.solution (ε : Fin n → Bool) (H P Q x : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (hx : inUJ ε x) : inUH H (Q * x * P) := by
  unfold inUJ at hx
  unfold inUH
  rw [hH]
  have e : (Q * x * P)ᴴ * (Pᴴ * Jm ε * P) * (Q * x * P)
      = Pᴴ * (xᴴ * ((P * Q)ᴴ * Jm ε * (P * Q)) * x) * P := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hPQ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hx]
end Formalism.QuantumDeterminants
