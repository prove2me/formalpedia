-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_EabH_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:26:12.072456+00:00
-- url     : https://prove2.me/submissions/a1248faa-ea44-48ea-a3fe-d44b0bd30e04

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_EabH_eq

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
theorem _root_.solution (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) :
    (fun y => EabH H a b f (Q * y * P)) =
      EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) := by
  funext y
  rw [ioh_EabH_eq ε H P Q f a b hQP hPQ hH]
  congr 1
  have : P * (Q * y * P) * Q = (P * Q) * y * (P * Q) := by simp only [Matrix.mul_assoc]
  rw [this, hPQ]; simp
end Formalism.QuantumDeterminants
