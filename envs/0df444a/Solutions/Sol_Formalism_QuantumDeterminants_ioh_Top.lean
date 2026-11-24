-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_Top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:26:10.034669+00:00
-- url     : https://prove2.me/submissions/98e4a988-cdf4-4a03-8aea-b2e14855b69e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_EabH_eq
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_PQ

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
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) (u : ℂ) (a b : Fin n)
    (R : Matrix (Fin n) (Fin n) ℂ → E) :
    Top (EabH H) u a b (fun x => R (P * x * Q)) =
      fun x => Top (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) u a b R (P * x * Q) := by
  funext x
  unfold Top
  rw [ioh_EabH_eq ε H P Q _ a b hQP hPQ hH x]
  have : (fun y => (fun x => R (P * x * Q)) (Q * y * P)) = R := by
    funext y; simp only [ioh_PQ P Q y hPQ]
  rw [this]
end Formalism.QuantumDeterminants
