-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_exp_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:05:15.124899+00:00
-- url     : https://prove2.me/submissions/992d5911-7683-44c5-9e21-698f919d9644

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
theorem _root_.solution (P Q X : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (hPQ : P * Q = 1) :
    NormedSpace.exp (P * X * Q) = P * NormedSpace.exp X * Q := by
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨P, Q, hPQ, hQP⟩
  exact Matrix.exp_units_conj U X
end Formalism.QuantumDeterminants
