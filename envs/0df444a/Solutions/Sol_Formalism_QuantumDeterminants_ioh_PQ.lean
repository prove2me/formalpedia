-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_PQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:39:27.603884+00:00
-- url     : https://prove2.me/submissions/505444ce-9e75-4ecc-b939-a72bed14c646

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
theorem _root_.solution (P Q y : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) : P * (Q * y * P) * Q = y := by
  have : P * (Q * y * P) * Q = (P * Q) * y * (P * Q) := by simp only [Matrix.mul_assoc]
  rw [this, hPQ]; simp
end Formalism.QuantumDeterminants
