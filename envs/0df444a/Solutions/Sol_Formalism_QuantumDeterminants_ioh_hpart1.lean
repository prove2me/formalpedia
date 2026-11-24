-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_hpart1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:47:43.351884+00:00
-- url     : https://prove2.me/submissions/feaa9478-0877-42b5-b090-344498e66fc1

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_conj_part

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
theorem _root_.solution (ε : Fin n → Bool) (H P Q Z : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) :
    P * hpart1 H Z * Q = cpart1 ε (P * Z * Q) := by
  have h := ioh_conj_part ε H P Q Z hQP hPQ hH
  unfold hpart1 cpart1
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, ← h]
end Formalism.QuantumDeterminants
