-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_hpart2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:47:46.342729+00:00
-- url     : https://prove2.me/submissions/5be6ac25-79ff-4f32-96d6-7e6ea409a5d1

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
    P * hpart2 H Z * Q = cpart2 ε (P * Z * Q) := by
  have h := ioh_conj_part ε H P Q Z hQP hPQ hH
  unfold hpart2 cpart2
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, ← h]
end Formalism.QuantumDeterminants
