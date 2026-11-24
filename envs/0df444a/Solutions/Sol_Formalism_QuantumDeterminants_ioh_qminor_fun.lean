-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_qminor_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:49.215929+00:00
-- url     : https://prove2.me/submissions/b3fd8191-81f3-4ba8-84ca-9229918e151a

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_PQ
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor

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
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) {t : ℕ} (α β : Fin t → Fin n) (u : ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ → E) :
    (fun y => qminorOp (EabH H) α β u G (Q * y * P)) =
      qminorOp (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) α β u (fun y => G (Q * y * P)) := by
  funext y
  rw [ioh_qminor ε H P Q hQP hPQ hH, ioh_PQ P Q y hPQ]
end Formalism.QuantumDeterminants
