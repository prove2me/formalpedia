-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_EabH_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:52.38779+00:00
-- url     : https://prove2.me/submissions/3495b98d-a2bf-4a10-85e0-70611da0f29b

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_rdV
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_hpart1
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_hpart2

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
    (hH : H = Pᴴ * Jm ε * P) (x : Matrix (Fin n) (Fin n) ℂ) :
    EabH H a b f x = EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) (P * x * Q) := by
  unfold EabH EcV
  rw [ioh_rdV P Q _ x f hQP hPQ, ioh_rdV P Q (hpart2 H _) x f hQP hPQ,
    ioh_hpart1 ε H P Q _ hQP hPQ hH, ioh_hpart2 ε H P Q _ hQP hPQ hH]
end Formalism.QuantumDeterminants
