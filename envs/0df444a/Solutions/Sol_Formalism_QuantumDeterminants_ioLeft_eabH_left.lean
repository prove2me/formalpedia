-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioLeft_eabH_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:10:56.177889+00:00
-- url     : https://prove2.me/submissions/9dc19ea4-7dea-4c4a-a42e-1986c4e1d5ab

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Theorems.Thm_Formalism_QuantumDeterminants_ioLeft_rdV_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL
noncomputable section
open Formalism Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (h : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    EabH H a b (fun x => f (h * x)) = fun x => EabH H a b f (h * x) := by
  funext g
  simp only [EabH, ioLeft_rdV_left]
end Formalism.QuantumDeterminants
