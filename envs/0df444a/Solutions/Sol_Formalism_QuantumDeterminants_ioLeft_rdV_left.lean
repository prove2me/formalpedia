-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioLeft_rdV_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:52:09.245566+00:00
-- url     : https://prove2.me/submissions/e7c87f52-92d1-4c14-b0d7-9430d8faca61

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft

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
    (X h : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    RdV X (fun x => f (h * x)) = fun x => RdV X f (h * x) := by
  funext g
  simp only [RdV, mul_assoc]
end Formalism.QuantumDeterminants
