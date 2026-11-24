-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioLeft_eabV_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:11:04.7378+00:00
-- url     : https://prove2.me/submissions/d1f0fdd5-48ec-41e2-bc46-95ecae24796d

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
    (ε : Fin n → Bool) (a b : Fin n) (h : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    EabV ε a b (fun x => f (h * x)) = fun x => EabV ε a b f (h * x) := by
  funext g
  simp only [EabV, EcV, ioLeft_rdV_left]
end Formalism.QuantumDeterminants
