-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioLeft_foldr_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:52:09.249689+00:00
-- url     : https://prove2.me/submissions/5356a5fd-14c5-41d7-b25e-38a8394358ec

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
    (h : Matrix (Fin n) (Fin n) ℂ)
    (L : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)))
    (hL : ∀ T ∈ L, ∀ f : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f (h * x)) = fun x => T f (h * x))
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    L.foldr (fun T g => T g) (fun x => f (h * x)) = fun x => L.foldr (fun T g => T g) f (h * x) := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hL T' (List.mem_cons.2 (Or.inr hT')))]
    exact hL T (List.mem_cons.2 (Or.inl rfl)) _
end Formalism.QuantumDeterminants
