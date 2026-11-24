-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capelli_left_conjugated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:34:22.631986+00:00
-- url     : https://prove2.me/submissions/106b4567-1502-4616-b26f-5a122aefdce4

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Theorems.Thm_Formalism_QuantumDeterminants_ioLeft_eabH_left
import Theorems.Thm_Formalism_QuantumDeterminants_ioLeft_foldr_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.REAL
noncomputable section
namespace Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private lemma qminorOp_comm_left_mul_of_Eop_comm_left_mul {n t : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (h : Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E),
      Eop a b (fun x => f (h * x)) = fun x => Eop a b f (h * x))
    (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    qminorOp Eop a b u (fun x => f (h * x)) = fun x => qminorOp Eop a b u f (h * x) := by
  funext x
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [ioLeft_foldr_left h _ ?_ f]
  intro T hT f'
  simp only [List.mem_ofFn, Set.mem_range] at hT
  obtain ⟨k, rfl⟩ := hT
  funext g
  simp only [Top, hE]
end Formalism.QuantumDeterminants
end
end

set_option autoImplicit false
open Matrix Formalism.REAL
noncomputable section
open Formalism Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution : CapLeftH := by
  intro n E _ _ H f u h
  exact qminorOp_comm_left_mul_of_Eop_comm_left_mul (EabH H) h (fun a b f => ioLeft_eabH_left H a b h f) id id u f
end Formalism.QuantumDeterminants
