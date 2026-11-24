-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:27.54572+00:00
-- url     : https://prove2.me/submissions/8a69cf67-9631-4a9e-91fa-a0b84867846f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_foldr

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
    (G : Matrix (Fin n) (Fin n) ℂ → E) (x : Matrix (Fin n) (Fin n) ℂ) :
    qminorOp (EabH H) α β u G x =
      qminorOp (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) α β u (fun y => G (Q * y * P))
        (P * x * Q) := by
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 : ∀ (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)),
      (List.ofFn fun k : Fin t => Top Eop (u - ((k : ℕ) : ℂ)) (α (σ k)) (β k)) =
        (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), α (σ k), β k)).map
          fun p => Top Eop p.1 p.2.1 p.2.2 := by
    intro Eop; rw [List.map_ofFn]; rfl
  rw [e1, e1, ioh_foldr ε H P Q hQP hPQ hH]
end Formalism.QuantumDeterminants
