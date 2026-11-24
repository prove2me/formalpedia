-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_qminor_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:49:45.463346+00:00
-- url     : https://prove2.me/submissions/9a4dec8a-3069-4e47-a66a-6ea8a92cb6f9

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_foldr_rep
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor_apply
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_sum


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
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants
theorem _root_.solution {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)} (hR : IOHRepr Eop Ealg)
    {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep (qminorOp Eop a b u F) (qminor Ealg a b u x).1 := by
  intro g hg
  rw [ioh_qminor_apply]
  have hs := io_rep_sum (fun σ : Equiv.Perm (Fin t) => (((Equiv.Perm.sign σ : ℤ) : ℂ)))
    (fun σ => ioh_foldr_rep hR (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)) h) g hg
  rw [← hs]
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, List.map_ofFn]
  rfl
end Formalism.QuantumDeterminants
