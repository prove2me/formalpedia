-- Prove2me | solution 1 for Formalism.QuantumDeterminants.io_qminor_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:27:51.659341+00:00
-- url     : https://prove2.me/submissions/1ba5f212-f187-4082-aaaf-e72b1012db80

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_sum
import Theorems.Thm_Formalism_QuantumDeterminants_io_foldr_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_qminor_apply

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
theorem _root_.solution {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep (qminorOp (EabV ε) a b u F) (qminor (ioE ε E) a b u x).1 := by
  intro g hg
  rw [io_qminor_apply]
  refine Eq.trans ?_ (io_rep_sum (fun σ : Equiv.Perm (Fin t) => ((Equiv.Perm.sign σ : ℤ) : ℂ))
    (fun σ => io_foldr_rep (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)) h) g hg)
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, List.map_ofFn, Function.comp_def]
end Formalism.QuantumDeterminants
