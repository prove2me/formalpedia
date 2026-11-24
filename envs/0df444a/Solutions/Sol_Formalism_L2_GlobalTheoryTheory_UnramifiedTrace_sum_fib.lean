-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.sum_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:29.81922+00:00
-- url     : https://prove2.me/submissions/743f18de-2c76-487b-960d-ac4cab17eb42

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_UnramifiedTrace_SumFib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
theorem _root_.solution {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P] (π : P → X) (V : P → ℂ) (w : X → ℂ)
    (hV : ∀ p, V p = w (π p)) :
    ∑ p, V p = ∑ x, ((Finset.univ.filter (fun p => π p = x)).card : ℂ) * w x := by
  have key : ∀ x, ∑ p ∈ Finset.univ.filter (fun p => π p = x), w (π p) =
      ((Finset.univ.filter (fun p => π p = x)).card : ℂ) * w x := by
    intro x
    rw [Finset.sum_congr rfl (g := fun _ => w x) (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
      Finset.sum_const, nsmul_eq_mul]
  simp_rw [hV]
  rw [← Finset.sum_fiberwise Finset.univ π (fun p => w (π p))]
  exact Finset.sum_congr rfl (fun x _ => key x)
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
