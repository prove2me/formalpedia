-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.trace_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:57:54.667213+00:00
-- url     : https://prove2.me/submissions/bd846346-900d-4228-9b29-96281cd71f56

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E) (a b : Fin N) :
    (∑ c, E c c) * E a b = E a b * ∑ c, E c c := by
  rw [Finset.sum_mul, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun c _ => hE c c a b), Finset.sum_sub_distrib]
  simp
end Formalism.FourierDecayAlt.P.ClosureOperators
