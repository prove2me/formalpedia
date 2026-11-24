-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x4_simpleLow_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:45:25.173587+00:00
-- url     : https://prove2.me/submissions/39f11a32-5047-48c8-a079-7cd0d1d16bbd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {m : ℕ} (l : Matrix (Fin m) (Fin m) ℂ) :
    C2.simpleLow l = ∑ p : Fin m, ∑ q : Fin m, if p.val = q.val + 1 then l p q else 0 := by
  unfold C2.simpleLow
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨q.val + 1, h⟩]
    · simp
    · intro p _ hp; rw [if_neg]; intro e; exact hp (Fin.ext e)
    · simp
  · apply (Finset.sum_eq_zero (fun p _ => ?_)).symm
    rw [if_neg]; intro e; have := p.isLt; omega
end Formalism.FourierDecayAlt.P
