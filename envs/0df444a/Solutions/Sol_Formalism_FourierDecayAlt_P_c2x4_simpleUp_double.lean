-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x4_simpleUp_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:45:15.988312+00:00
-- url     : https://prove2.me/submissions/dcf652af-9e7b-4174-a280-b2388dc1bf89

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
theorem _root_.solution {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) :
    C2.simpleUp u = ∑ a : Fin m, ∑ b : Fin m, if b.val = a.val + 1 then u a b else 0 := by
  unfold C2.simpleUp
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val + 1, h⟩]
    · simp
    · intro p _ hp; rw [if_neg]; intro e; exact hp (Fin.ext e)
    · simp
  · apply (Finset.sum_eq_zero (fun p _ => ?_)).symm
    rw [if_neg]; intro e; have := p.isLt; omega
end Formalism.FourierDecayAlt.P
