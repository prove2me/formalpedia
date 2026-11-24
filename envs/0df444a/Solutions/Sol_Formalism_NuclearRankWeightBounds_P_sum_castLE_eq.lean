-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.sum_castLE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:26.711731+00:00
-- url     : https://prove2.me/submissions/4a7aa181-f0b6-4984-9ebe-336bd31a8067

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DetMulDiagonalMulEqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Polynomial Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution {N i : ℕ} (hi : i ≤ N) {β : Type*} [AddCommMonoid β] (f : Fin N → β) :
    ∑ a : Fin i, f (Fin.castLE hi a) = ∑ a ∈ univ.filter (fun a : Fin N => a.val < i), f a := by
  refine Finset.sum_bij' (fun a _ => Fin.castLE hi a) (fun a ha => ⟨a.val, (mem_filter.mp ha).2⟩)
    ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp_all
end Formalism.NuclearRankWeightBounds.P
