-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.finite_of_finset_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:33:00.124034+00:00
-- url     : https://prove2.me/submissions/324bdea5-f360-4b7b-a71d-576bcadfc927

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {α : Type*} (T : Set α) (C : ℝ)
    (h : ∀ S : Finset α, (↑S ⊆ T) → (S.card : ℝ) ≤ C) : T.Finite ∧ (T.ncard : ℝ) ≤ C := by
  have hfin : T.Finite := by
    by_contra hinf
    obtain ⟨S, hS, hc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈C⌉₊ + 1)
    have := h S hS
    rw [hc] at this
    have h2 := Nat.le_ceil C
    push_cast at this
    linarith
  refine ⟨hfin, ?_⟩
  have := h hfin.toFinset (by simp)
  rwa [← Set.ncard_eq_toFinset_card _ hfin] at this
end Formalism.HermitianLatticeCounting.P
