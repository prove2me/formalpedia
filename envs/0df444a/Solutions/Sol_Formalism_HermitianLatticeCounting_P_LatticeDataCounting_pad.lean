-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.pad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:28.52168+00:00
-- url     : https://prove2.me/submissions/06d6ada5-1725-481a-b791-a2a64d256336

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution {R X : Type*} [Semiring R] [AddCommMonoid X] [Module R X] {n j : ℕ} (hnj : n ≤ j) (s : Fin n → X)
    (B : Submodule R X) (hs : ∀ i, s i ∈ B) :
    ∃ t : Fin j → X, (∀ i, t i ∈ B) ∧
      Submodule.span R (Set.range s) ≤ Submodule.span R (Set.range t) := by
  refine ⟨fun i => if h : (i : ℕ) < n then s ⟨i, h⟩ else 0, fun i => ?_, ?_⟩
  · by_cases h : (i : ℕ) < n
    · simp only [h, dif_pos]; exact hs _
    · simp only [h, dif_neg, not_false_eq_true]; exact B.zero_mem
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, lt_of_lt_of_le i.2 hnj⟩, by simp⟩
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
