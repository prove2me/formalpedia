-- Prove2me | solution 1 for BCFGJPSSV26.Stable.BiGraph.exists_swap_families
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:00:55.857254+00:00
-- url     : https://prove2.me/submissions/5ef7cf0d-b83b-43b2-a0ff-b6458120b3e7

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForestAux
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForest
import all Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForest

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace BiGraph

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (G : BiGraph α β)

end BiGraph

namespace BiGraph

open StarForestAux

variable {α β : Type*}

variable {G : BiGraph α β}

end BiGraph

namespace BiGraph

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (G : BiGraph α β)

/-- **Swap families** ([BCFGJPSSV26b, Lemma 6.2]): good families such that, on average over them,
every left vertex of degree at most `1` is in at most `1 + 8/N` swaps. -/
theorem exists_swap_families {N : ℕ} (hN : 200 ≤ N) (hG : G.IsStarLike)
    (hc : G.R.card ≤ G.L.card) :
    ∃ (b : ℕ) (_ : 0 < b) (𝒮 : Fin b → List (Swap α β)), (∀ r, G.Good N (𝒮 r)) ∧
      ∀ u ∈ G.L, G.degL u ≤ 1 →
        (∑ r, ((𝒮 r).countP fun σ ↦ u ∈ σ.Ls : ℝ)) ≤ (1 + 8 / N) * b := by
  by_cases h : G.LF.card < 12 * N
  · exact small_case hG hc hN h
  · exact large_case hG hc hN (by omega)

end BiGraph

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.BiGraph.exists_swap_families := @BCFGJPSSV26.Stable.BiGraph.exists_swap_families
