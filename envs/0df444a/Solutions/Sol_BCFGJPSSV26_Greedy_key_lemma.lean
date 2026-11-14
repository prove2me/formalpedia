-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.key_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:56:16.657204+00:00
-- url     : https://prove2.me/submissions/d373c303-96ee-46bb-980d-383d58dfcc8f

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Space
import Mathlib.Data.Finset.Max
public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
import all Definitions.Def_BCFGJPSSV26_Greedy_Openable

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

section Mono

variable {θ T T' f η : ℚ} {D D' : Fin n → ℚ} {i i₀ : Fin m}

end Mono

/-- **Key lemma**: for `T ∈ [θ, (1 + ε²) θ]`, the overbidding of `i₀` under the bids for `i` is
at most `Ψ = ∑_j β(min (T, (1 - δ) D j), d(j, i₀))`, which is at most what `i₀` collects in (iii)
with the same `T`. -/
theorem key_lemma (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {θ T : ℚ} (hθ : 0 < θ) (hT : θ ≤ T)
    (hT' : T ≤ P.θplus θ) (D : Fin n → ℚ) (i i₀ : Fin m) :
    lhs4 P d θ D i T i₀ ≤ ∑ j, bid (min T ((1 - P.δ) * D j)) (d j i₀) ∧
      ∑ j, bid (min T ((1 - P.δ) * D j)) (d j i₀) ≤ lhs3 P d θ D i₀ T :=
  ⟨sum_le_sum fun j _ ↦ bid_mono_left (le_min (mT_le_T hT D i j) (mT_le_D θ D i T j)) _,
    sum_le_sum fun j _ ↦ bid_min_le_bid_mT hP (hd j i₀) hθ hT'⟩

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.key_lemma := @BCFGJPSSV26.Greedy.key_lemma
