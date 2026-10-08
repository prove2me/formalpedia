-- Prove2me | solution 1 for ErschlerZheng.isCofinal_and_printed_gray_ones_infinite_prepend_false_oneRay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.921977+00:00
-- url     : https://prove2.me/submissions/f1c50845-7337-4ac4-b845-7ef6e70240f7

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Rays: prefixes, shifts, and the action of sections
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace RayBasic

open GrigBasic

end RayBasic

end ErschlerZheng
end

section
/-!
# The Gray code on finite words, and how the generators move it

For a word `w` of length `N`, `grayList w < 2^N`. The generator `a` changes it by `+1` when `w`
has an even number of zeros and by `-1` otherwise; a generator `γ_ω` either fixes `w` or changes
it by `-1` (even) or `+1` (odd). From every word there is a generator step up (below the top
value `2^N - 1`) and down (above `0`) whose section at `w` is trivial.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace GrayDev

open GrigBasic

end GrayDev

end ErschlerZheng
end

section
/-!
# The Schreier graph of `1^∞` through the Gray code

Rays that are all ones from position `N` on are `prepend w 1^∞` with `|w| = N`; their Gray code
is `grayList w`. A generator moves the Gray code of such a ray by at most one, and from `w` to
`w'` of the same length there is a path of `|ḡ(w) - ḡ(w')|` generators with trivial sections at
the intermediate words, so it carries any tail along unchanged.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace SchreierDev

open GrigBasic RayBasic GrayDev

/-! ### Generators on rays that are eventually all ones -/

end SchreierDev

end ErschlerZheng
end

section
/-!
# A9: `d_𝒮(x, y) = |x̄ - ȳ|` for cofinal rays (p. 34); A9F: the printed prefix sums fail
-/

open scoped RightActions

namespace ErschlerZheng

end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
theorem solution :
    IsCofinal (prepend [false] oneRay) ∧
      {i : ℕ | (∑ k ∈ Finset.range (i + 1), (1 - (prepend [false] oneRay k).toNat)) % 2 = 1}.Infinite := by
  constructor
  · unfold ErschlerZheng.IsCofinal
    rw [Filter.eventually_atTop]
    exact ⟨1, fun k hk => by simp [prepend, oneRay, show ¬ k < 1 by omega]⟩
  · have : ∀ i : ℕ, (∑ k ∈ Finset.range (i + 1), (1 - (prepend [false] oneRay k).toNat)) = 1 := by
      intro i
      rw [Finset.sum_range_succ']
      have : ∀ k ∈ Finset.range i, (1 - (prepend [false] oneRay (k + 1)).toNat) = 0 := by
        intro k _
        simp [prepend, oneRay]
      rw [Finset.sum_eq_zero this]
      simp [prepend]
    have hs : {i : ℕ | (∑ k ∈ Finset.range (i + 1), (1 - (prepend [false] oneRay k).toNat)) % 2 = 1}
        = Set.univ := by
      ext i; simp [this i]
    rw [hs]
    exact Set.infinite_univ
end
