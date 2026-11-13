-- Prove2me | solution 1 for AutoregLTF.theorem_1_counting
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:59.151191+00:00
-- url     : https://prove2.me/submissions/e3608357-4eea-4fc3-9435-d055de321bb2

import Mathlib
import Definitions.Def_AutoregLTF_block

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Counting

lemma key (d : ℕ) (hd : 1 ≤ d) (hm : 2 ≤ max 1 ((d - 1) / 378 - 2)) :
    378 * (max 1 ((d - 1) / 378 - 2) + 2) ≤ d - 1 := by
  omega

lemma ub (d : ℕ) (hd : 1 ≤ d) : d ≤ 378 * (max 1 ((d - 1) / 378 - 2) + 3) := by
  omega

end AutoregLTF.Dev.Counting
namespace AutoregLTF
open AutoregLTF.Dev.Counting in
theorem chk_theorem_1_counting (d T : ℕ) (hd : 1 ≤ d) (hT : d ^ 2 ≤ T) :
    let m := max 1 ((d - 1) / 378 - 2)
    (2 ≤ m → p m ≤ d - 1 ∧ (m + 3) * p m < p m ^ 2 ∧ p m ^ 2 < d ^ 2) ∧
    (m = 1 → d ≤ 1512) ∧
    (2 ≤ m → d ≤ 378 * (m + 3) ∧ 378 * (m + 3) ≤ 1512 * m) ∧
    d ^ 2 ≤ 1512 ^ 2 * m ^ 2 := by
  intro m
  have hub : d ≤ 378 * (m + 3) := ub d hd
  refine ⟨fun h2 => ?_, fun h1 => ?_, fun h2 => ⟨hub, by omega⟩, ?_⟩
  · have hp : p m ≤ d - 1 := by unfold p; exact key d hd h2
    refine ⟨hp, ?_, ?_⟩
    · unfold p; nlinarith
    · have : p m < d := by omega
      exact Nat.pow_lt_pow_left this (by norm_num)
  · have : d ≤ 378 * (m + 3) := hub
    omega
  · have h1 : m ≥ 1 := le_max_left _ _
    have : d ≤ 1512 * m := by
      by_cases h2 : 2 ≤ m
      · omega
      · omega
    calc d ^ 2 ≤ (1512 * m) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 1512 ^ 2 * m ^ 2 := by ring
end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_theorem_1_counting := @AutoregLTF.chk_theorem_1_counting
