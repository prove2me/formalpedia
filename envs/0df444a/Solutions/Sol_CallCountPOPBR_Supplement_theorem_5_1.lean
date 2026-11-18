-- Prove2me | solution 1 for CallCountPOPBR.Supplement.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:21:42.335803+00:00
-- url     : https://prove2.me/submissions/e67dcaf5-d714-4aa8-a42d-8316ce5013ce

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_DecSpec

set_option autoImplicit false

namespace CC51Aux
open CallCountPOPBR.Supplement

lemma count_eq (s : DecSpec) (n : ℕ) :
    s.count n = 1 + ((s.calls n).attach.map (fun k => s.count k.1)).sum := by
  rw [DecSpec.count]

lemma calls_zero (s : DecSpec) : s.calls 0 = [] := by
  rcases h : s.calls 0 with _ | ⟨k, l⟩
  · rfl
  · exact absurd (s.dec 0 k (by rw [h]; exact List.mem_cons_self)) (Nat.not_lt_zero k)

lemma count_zero (s : DecSpec) : s.count 0 = 1 := by
  rw [count_eq, calls_zero]; rfl

lemma one_le_count (s : DecSpec) (n : ℕ) : 1 ≤ s.count n := by
  rw [count_eq]; omega

def mkSpec (c : ℕ → ℤ) : DecSpec where
  calls n := if n = 0 then [] else List.replicate ((c n).toNat - 1) 0
  dec n k hk := by
    by_cases hn : n = 0
    · simp [hn] at hk
    · simp only [hn, if_false] at hk
      rw [(List.mem_replicate.mp hk).2]; omega

end CC51Aux

open CallCountPOPBR.Supplement in
theorem solution (c : ℕ → ℤ) :
    (∃ s : DecSpec, ∀ n, c n = (s.count n : ℤ)) ↔ (c 0 = 1 ∧ ∀ n, 1 ≤ c n) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨by rw [hs, CC51Aux.count_zero]; rfl, fun n => ?_⟩
    rw [hs]; exact_mod_cast CC51Aux.one_le_count s n
  · rintro ⟨h0, h1⟩
    refine ⟨CC51Aux.mkSpec c, fun n => ?_⟩
    by_cases hn : n = 0
    · subst hn; rw [h0, CC51Aux.count_zero]; rfl
    · rw [CC51Aux.count_eq]
      have hcalls : (CC51Aux.mkSpec c).calls n = List.replicate ((c n).toNat - 1) 0 := by
        simp [CC51Aux.mkSpec, hn]
      have hsum : (((CC51Aux.mkSpec c).calls n).attach.map
          (fun k => (CC51Aux.mkSpec c).count k.1)).sum = (c n).toNat - 1 := by
        have : ∀ k ∈ ((CC51Aux.mkSpec c).calls n).attach.map
            (fun k => (CC51Aux.mkSpec c).count k.1), k = 1 := by
          intro k hk
          rw [List.mem_map] at hk
          obtain ⟨⟨j, hj⟩, _, rfl⟩ := hk
          have hj' : j ∈ List.replicate ((c n).toNat - 1) 0 := hcalls ▸ hj
          show (CC51Aux.mkSpec c).count j = 1
          rw [(List.mem_replicate.mp hj').2, CC51Aux.count_zero]
        rw [List.eq_replicate_of_mem this, List.sum_replicate, List.length_map,
          List.length_attach, hcalls, List.length_replicate, smul_eq_mul, mul_one]
      rw [hsum]
      have := h1 n
      push_cast
      omega
