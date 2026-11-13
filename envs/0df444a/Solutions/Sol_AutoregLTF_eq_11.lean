-- Prove2me | solution 1 for AutoregLTF.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:59.149208+00:00
-- url     : https://prove2.me/submissions/28ce937c-02af-472a-9f8d-9ec84f423c47

import Mathlib
import Definitions.Def_AutoregLTF_state

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Lemma1
open AutoregLTF

lemma ptr_eq (m : ℕ) (θ : ℕ → ℤ) (i : ℕ) :
    ∀ t j : ℕ, 1 ≤ j → (state m θ i t).ptr j = decide (t + j = m + 1) := by
  intro t
  induction t with
  | zero => intro j hj; simp [state, init]
  | succ t ih =>
    intro j hj
    show (if j ≤ m then (state m θ i t).ptr (j + 1) else false) = _
    by_cases h : j ≤ m
    · rw [if_pos h, ih (j + 1) (by omega)]
      simp only [decide_eq_decide]; omega
    · rw [if_neg h]
      have : ¬ (t + 1 + j = m + 1) := by omega
      simp [this]

end AutoregLTF.Dev.Lemma1

namespace AutoregLTF
open AutoregLTF.Dev.Lemma1 in
theorem chk_eq_11 (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) (i : ℕ) (hi : i ∈ Finset.Icc 1 m)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (m + 1)) (t : ℕ) :
    (state m (enc m lab) i t).ptr j = decide ((t : ℤ) = (m : ℤ) + 1 - j) := by
  rw [Finset.mem_Icc] at hj
  rw [ptr_eq _ _ _ t j (by omega)]
  simp only [decide_eq_decide]; omega

end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_eq_11 := @AutoregLTF.chk_eq_11
