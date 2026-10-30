-- Prove2me | solution 1 for BitcoinFeerateDiagram.evaluateFeeDown_eq_floor
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:16:29.136432+00:00
-- url     : https://prove2.me/submissions/92ded948-96a3-4772-981a-9af878caf6da

import Definitions.Def_BitcoinFeerateDiagram
import Theorems.Thm_BitcoinFeerateDiagram_div_round_down_eq_floor

open BitcoinFeerateDiagram BitcoinReplacement

private theorem add_fee (a b : FeeFrac) : (a + b).fee = a.fee + b.fee := rfl

private theorem add_size (a b : FeeFrac) : (a + b).size = a.size + b.size := rfl

private theorem sub_fee (a b : FeeFrac) : (a - b).fee = a.fee - b.fee := rfl

private theorem sub_size (a b : FeeFrac) : (a - b).size = a.size - b.size := rfl

private theorem zero_fee : (0 : FeeFrac).fee = 0 := rfl

private theorem zero_size : (0 : FeeFrac).size = 0 := rfl

private theorem ff_ext {x y : FeeFrac} (h1 : x.fee = y.fee) (h2 : x.size = y.size) : x = y := by
  cases x; cases y; simp_all

private theorem add_sub_cancel_ff (c a : FeeFrac) : c + a - a = c :=
  ff_ext (by rw [sub_fee, add_fee]; ring) (by rw [sub_size, add_size]; ring)

private theorem ediv_emod_facts (n d : ℤ) (hd : 0 < d) :
    n % d + d * (n / d) = n ∧ 0 ≤ n % d ∧ n % d < d :=
  (Int.ediv_emod_unique hd).1 ⟨rfl, rfl⟩

private theorem floor_div_int (n d : ℤ) (hd : 0 < d) : ⌊(n : ℚ) / d⌋ = n / d := by
  obtain ⟨h1, h2, h3⟩ := ediv_emod_facts n d hd
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  set q := n / d
  set r := n % d
  have hn : (n : ℚ) = r + d * q := by exact_mod_cast h1.symm
  have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast h2
  have hr1 : (r : ℚ) < d := by exact_mod_cast h3
  rw [Int.floor_eq_iff, le_div_iff₀ hd', div_lt_iff₀ hd', hn]
  constructor <;> nlinarith

private theorem ceil_div_int (n d : ℤ) (hd : 0 < d) :
    ⌈(n : ℚ) / d⌉ = n / d + if n % d = 0 then 0 else 1 := by
  obtain ⟨h1, h2, h3⟩ := ediv_emod_facts n d hd
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  set q := n / d
  set r := n % d
  have hn : (n : ℚ) = r + d * q := by exact_mod_cast h1.symm
  have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast h2
  have hr1 : (r : ℚ) < d := by exact_mod_cast h3
  rw [Int.ceil_eq_iff, lt_div_iff₀ hd', div_le_iff₀ hd', hn]
  split_ifs with h0
  · have : (r : ℚ) = 0 := by exact_mod_cast h0
    push_cast
    constructor <;> nlinarith
  · have : (0 : ℚ) < r := by
      have : 0 < r := lt_of_le_of_ne h2 (Ne.symm h0)
      exact_mod_cast this
    push_cast
    constructor <;> nlinarith

private theorem tdiv_tmod_facts (n d : ℤ) (hd : 0 < d) :
    (n.tdiv d = n / d ∧ n.tmod d = n % d) ∨
    (n.tdiv d = n / d + 1 ∧ n.tmod d = n % d - d ∧ n % d ≠ 0) := by
  rw [Int.tdiv_eq_ediv, Int.tmod_eq_emod, Int.sign_eq_one_of_pos hd]
  by_cases hc : 0 ≤ n ∨ d ∣ n
  · left; simp [hc]
  · right
    have hnd : ¬ d ∣ n := fun h => hc (Or.inr h)
    rw [Int.dvd_iff_emod_eq_zero] at hnd
    simp [hc, Int.natAbs_of_nonneg hd.le, hnd]

/-- `EvaluateFeeDown(at_size)` is `⌊fee · at_size / size⌋` (for `size > 0`, `at_size ≥ 0`), on both
the `uint64_t` fast path and the `Mul`/`Div` path. -/
theorem solution (f : FeeFrac) (atSize : ℤ)
    (hs : 0 < f.size) (_ha : 0 ≤ atSize) :
    FeeFrac.evaluateFeeDown f atSize = ⌊((f.fee * atSize : ℤ) : ℚ) / f.size⌋ := by
  simp only [FeeFrac.evaluateFeeDown, FeeFrac.evaluateFee, if_true]
  split_ifs with h
  · exact (floor_div_int _ _ hs).symm
  · exact BitcoinFeerateDiagram.div_round_down_eq_floor _ _ hs
