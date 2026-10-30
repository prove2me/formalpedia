-- Prove2me | solution 1 for BitcoinFeerateDiagram.divFallback_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:16:28.538468+00:00
-- url     : https://prove2.me/submissions/4271dbeb-8fce-4163-8e97-5f675fffadf3

import Definitions.Def_BitcoinFeerateDiagram
import Theorems.Thm_BitcoinFeerateDiagram_div_round_down_eq_floor
import Theorems.Thm_BitcoinFeerateDiagram_div_round_up_eq_ceil

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

/-- `DivFallback((high, low), d, round_down)` computes `Div(high * 2^32 + low, d, round_down)`:
the 96/32 fallback division agrees with the `__int128` division (for `d > 0`). -/
theorem solution (n : ℤ × ℤ) (d : ℤ) (hd : 0 < d) (rd : Bool) :
    FeeFrac.divFallback n d rd = FeeFrac.div (n.1 * 2 ^ 32 + n.2) d rd := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  -- `n.1 = d * tdiv + tmod`
  have hsplit : n.1 = d * n.1.tdiv d + n.1.tmod d := by
    obtain ⟨h1, h2, h3⟩ := ediv_emod_facts n.1 d hd
    rcases tdiv_tmod_facts n.1 d hd with ⟨hq, hr⟩ | ⟨hq, hr, hne⟩ <;> rw [hq, hr] <;> linarith
  -- the low part of the fallback is literally `div nLow d rd`
  have hlow : FeeFrac.divFallback n d rd =
      n.1.tdiv d * 2 ^ 32 + FeeFrac.div (n.1.tmod d * 2 ^ 32 + n.2) d rd := rfl
  rw [hlow]
  generalize n.1.tdiv d = q at hsplit ⊢
  generalize n.1.tmod d = r at hsplit ⊢
  have hN : n.1 * 2 ^ 32 + n.2 = (r * 2 ^ 32 + n.2) + (q * 2 ^ 32) * d := by
    rw [hsplit]; ring
  have key : (((r * 2 ^ 32 + n.2) + (q * 2 ^ 32) * d : ℤ) : ℚ) / d =
      ((r * 2 ^ 32 + n.2 : ℤ) : ℚ) / d + ((q * 2 ^ 32 : ℤ) : ℚ) := by
    push_cast; field_simp
  cases rd
  · rw [BitcoinFeerateDiagram.div_round_up_eq_ceil _ _ hd,
      BitcoinFeerateDiagram.div_round_up_eq_ceil _ _ hd, hN, key, Int.ceil_add_intCast]
    ring
  · rw [BitcoinFeerateDiagram.div_round_down_eq_floor _ _ hd,
      BitcoinFeerateDiagram.div_round_down_eq_floor _ _ hd, hN, key, Int.floor_add_intCast]
    ring
