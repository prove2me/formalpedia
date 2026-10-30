-- Prove2me | solution 1 for BitcoinFeerateDiagram.getFee_eq_evaluateFeeUp
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:18:43.010131+00:00
-- url     : https://prove2.me/submissions/6c051f31-4443-470c-98e4-8810fdc651fa

import Definitions.Def_BitcoinFeerateDiagram
import Theorems.Thm_BitcoinFeerateDiagram_evaluateFeeUp_eq_ceil

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

/-- `CFeeRate::GetFee` of the previous mission (`FeeRate.getFee`, the ℕ ceiling
`(fee * v + (size - 1)) / size`) is `FeeFrac::EvaluateFeeUp` on the same fraction. -/
theorem solution (r : FeeRate) (v : ℕ) :
    (r.getFee v : ℤ) = FeeFrac.evaluateFeeUp ⟨r.fee, r.size⟩ v := by
  have hsz := r.size_pos
  have hs : (0 : ℤ) < (⟨(r.fee : ℤ), (r.size : ℤ)⟩ : FeeFrac).size := by
    simp; exact hsz
  rw [BitcoinFeerateDiagram.evaluateFeeUp_eq_ceil _ _ hs (by positivity)]
  simp only
  have hs' : (0 : ℚ) < ((r.size : ℤ) : ℚ) := by exact_mod_cast hsz
  symm
  rw [Int.ceil_eq_iff]
  unfold FeeRate.getFee
  have h1 : (r.fee * v + (r.size - 1)) % r.size + r.size * ((r.fee * v + (r.size - 1)) / r.size)
      = r.fee * v + (r.size - 1) := Nat.mod_add_div _ _
  have h3 : (r.fee * v + (r.size - 1)) % r.size < r.size := Nat.mod_lt _ hsz
  generalize (r.fee * v + (r.size - 1)) / r.size = q at h1 ⊢
  generalize (r.fee * v + (r.size - 1)) % r.size = m at h1 h3 ⊢
  have e : (m : ℚ) + r.size * q = r.fee * v + r.size - 1 := by
    have : (m : ℤ) + r.size * q = r.fee * v + r.size - 1 := by omega
    exact_mod_cast this
  have hm : (m : ℚ) + 1 ≤ r.size := by exact_mod_cast h3
  have hm0 : (0 : ℚ) ≤ m := by positivity
  constructor
  · refine (lt_div_iff₀ hs').2 ?_
    push_cast
    linarith
  · refine (div_le_iff₀ hs').2 ?_
    push_cast
    linarith
