-- Prove2me | solution 1 for DeepQOperator.eq_41_42
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T12:05:55.682417+00:00
-- url     : https://prove2.me/submissions/59845d02-29a0-454f-ac95-80e4503fe6cc

import Mathlib
import Definitions.Def_DeepQOperator_Quantizer

open DeepQOperator

namespace P2MHole01_448c6e4b
theorem solution (d : ℕ) (hd : (1 : ℕ) ≤ d) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) (1 : ℝ)) :
  (0 : ℝ) ≤ (2 : ℝ) ^ (d - (1 : ℕ)) * (x + (1 : ℝ)) ∧ (2 : ℝ) ^ (d - (1 : ℕ)) * (x + (1 : ℝ)) ≤ (2 : ℝ) ^ d := by
  have h1 : (0 : ℝ) ≤ x + 1 := by linarith [hx.1]
  have h2 : x + 1 ≤ 2 := by linarith [hx.2]
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (d - 1) := pow_nonneg (by norm_num) (d - 1)
  refine ⟨mul_nonneg hpow h1, ?_⟩
  calc
    (2 : ℝ) ^ (d - 1) * (x + 1) ≤ (2 : ℝ) ^ (d - 1) * 2 := by
      apply mul_le_mul_of_nonneg_left h2 hpow
    _ = (2 : ℝ) ^ (d - 1) * (2 : ℝ) ^ 1 := by norm_num
    _ = (2 : ℝ) ^ ((d - 1) + 1) := by rw [← pow_add]
    _ = (2 : ℝ) ^ d := by rw [Nat.sub_add_cancel hd]
end P2MHole01_448c6e4b

/-- Range of the affine scale `t(x) = 2^{d-1}(x+1)` on `[-1,1]`: `0 ≤ t(x) ≤ 2^d`. -/
lemma t_range (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ (2 : ℝ) ^ (d - 1) * (x + 1) ∧ (2 : ℝ) ^ (d - 1) * (x + 1) ≤ (2 ^ d : ℝ) := by
  (first | exact P2MHole01_448c6e4b.solution d hd x hx | (apply P2MHole01_448c6e4b.solution <;> assumption))

namespace P2MHole02_d740c2cc
theorem solution (d : ℕ) (hd : (1 : ℕ) ≤ d) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) (1 : ℝ))
  (ht : (0 : ℝ) ≤ (2 : ℝ) ^ (d - (1 : ℕ)) * (x + (1 : ℝ)) ∧ (2 : ℝ) ^ (d - (1 : ℕ)) * (x + (1 : ℝ)) ≤ (2 : ℝ) ^ d) :
  ↑(jEnc d x) ≤ (2 : ℝ) ^ (d - (1 : ℕ)) * (x + (1 : ℝ)) ∧
    (2 : ℝ) ^ (d - (1 : ℕ)) * (x + (1 : ℝ)) ≤ ↑(jEnc d x) + (1 : ℝ) := by
  set t := (2 : ℝ) ^ (d - (1 : ℕ)) * (x + (1 : ℝ)) with ht_def
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ (2 : ℝ) ^ d := ht.2
  have hf0 : 0 ≤ ⌊t⌋ := (Int.le_floor (z := (0 : ℤ))).mpr (by simpa using ht0)
  have hto : (Int.toNat ⌊t⌋ : ℤ) = ⌊t⌋ := Int.toNat_of_nonneg hf0
  have htoR : ((Int.toNat ⌊t⌋ : ℕ) : ℝ) = (⌊t⌋ : ℝ) := by
    rw [← hto]
    norm_cast
  by_cases hcase : ⌊t⌋ ≤ (2 : ℤ) ^ d - 1
  · -- the min keeps the toNat branch
    have hto_le : Int.toNat ⌊t⌋ ≤ 2 ^ d - 1 := by simpa [hto] using hcase
    have hj : jEnc d x = Int.toNat ⌊t⌋ := by
      dsimp only [jEnc]
      exact (min_eq_iff (a := (2 : ℕ) ^ d - 1) (b := Int.toNat ⌊t⌋) (c := Int.toNat ⌊t⌋)).mpr
        (Or.inr ⟨rfl, hto_le⟩)
    refine ⟨?_, ?_⟩
    · rw [hj, htoR]
      exact Int.floor_le t
    · rw [hj, htoR]
      linarith [Int.lt_floor_add_one t]
  · -- the min keeps the 2^d - 1 branch
    have hge : (2 : ℤ) ^ d ≤ ⌊t⌋ := by
      have hlt : (2 : ℤ) ^ d - 1 < ⌊t⌋ := (not_le (a := ⌊t⌋)).mp hcase
      linarith
    have h2d_le_n : (2 : ℕ) ^ d ≤ Int.toNat ⌊t⌋ := by
      have h2dI : (2 : ℤ) ^ d ≤ (Int.toNat ⌊t⌋ : ℤ) := by
        rw [hto]
        exact hge
      exact_mod_cast h2dI
    have h1n : (2 : ℕ) ^ d - 1 ≤ 2 ^ d := Nat.le_of_lt (Nat.sub_lt (Nat.two_pow_pos d) Nat.one_pos)
    have hj : jEnc d x = 2 ^ d - 1 := by
      dsimp only [jEnc]
      exact (min_eq_iff (a := (2 : ℕ) ^ d - 1) (b := Int.toNat ⌊t⌋) (c := (2 : ℕ) ^ d - 1)).mpr
        (Or.inl ⟨rfl, le_trans h1n h2d_le_n⟩)
    have htf : (2 : ℝ) ^ d ≤ t := by
      have hgeR : (2 : ℝ) ^ d ≤ (⌊t⌋ : ℝ) := by exact_mod_cast hge
      simpa using le_trans hgeR (Int.floor_le t)
    have hcast : ((2 ^ d - 1 : ℕ) : ℝ) = (2 : ℝ) ^ d - 1 := by
      simpa using Nat.cast_sub (n := (1 : ℕ))
    refine ⟨?_, ?_⟩
    · rw [hj]
      linarith [htf, hcast]
    · rw [hj]
      linarith [htf, hcast]
end P2MHole02_d740c2cc

/-- `x` lies in bin `jEnc d x` on the scale `t(x) = 2^{d-1}(x+1)`:
`jEnc ≤ t(x) ≤ jEnc + 1`, with the top bin truncated at `t = 2^d` (i.e. `x = 1`). -/
-- riskiest
lemma jEnc_bin (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (ht : 0 ≤ (2 : ℝ) ^ (d - 1) * (x + 1) ∧ (2 : ℝ) ^ (d - 1) * (x + 1) ≤ (2 ^ d : ℝ)) :
    (jEnc d x : ℝ) ≤ (2 : ℝ) ^ (d - 1) * (x + 1) ∧
    (2 : ℝ) ^ (d - 1) * (x + 1) ≤ (jEnc d x : ℝ) + 1 := by
  (first | exact P2MHole02_d740c2cc.solution d hd x hx ht | (apply P2MHole02_d740c2cc.solution <;> assumption))

/-- A point in bin `j` is at most half the bin width `2^{-d+1}/2 = 2^{-d}` from its midpoint
`recon d j`: `|recon d j - x| ≤ 2^{-d}` whenever `j ≤ t(x) ≤ j + 1`. -/
lemma bin_err (d : ℕ) (hd : 1 ≤ d) (j : ℕ) (x : ℝ)
    (ht : (j : ℝ) ≤ (2 : ℝ) ^ (d - 1) * (x + 1) ∧ (2 : ℝ) ^ (d - 1) * (x + 1) ≤ (j : ℝ) + 1) :
    |recon d j - x| ≤ (2 : ℝ) ^ (-(d : ℤ)) := by
  set t := (2 : ℝ) ^ (d - 1) * (x + 1)
  have hpow : 0 < (2 : ℝ) ^ d := by positivity
  have hd0 : (2 : ℝ) ^ d ≠ 0 := ne_of_gt hpow
  have ht1 : (j : ℝ) ≤ t := ht.1
  have ht2 : t ≤ (j : ℝ) + 1 := ht.2
  have h2 : (2 : ℝ) ^ d = 2 * (2 : ℝ) ^ (d - 1) := by
    have hd' : (d - 1) + 1 = d := Nat.sub_add_cancel hd
    rw [← congrArg (fun k : ℕ => (2 : ℝ) ^ k) hd', pow_succ']
  have hx2 : x * (2 : ℝ) ^ d = 2 * t - (2 : ℝ) ^ d := by
    calc
      x * (2 : ℝ) ^ d = x * (2 * (2 : ℝ) ^ (d - 1)) := by rw [h2]
      _ = 2 * (x * (2 : ℝ) ^ (d - 1)) := by ring
      _ = 2 * (((x + 1) * (2 : ℝ) ^ (d - 1)) - (2 : ℝ) ^ (d - 1)) := by ring
      _ = 2 * ((2 : ℝ) ^ (d - 1) * (x + 1) - (2 : ℝ) ^ (d - 1)) := by ring
      _ = 2 * t - (2 : ℝ) ^ d := by simp [t, h2]; ring
  have hdiff : (2 : ℝ) ^ d * (recon d j - x) = 2 * (j : ℝ) - 2 * t + 1 := by
    rw [recon]
    calc
      (2 : ℝ) ^ d * (-1 + (2 * (j : ℝ) + 1) / (2 : ℝ) ^ d - x) =
          (2 : ℝ) ^ d * -1 + (2 : ℝ) ^ d * ((2 * (j : ℝ) + 1) / (2 : ℝ) ^ d) -
          (2 : ℝ) ^ d * x := by ring
      _ = (2 : ℝ) ^ d * -1 + (2 * (j : ℝ) + 1) - x * (2 : ℝ) ^ d := by
        have hd1 : (2 : ℝ) ^ d * ((2 * (j : ℝ) + 1) / (2 : ℝ) ^ d) = 2 * (j : ℝ) + 1 := by
          field_simp [hd0]
        rw [hd1, mul_comm]
        ring
      _ = 2 * (j : ℝ) - 2 * t + 1 := by rw [hx2]; ring
  have hle : |(2 : ℝ) ^ d * (recon d j - x)| ≤ 1 := by
    rw [hdiff]
    apply abs_le.mpr
    constructor
    · linarith [ht1, ht2]
    · linarith [ht1, ht2]
  calc
    |recon d j - x| = |(2 : ℝ) ^ d * (recon d j - x) / (2 : ℝ) ^ d| := by
      field_simp [hd0]
    _ = |(2 : ℝ) ^ d * (recon d j - x)| / (2 : ℝ) ^ d := by
      rw [abs_div, abs_of_nonneg (le_of_lt hpow)]
    _ ≤ 1 / (2 : ℝ) ^ d := by
      have hb : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ d := by positivity
      have h : (1 / (2 : ℝ) ^ d) * |(2 : ℝ) ^ d * (recon d j - x)| ≤
          (1 / (2 : ℝ) ^ d) * 1 := mul_le_mul_of_nonneg_left hle hb
      convert h using 2
      · ring
      · ring
    _ = (2 : ℝ) ^ (-(d : ℤ)) := by
      rw [zpow_neg]
      norm_num

namespace P2MHole04_f8c54082
theorem solution (d : ℕ) : Measurable fun (x : ℝ) => ⌊(2 : ℝ) ^ (d - (1 : ℕ)) * (x + (1 : ℝ))⌋ := by
  fun_prop
end P2MHole04_f8c54082

/-- The affine floor `x ↦ ⌊2^{d-1}(x+1)⌋` is Borel-measurable into `ℤ`. -/
lemma floor_t_meas (d : ℕ) : Measurable (fun x : ℝ => ⌊(2 : ℝ) ^ (d - 1) * (x + 1)⌋) := by
  (first | exact P2MHole04_f8c54082.solution d | (apply P2MHole04_f8c54082.solution <;> assumption))

namespace P2MHole05_96601d22
theorem solution : Measurable Int.toNat := by
  solve_by_elim
end P2MHole05_96601d22

/-- `Int.toNat : ℤ → ℕ` is measurable (discrete codomain). -/
lemma toNat_meas : Measurable (Int.toNat : ℤ → ℕ) := by
  (first | exact P2MHole05_96601d22.solution | (apply P2MHole05_96601d22.solution <;> assumption))

/-- **(41)–(42)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.1, p.23, PDF p.26).

For an integer `d ≥ 1` and `x ∈ [-1, 1]`, the index `j_d(x)` lies in `{0, …, 2^d - 1}`, the
reconstruction obeys `|Q_d(x) - x| ≤ 2^{-d}` (42), and the encoder is Borel measurable.

**Formalization Note.** `jEnc`, `qRound` are (41) (see `Def_DeepQOperator_Quantizer`).
`2^{-d}` is the integer power `(2:ℝ) ^ (-(d:ℤ))`. Measurability is with the Borel σ-algebra on
`ℝ` and the discrete one on `ℕ`. -/
theorem solution :
    (∀ d : ℕ, 1 ≤ d → ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      jEnc d x < 2 ^ d ∧ |qRound d x - x| ≤ (2 : ℝ) ^ (-(d : ℤ))) ∧
    (∀ d : ℕ, Measurable (jEnc d)) := by
  constructor
  · intro d hd x hx
    have htr := t_range d hd x hx
    constructor
    · exact jEnc_lt d x
    · simpa [qRound] using (bin_err d hd (jEnc d x) x) (jEnc_bin d hd x hx htr)
  · intro d
    have h : jEnc d = fun x : ℝ =>
        min (2 ^ d - 1) (Int.toNat (⌊(2 : ℝ) ^ (d - 1) * (x + 1)⌋)) := by rfl
    rw [h]
    have hconst : Measurable (fun _ : ℝ => 2 ^ d - 1) := measurable_const
    exact Measurable.inf hconst (Measurable.comp toNat_meas (floor_t_meas d))
