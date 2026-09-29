-- Prove2me | solution 1 for BlockCycleRotation.lemma17_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:30:40.393963+00:00
-- url     : https://prove2.me/submissions/bfda76dd-395f-42dd-a1fb-8f84b39e7a6e

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_lower_order_le
import Theorems.Thm_BlockCycleRotation_cTerm_summable
import Theorems.Thm_BlockCycleRotation_cConst_le_bulk_add
import Theorems.Thm_BlockCycleRotation_bulk_double_le_pairs
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem cTerm_nonneg (p : ℕ × ℕ) : 0 ≤ cTerm p := by
  unfold cTerm
  split
  · positivity
  · exact le_refl 0

/-- **The main term splits.** -/
theorem G1_split (m d : ℕ) (s : Finset (ℕ × ℕ)) :
    ∑ p ∈ s, ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p)
      = (∑ p ∈ s, (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)))
        + (m : ℝ) ^ 2 * ∑ p ∈ s, cTerm p := by
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- **Any partial sum of the series is at most `C`.** -/
theorem sum_cTerm_le_cConst (s : Finset (ℕ × ℕ)) : ∑ p ∈ s, cTerm p ≤ cConst :=
  Summable.sum_le_tsum s (fun p _ => cTerm_nonneg p) cTerm_summable

/-- **The partial sum over the bulk is squeezed.**  Together with
`cConst_le_bulk_add`, the bulk partial sum of `cTerm` lies within `3/(2N)` of
`C`, so `m²` times it lies within `m²·3/(2N)` of `m²·C`.  With
`N = √(m/(2d))` that error is `O(m^{3/2}√d)`, matching the small part. -/
theorem bulk_sum_close {m d N : ℕ} (hN : 0 < N)
    (hbulk : ∀ a a', a ≤ N → 1 ≤ a' → a' < a → d * a * (a + a') ≤ m) :
    cConst - 3 / (2 * (N : ℝ))
      ≤ ∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a,
          (if d * a * (a + a') ≤ m then cTerm (a, a') else 0) := by
  have h := cConst_le_bulk_add hN hbulk
  linarith

/-- **The bulk pair sum is within `3/(2N)` of `C`.**

This is the reconciled form of `bulk_sum_close`: the partial sum of the series
for `C` over the bulk pairs — the shape the main term actually produces — is
squeezed between `C - 3/(2N)` and `C`. -/
theorem bulk_pairs_close {m d N : ℕ} (hN : 0 < N) (hd : 0 < d)
    (hbulk : ∀ a a', a ≤ N → 1 ≤ a' → a' < a → d * a * (a + a') ≤ m) :
    cConst - 3 / (2 * (N : ℝ))
        ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m), cTerm p
      ∧ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m), cTerm p
        ≤ cConst :=
  ⟨le_trans (bulk_sum_close hN hbulk) (bulk_double_le_pairs hd),
    sum_cTerm_le_cConst _⟩

end BlockCycleRotation

open BlockCycleRotation in
/-- **Lemma 17, at a single divisor.**

The main term for the divisor `d`, with `m = n/d`, differs from `m²·C` by at
most the lower-order part plus the truncation error.  Taking
`N = √(m/(2d))` both are `O(m^{3/2}√d)`. -/
theorem solution {m d N : ℕ} (hm : 0 < m) (hd : 0 < d) (hN : 0 < N)
    (hbulk : ∀ a a', a ≤ N → 1 ≤ a' → a' < a → d * a * (a + a') ≤ m) :
    |(∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
          ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p))
        - (m : ℝ) ^ 2 * cConst|
      ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * ((d : ℝ) * (m : ℝ))
        + (m : ℝ) ^ 2 * (3 / (2 * (N : ℝ))):= by
  rw [G1_split]
  obtain ⟨hlow, hhigh⟩ := bulk_pairs_close hN hd hbulk
  have hL := lower_order_le hm hd
  have hLnn : (0 : ℝ) ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
      (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hm2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have htrunc : (0 : ℝ) ≤ (m : ℝ) ^ 2 * (3 / (2 * (N : ℝ))) := by positivity
  rw [abs_le]
  constructor
  · nlinarith [hlow, hLnn, hm2]
  · nlinarith [hhigh, hL, hm2, htrunc]
