-- Prove2me | solution 1 for BlockCycleRotation.small_part_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:25:53.651819+00:00
-- url     : https://prove2.me/submissions/2ec90f9b-78ca-4f26-818f-d93a0eb82f76

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_gtTriples_decompose
import Theorems.Thm_BlockCycleRotation_sum_coprimePairs_filter
import Theorems.Thm_BlockCycleRotation_card_a_le
import Theorems.Thm_BlockCycleRotation_small_pair_le
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

theorem mem_coprimePairs {m a a' : ℕ} :
    (a, a') ∈ coprimePairs m ↔ (a ≤ m ∧ a' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ Nat.gcd a a' = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

end BlockCycleRotation

open BlockCycleRotation in
/-- **The small part is `O(m^{3/2}·√d)`.** -/
theorem solution {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      ≤ (Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)):= by
  classical
  rw [Finset.sum_filter,
    gtTriples_decompose hm (fun a a' b' =>
      if ¬ (d * a * (a + a') ≤ m) then d * a + (m - a' * b') / a else 0)]
  -- each pair contributes at most `(2d+2) · 2·(m/a)`
  have hpair : ∀ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
      (∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
          if ¬ (d * p.1 * (p.1 + p.2) ≤ m) then d * p.1 + (m - p.2 * b') / p.1 else 0)
        ≤ (2 * d + 2) * (2 * (m / p.1)) := by
    rintro ⟨a, a'⟩ hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpair', hda⟩ := hp
    obtain ⟨-, ha1, ha2, hgcd⟩ := mem_coprimePairs.1 hpair'
    by_cases hsmall : ¬ (d * a * (a + a') ≤ m)
    · simp only [hsmall, if_true]
      exact small_pair_le (by omega) ha1 hgcd hda ha2 hsmall
    · simp only [hsmall, if_false]
      simp
  refine le_trans (Finset.sum_le_sum hpair) ?_
  -- decompose the pairs by their first component
  rw [sum_coprimePairs_filter (m := m) (d := d)
    (g := fun a _ => (2 * d + 2) * (2 * (m / a)))]
  calc ∑ a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
        ∑ _a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
          (2 * d + 2) * (2 * (m / a))
      ≤ ∑ _a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
          (2 * d + 2) * (2 * m) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [Finset.sum_const, smul_eq_mul]
        have hc : ((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card ≤ a := by
          calc ((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card
              ≤ (Finset.Ico 1 a).card := Finset.card_filter_le _ _
            _ = a - 1 := by simp
            _ ≤ a := Nat.sub_le _ _
        have hma : a * (m / a) ≤ m := Nat.mul_div_le m a
        calc ((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card
              * ((2 * d + 2) * (2 * (m / a)))
            ≤ a * ((2 * d + 2) * (2 * (m / a))) := Nat.mul_le_mul_right _ hc
          _ = (2 * d + 2) * (2 * (a * (m / a))) := by ring
          _ ≤ (2 * d + 2) * (2 * m) := by
              exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hma)
    _ = (((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card)
          * ((2 * d + 2) * (2 * m)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) :=
        Nat.mul_le_mul_right _ (card_a_le hd)
