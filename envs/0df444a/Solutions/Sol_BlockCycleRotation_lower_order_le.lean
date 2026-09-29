-- Prove2me | solution 1 for BlockCycleRotation.lower_order_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:27:14.983542+00:00
-- url     : https://prove2.me/submissions/19d3337c-0cca-4334-b7df-410f2283fbb4

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_sum_coprimePairs_filter
import Theorems.Thm_BlockCycleRotation_card_a_le
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

/-- For each `a`, the number of admissible `a'` is less than `a`. -/
theorem card_coprimeSecond_lt {a : ℕ} (ha : 0 < a) :
    (((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card : ℝ) ≤ (a : ℝ) := by
  have h : ((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card ≤ a := by
    calc ((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card
        ≤ (Finset.Ico 1 a).card := Finset.card_filter_le _ _
      _ = a - 1 := by simp
      _ ≤ a := Nat.sub_le _ _
  exact_mod_cast h

end BlockCycleRotation

open BlockCycleRotation in
/-- **The lower-order part of the main term.** -/
theorem solution {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
        (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
      ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * ((d : ℝ) * (m : ℝ)):= by
  have hsub : (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m)
      ⊆ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m) := by
    rintro ⟨a, a'⟩ hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨hmem, hbulk⟩ := hp
    obtain ⟨-, ha1, ha2, -⟩ := mem_coprimePairs.1 hmem
    exact ⟨hmem, by nlinarith⟩
  calc ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
        (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
      ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = ∑ a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
          ∑ a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
            (d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) :=
        sum_coprimePairs_filter (m := m) (d := d)
          (g := fun a a' => (d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)))
    _ ≤ ∑ _a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m), (d : ℝ) * (m : ℝ) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · subst h0
          simp
          positivity
        · have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h0
          have hcard := card_coprimeSecond_lt h0
          calc ∑ a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
                (d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ))
              ≤ ∑ _a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
                  (d : ℝ) * (m : ℝ) / (a : ℝ) := by
                refine Finset.sum_le_sum fun a' _ => ?_
                have ha'0 : (0 : ℝ) ≤ (a' : ℝ) := by positivity
                apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
            _ = (((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card : ℝ)
                  * ((d : ℝ) * (m : ℝ) / (a : ℝ)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (a : ℝ) * ((d : ℝ) * (m : ℝ) / (a : ℝ)) := by
                refine mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = (d : ℝ) * (m : ℝ) := by field_simp
    _ = ((((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ))
          * ((d : ℝ) * (m : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * ((d : ℝ) * (m : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h := card_a_le (m := m) hd
        have hc : ((((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ))
            ≤ ((Nat.sqrt ((m - 1) / d) + 1 : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at hc
        linarith
