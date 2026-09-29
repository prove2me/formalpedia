-- Prove2me | solution 1 for BlockCycleRotation.middle_layer_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:21:48.937644+00:00
-- url     : https://prove2.me/submissions/a29b32a1-7eaf-4ad9-ac8d-2c3391f3222a

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_sum_coprimePairs_filter
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
/-- **The middle layer.**  Summing the per-pair error bound over the coprime
pairs gives `3m(1 + log m)` for each admissible `a`. -/
theorem solution {m d : ℕ} (hm : 0 < m) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
        (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / p.1) * (1 + Real.log m)
      ≤ (((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ)
          * (3 * (m : ℝ) * (1 + Real.log m)):= by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : (0 : ℝ) ≤ 1 + Real.log m := by
    have := Real.log_nonneg hm'
    linarith
  rw [sum_coprimePairs_filter (m := m) (d := d)
    (g := fun a _ => (((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a) * (1 + Real.log m))]
  calc ∑ a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
        ∑ _a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
          (((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a) * (1 + Real.log m)
      ≤ ∑ _a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
          3 * (m : ℝ) * (1 + Real.log m) := by
        refine Finset.sum_le_sum fun a ha => ?_
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        obtain ⟨ham, hda⟩ := ha
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · subst h0
          simp
          positivity
        · have hcard := card_coprimeSecond_lt h0
          have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h0
          have hane : (a : ℝ) ≠ 0 := by linarith
          have hdle : (d : ℝ) * a * a ≤ (m : ℝ) := by
            have h2 : d * a * a ≤ m := hda.le
            exact_mod_cast h2
          calc ∑ _a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
                (((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a) * (1 + Real.log m)
              = ((((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card : ℝ))
                  * ((((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a) * (1 + Real.log m)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (a : ℝ) * ((((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a) * (1 + Real.log m)) := by
                refine mul_le_mul_of_nonneg_right hcard ?_
                have hnn : (0 : ℝ) ≤ ((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a := by positivity
                exact mul_nonneg hnn hlog
            _ = ((d : ℝ) * a * a + 2 * (m : ℝ)) * (1 + Real.log m) := by
                push_cast
                field_simp
            _ ≤ 3 * (m : ℝ) * (1 + Real.log m) := by nlinarith
    _ = (((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ)
          * (3 * (m : ℝ) * (1 + Real.log m)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
