-- Prove2me | solution 1 for BlockCycleRotation.bulk_pair_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:47:40.169961+00:00
-- url     : https://prove2.me/submissions/e6a5ac9b-7ee1-4c4a-b616-149800ab4385

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_gtBound_bulk_eq
import Theorems.Thm_BlockCycleRotation_inner_gt_estimate
import Theorems.Thm_BlockCycleRotation_main_term_vs_sum
import Theorems.Thm_BlockCycleRotation_main_term_substitute
import Mathlib

open Finset Real

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
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem mem_gtRange {m d a a' b' : ℕ} (hm : 0 < m) (haa : 0 < a + a') (ha' : 0 < a')
    (hda : d * a * a < m) :
    b' ∈ Finset.Ico 1 (gtBound m d a a')
      ↔ (1 ≤ b' ∧ (a + a') * b' < m ∧ a' * b' + d * a * a < m) := by
  rw [Finset.mem_Ico, gtBound, lt_min_iff, Nat.lt_succ_iff, Nat.lt_succ_iff,
    Nat.le_div_iff_mul_le haa, Nat.le_div_iff_mul_le ha',
    Nat.mul_comm b' (a + a'), Nat.mul_comm b' a']
  omega

/-- **The closed form of the main term.**  `∑_{1 ≤ b < U} (A + B·b)`. -/
theorem sum_linear_Ico (A B : ℝ) : ∀ U : ℕ, 1 ≤ U →
    ∑ b ∈ Finset.Ico 1 U, (A + B * (b : ℝ))
      = A * ((U : ℝ) - 1) + B * (((U : ℝ) - 1) * (U : ℝ) / 2) := by
  intro U hU
  induction U, hU using Nat.le_induction with
  | base => simp
  | succ U hU ih =>
    rw [Finset.sum_Ico_succ_top hU, ih]
    push_cast
    ring

end BlockCycleRotation

open BlockCycleRotation in
set_option maxHeartbeats 1000000 in
-- Three separate approximations are chained here, each with its own algebraic
-- normalisation; the default budget is not enough.
/-- **The estimate at a single bulk pair.** -/
theorem solution {m d a a' : ℕ} (hm : 0 < m) (hd : 0 < d)
    (ha' : 1 ≤ a') (haa : a' < a) (hgcd : Nat.gcd a a' = 1)
    (hbulk : d * a * (a + a') ≤ m) :
    |((∑ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
          (d * a + (m - a' * b') / a) : ℕ) : ℝ)
        - ((d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a'))|
      ≤ 2 * (((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / (a : ℝ)) * (1 + Real.log m):= by
  have ha : 0 < a := by omega
  have hs : 0 < a + a' := by omega
  have hda2 : d * a * a < m := by nlinarith
  have haleM : a ≤ m := by
    refine le_trans ?_ hbulk
    calc a = 1 * a * 1 := by ring
      _ ≤ d * a * (a + a') := Nat.mul_le_mul (Nat.mul_le_mul hd (le_refl a)) hs
  have hsm : a + a' ≤ m := by
    refine le_trans ?_ hbulk
    calc a + a' = 1 * 1 * (a + a') := by ring
      _ ≤ d * a * (a + a') := Nat.mul_le_mul (Nat.mul_le_mul hd ha) (le_refl _)
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha'R : (1 : ℝ) ≤ (a' : ℝ) := by exact_mod_cast ha'
  have hsR : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- the cut-off
  have hUeq : gtBound m d a a' = (m - 1) / (a + a') + 1 := gtBound_bulk_eq hd ha' haa hbulk
  set K := (m - 1) / (a + a') with hKdef
  set U := gtBound m d a a' with hUdef
  have hU1 : 1 ≤ U := by rw [hUeq]; exact Nat.le_add_left 1 K
  have hrange : ∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m := by
    intro b' hb'
    have := (mem_gtRange hm hs ha' hda2).1 hb'
    omega
  -- the three approximations
  obtain ⟨c, hc⟩ := inner_gt_estimate (m := m) (d := d) (a := a) (a' := a') ha hgcd U hrange
  set A : ℝ := ((d * a : ℕ) : ℝ) + (m : ℝ) / (a : ℝ) with hA
  set B : ℝ := -(a' : ℝ) / (a : ℝ) with hB
  set V : ℝ := (m : ℝ) / ((a : ℝ) + (a' : ℝ)) with hV
  have hsum : ∑ b' ∈ Finset.Ico 1 U, (A + B * (b' : ℝ))
      = A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2 := by
    rw [sum_linear_Ico A B U hU1, hUeq]
    push_cast
    ring
  have hKV : (K : ℝ) ≤ V := by
    rw [hV, le_div_iff₀ hsR]
    have h1 : K * (a + a') ≤ m := le_trans (Nat.div_mul_le_self _ _) (by omega)
    have h2 : ((K * (a + a') : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hVK : V ≤ (K : ℝ) + 1 := by
    rw [hV, div_le_iff₀ hsR]
    have h1 : m - 1 < (K + 1) * (a + a') := by
      have hdm := Nat.div_add_mod (m - 1) (a + a')
      have hlt : (m - 1) % (a + a') < a + a' := Nat.mod_lt _ hs
      nlinarith
    have h2 : m ≤ (K + 1) * (a + a') := by omega
    have h3 : (m : ℝ) ≤ (((K + 1) * (a + a') : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hV1 : 1 ≤ V := by
    rw [hV, le_div_iff₀ hsR]
    have : ((a + a' : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hsm
    push_cast at this
    linarith
  have hmts := main_term_vs_sum A B V K hKV hVK hV1
  have hsubst := main_term_substitute (m := m) (d := d) ha' haa hgcd
  -- absolute values of the coefficients
  have hAnn : (0 : ℝ) ≤ A := by rw [hA]; positivity
  have hAabs : |A| = A := abs_of_nonneg hAnn
  have hBabs : |B| = (a' : ℝ) / (a : ℝ) := by
    rw [hB, abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (a' : ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (a : ℝ))]
  have hBV : |B| * V ≤ (m : ℝ) / (a : ℝ) := by
    rw [hBabs, hV, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (m : ℝ))
      (by linarith : (0:ℝ) ≤ (a : ℝ))) (by linarith : (0:ℝ) ≤ (a : ℝ))]
  set W : ℝ := ((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / (a : ℝ) with hW
  have hAW : |A| + |B| * V ≤ W := by
    rw [hAabs, hA, hW]
    have : (m : ℝ) / (a : ℝ) + (m : ℝ) / (a : ℝ) = 2 * (m : ℝ) / (a : ℝ) := by ring
    linarith [hBV]
  have hAWK : |A| + |B| * ((U - 1 : ℕ) : ℝ) ≤ W := by
    have hUK : ((U - 1 : ℕ) : ℝ) = (K : ℝ) := by
      have : U - 1 = K := by omega
      rw [this]
    rw [hUK]
    have hBK : |B| * (K : ℝ) ≤ |B| * V := by
      refine mul_le_mul_of_nonneg_left hKV (abs_nonneg B)
    linarith [hAW]
  -- assemble
  have hWnn : (0 : ℝ) ≤ W := by rw [hW]; positivity
  have hloga : Real.log a ≤ Real.log m := Real.log_le_log (by linarith) (by exact_mod_cast haleM)
  have hlogm : (0 : ℝ) ≤ Real.log m := Real.log_nonneg hmR
  have hlogann : (0 : ℝ) ≤ Real.log a := Real.log_nonneg haR
  have hstep1 : |((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
        (d * a + (m - a' * b') / a) : ℕ) : ℝ)
      - (1 / (a : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)|
      ≤ W * (1 + Real.log a) := by
    rw [← hsum]
    refine hc.trans ?_
    exact mul_le_mul_of_nonneg_right hAWK (by linarith)
  have hstep2 : |(1 / (a : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
      - ((d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a'))| ≤ W := by
    rw [← hsubst, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (a : ℝ))]
    have hinner : |(A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2) - (A * V + B * V ^ 2 / 2)|
        ≤ W := by
      rw [abs_sub_comm]
      exact hmts.trans hAW
    have hia : 1 / (a : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    calc 1 / (a : ℝ) * |(A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2) - (A * V + B * V ^ 2 / 2)|
        ≤ 1 * W := mul_le_mul hia hinner (abs_nonneg _) (by norm_num)
      _ = W := one_mul W
  calc |((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
          (d * a + (m - a' * b') / a) : ℕ) : ℝ)
        - ((d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a'))|
      ≤ W * (1 + Real.log a) + W := by
        have := abs_add_le
          (((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
              (d * a + (m - a' * b') / a) : ℕ) : ℝ)
            - (1 / (a : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2))
          ((1 / (a : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
            - ((d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a')))
        simp only [sub_add_sub_cancel] at this
        linarith [hstep1, hstep2]
    _ ≤ 2 * W * (1 + Real.log m) := by nlinarith
