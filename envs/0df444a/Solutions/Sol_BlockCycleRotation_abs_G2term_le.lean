-- Prove2me | solution 1 for BlockCycleRotation.abs_G2term_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:50:01.815981+00:00
-- url     : https://prove2.me/submissions/70626cc0-932e-4960-96f4-b25e43009b3b

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem13
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_gtBound_bulk_eq
import Theorems.Thm_BlockCycleRotation_main_term_vs_sum
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
/-- **The bound of Lemma 18 at one pair:** `|G₂| ≤ |A| + |B·Y|`. -/
theorem solution {m d a a' : ℕ} (hm : 0 < m) (hd : 0 < d)
    (ha' : 1 ≤ a') (haa : a' < a) (hbulk : d * a * (a + a') ≤ m) :
    |G2term m d a a'| ≤ |aCoeff m d a| + |bCoeff a a'| * yCut m a a':= by
  have ha : 0 < a := by omega
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hs : a + a' ≤ m := by
    refine le_trans ?_ hbulk
    calc a + a' = 1 * 1 * (a + a') := by ring
      _ ≤ d * a * (a + a') := Nat.mul_le_mul (Nat.mul_le_mul hd ha) (le_refl _)
  have hsR : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by
    have : (0 : ℝ) < (a : ℝ) := by linarith
    have : (0 : ℝ) ≤ (a' : ℝ) := by positivity
    linarith
  have hUeq : gtBound m d a a' = (m - 1) / (a + a') + 1 := gtBound_bulk_eq hd ha' haa hbulk
  set K := (m - 1) / (a + a') with hKdef
  have hU1 : 1 ≤ gtBound m d a a' := by rw [hUeq]; exact Nat.le_add_left 1 K
  have hsum : innerLinear m d a a'
      = aCoeff m d a * (K : ℝ) + bCoeff a a' * ((K : ℝ) * ((K : ℝ) + 1)) / 2 := by
    rw [innerLinear, sum_linear_Ico _ _ _ hU1, hUeq]
    push_cast
    ring
  have hKV : (K : ℝ) ≤ yCut m a a' := by
    rw [yCut, le_div_iff₀ hsR]
    have h1 : K * (a + a') ≤ m := le_trans (Nat.div_mul_le_self _ _) (by omega)
    have h2 : ((K * (a + a') : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hVK : yCut m a a' ≤ (K : ℝ) + 1 := by
    rw [yCut, div_le_iff₀ hsR]
    have h1 : m - 1 < (K + 1) * (a + a') := by
      have hdm := Nat.div_add_mod (m - 1) (a + a')
      have hlt : (m - 1) % (a + a') < a + a' := Nat.mod_lt _ (by omega)
      nlinarith
    have h2 : m ≤ (K + 1) * (a + a') := by omega
    have h3 : (m : ℝ) ≤ (((K + 1) * (a + a') : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hV1 : 1 ≤ yCut m a a' := by
    rw [yCut, le_div_iff₀ hsR]
    have : ((a + a' : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hs
    push_cast at this
    linarith
  have hmts := main_term_vs_sum (aCoeff m d a) (bCoeff a a') (yCut m a a') K hKV hVK hV1
  have hG2 : G2term m d a a'
      = (1 / (a : ℝ)) * ((aCoeff m d a * (K : ℝ)
          + bCoeff a a' * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
        - (aCoeff m d a * yCut m a a' + bCoeff a a' * yCut m a a' ^ 2 / 2)) := by
    unfold G2term G1term
    rw [hsum]
    ring
  rw [hG2, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (a : ℝ))]
  have hia : 1 / (a : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have habs : |(aCoeff m d a * (K : ℝ) + bCoeff a a' * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
      - (aCoeff m d a * yCut m a a' + bCoeff a a' * yCut m a a' ^ 2 / 2)|
      ≤ |aCoeff m d a| + |bCoeff a a'| * yCut m a a' := by
    rw [abs_sub_comm]
    exact hmts
  have hYnn : (0 : ℝ) ≤ yCut m a a' := by linarith
  calc 1 / (a : ℝ) * |(aCoeff m d a * (K : ℝ) + bCoeff a a' * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
          - (aCoeff m d a * yCut m a a' + bCoeff a a' * yCut m a a' ^ 2 / 2)|
      ≤ 1 * (|aCoeff m d a| + |bCoeff a a'| * yCut m a a') :=
        mul_le_mul hia habs (abs_nonneg _)
          (by positivity)
    _ = |aCoeff m d a| + |bCoeff a a'| * yCut m a a' := one_mul _
