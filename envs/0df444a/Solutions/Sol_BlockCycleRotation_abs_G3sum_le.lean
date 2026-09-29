-- Prove2me | solution 1 for BlockCycleRotation.abs_G3sum_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:51:44.359621+00:00
-- url     : https://prove2.me/submissions/68131f95-903d-497f-a3fe-c6182140e7f6

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem13
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_gtBound_bulk_eq
import Theorems.Thm_BlockCycleRotation_abs_G3term_le
import Theorems.Thm_BlockCycleRotation_aggregate_le
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

theorem mem_coprimePairs {m a a' : ℕ} :
    (a, a') ∈ coprimePairs m ↔ (a ≤ m ∧ a' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ Nat.gcd a a' = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem gtBound_sub_one_le_yCut {m d a a' : ℕ} (hd : 0 < d) (ha' : 1 ≤ a') (haa : a' < a)
    (hbulk : d * a * (a + a') ≤ m) :
    ((gtBound m d a a' - 1 : ℕ) : ℝ) ≤ yCut m a a' := by
  have ha : 0 < a := by omega
  have hsR : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by
    have h1 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have h2 : (0 : ℝ) ≤ (a' : ℝ) := by positivity
    linarith
  have hUeq : gtBound m d a a' = (m - 1) / (a + a') + 1 := gtBound_bulk_eq hd ha' haa hbulk
  have hK : gtBound m d a a' - 1 = (m - 1) / (a + a') := by
    rw [hUeq, Nat.add_sub_cancel]
  rw [hK, yCut, le_div_iff₀ hsR]
  have h1 : (m - 1) / (a + a') * (a + a') ≤ m :=
    le_trans (Nat.div_mul_le_self _ _) (by omega)
  have h2 : (((m - 1) / (a + a') * (a + a') : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith

end BlockCycleRotation

open BlockCycleRotation in
theorem solution {n : ℕ} (hn : 0 < n) : |G3sum n| ≤ Err n:= by
  refine aggregate_le hn (fun m d a a' => G3term m d a a') fun d hd p hp => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hm0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  obtain ⟨a, a'⟩ := p
  rw [Finset.mem_filter] at hp
  obtain ⟨hpc, hpb⟩ := hp
  have hpb' : d * a * (a + a') ≤ n / d := hpb
  obtain ⟨-, ha1, haa, hgcd⟩ := mem_coprimePairs.1 hpc
  have ha : 0 < a := by omega
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hmR : (1 : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast hm0
  have haleM : a ≤ n / d := by
    refine le_trans ?_ hpb'
    calc a = 1 * a * 1 := by ring
      _ ≤ d * a * (a + a') := Nat.mul_le_mul (Nat.mul_le_mul hd0 (le_refl a)) (by omega)
  have haleMR : (a : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast haleM
  have h := abs_G3term_le hm0 hd0 ha1 haa hgcd hpb'
  -- `|A| + |B|·(U-1) ≤ d·a + 2m/a`
  have hAabs : |aCoeff (n / d) d a| = aCoeff (n / d) d a :=
    abs_of_nonneg (by unfold aCoeff; positivity)
  have hBabs : |bCoeff a a'| = (a' : ℝ) / (a : ℝ) := by
    unfold bCoeff
    rw [abs_div, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a' : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a : ℝ))]
  have hsR : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by
    have h1 : (0 : ℝ) ≤ (a' : ℝ) := by positivity
    have h2 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    linarith
  have hBY : |bCoeff a a'| * yCut (n / d) a a' ≤ ((n / d : ℕ) : ℝ) / (a : ℝ) := by
    rw [hBabs, yCut, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have hma : (0 : ℝ) ≤ ((n / d : ℕ) : ℝ) * (a : ℝ) * (a : ℝ) := by positivity
    nlinarith [hma, Nat.cast_nonneg (α := ℝ) a']
  have hKY := gtBound_sub_one_le_yCut hd0 ha1 haa hpb'
  have hBK : |bCoeff a a'| * ((gtBound (n / d) d a a' - 1 : ℕ) : ℝ)
      ≤ |bCoeff a a'| * yCut (n / d) a a' :=
    mul_le_mul_of_nonneg_left hKY (abs_nonneg _)
  have hW : |aCoeff (n / d) d a| + |bCoeff a a'| * ((gtBound (n / d) d a a' - 1 : ℕ) : ℝ)
      ≤ ((d * a : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (a : ℝ) := by
    rw [hAabs]
    unfold aCoeff
    have hrw : ((n / d : ℕ) : ℝ) / (a : ℝ) + ((n / d : ℕ) : ℝ) / (a : ℝ)
        = 2 * ((n / d : ℕ) : ℝ) / (a : ℝ) := by ring
    linarith [hBK, hBY]
  have hlogle : Real.log (a : ℝ) ≤ Real.log ((n / d : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) haleMR
  have hloga : (0 : ℝ) ≤ Real.log (a : ℝ) := Real.log_nonneg haR
  have hWnn : (0 : ℝ) ≤ ((d * a : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (a : ℝ) := by positivity
  have hnn : (0 : ℝ) ≤ |aCoeff (n / d) d a|
      + |bCoeff a a'| * ((gtBound (n / d) d a a' - 1 : ℕ) : ℝ) := by positivity
  nlinarith [h, hW, hWnn, hlogle, hloga, hnn]
