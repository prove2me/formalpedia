-- Prove2me | solution 1 for BlockCycleRotation.psi_rat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:58:31.804972+00:00
-- url     : https://prove2.me/submissions/84e299ea-0e1c-42f1-ad0c-c26ac30894d0

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_remSum_congr_mod
import Theorems.Thm_BlockCycleRotation_psi_eq
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

/-- The defining recursion, in the form we actually use. -/
theorem remSum_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    remSum n k = k + remSum k (n % k) := by
  rw [remSum]; simp [hk]

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

/-- The step of the algorithm's recursion agrees with the Euclidean step. -/
theorem remSum_step {k r : ℕ} : remSum (k + r) r = remSum k r :=
  remSum_congr_mod (by simp [Nat.add_mod_right])

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem Inn_zero : Inn 0 = 0 := by simp [Inn]

theorem psi_zero : psi 0 = 0 := by
  unfold psi
  have h : ∀ i, psiTerm 0 i = 0 := by
    intro i
    unfold psiTerm
    have : Inn^[i] (0 : ℝ) = 0 := by
      induction i with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih, Inn_zero]
    rw [this, mul_zero]
  simp [h]

theorem floor_nat_div {n k : ℕ} (hk : 0 < k) : ⌊(n : ℝ) / (k : ℝ)⌋ = ((n / k : ℕ) : ℤ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : (((n / k : ℕ) : ℤ) : ℝ) ≤ (n : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hkR, Int.cast_natCast]
    have h : k * (n / k) ≤ n := Nat.mul_div_le n k
    have hc : ((k * (n / k) : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_mul] at hc
    linarith
  have h2 : (n : ℝ) / (k : ℝ) < (((n / k : ℕ) : ℤ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hkR, Int.cast_natCast]
    have hd : k * (n / k) + n % k = n := Nat.div_add_mod n k
    have hm : n % k < k := Nat.mod_lt _ hk
    have h : n < k * (n / k + 1) := by
      have h3 : k * (n / k + 1) = k * (n / k) + k := by ring
      omega
    have hc : ((n : ℕ) : ℝ) < ((k * (n / k + 1) : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hc
    linarith
  exact Int.floor_eq_iff.2 ⟨h1, h2⟩

theorem fract_nat_div {n k : ℕ} (hk : 0 < k) :
    Int.fract ((n : ℝ) / (k : ℝ)) = ((n % k : ℕ) : ℝ) / (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [Int.fract, floor_nat_div hk, Int.cast_natCast]
  have h : k * (n / k) + n % k = n := Nat.div_add_mod n k
  have hR : (k : ℝ) * ((n / k : ℕ) : ℝ) + ((n % k : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast h
  field_simp
  linarith

theorem one_div_nat_div {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    1 / ((k : ℝ) / (n : ℝ)) = (n : ℝ) / (k : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  field_simp

theorem Outt_rat {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    Outt ((k : ℝ) / (n : ℝ)) = ((k + n % k : ℕ) : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hne : (k : ℝ) / (n : ℝ) ≠ 0 := by positivity
  unfold Outt
  rw [if_neg hne, one_div_nat_div hn hk, fract_nat_div hk]
  push_cast
  field_simp

theorem Inn_rat {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    Inn ((k : ℝ) / (n : ℝ)) = ((n % k : ℕ) : ℝ) / ((k + n % k : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hne : (k : ℝ) / (n : ℝ) ≠ 0 := by positivity
  unfold Inn
  rw [if_neg hne, one_div_nat_div hn hk, fract_nat_div hk]
  push_cast
  field_simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The bridge.**  `n·ψ(k/n) = 2·remSum(n,k)` for `2k ≤ n`. -/
theorem solution : ∀ k : ℕ, ∀ n : ℕ, 0 < n → 2 * k ≤ n →
    (n : ℝ) * psi ((k : ℝ) / (n : ℝ)) = 2 * (remSum n k : ℝ):= by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hn hkn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [psi_zero]
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hx0 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
      have hx : (k : ℝ) / (n : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hnR (by norm_num)]
        have : ((2 * k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
        push_cast at this
        linarith
      set k' := n % k with hk'
      set n' := k + k' with hn'
      have hk'k : k' < k := Nat.mod_lt _ hk
      have hn'pos : 0 < n' := by omega
      have hn'R : (0 : ℝ) < (n' : ℝ) := by exact_mod_cast hn'pos
      have hIH : (n' : ℝ) * psi ((k' : ℝ) / (n' : ℝ)) = 2 * (remSum n' k' : ℝ) :=
        ih k' hk'k n' hn'pos (by omega)
      rw [psi_eq hx0 hx, Outt_rat hn hk, Inn_rat hn hk]
      have hcast : ((k + n % k : ℕ) : ℝ) = (n' : ℝ) := by rw [hn', hk']
      have hcast2 : ((n % k : ℕ) : ℝ) = (k' : ℝ) := by rw [hk']
      rw [hcast, hcast2]
      have hstep : remSum n' k' = remSum k k' := remSum_step
      have hrec : remSum n k = k + remSum k k' := by
        rw [remSum_of_pos n hk.ne', hk']
      rw [hrec]
      push_cast
      have hexp : (n : ℝ) * (2 * ((k : ℝ) / (n : ℝ))
          + (n' : ℝ) / (n : ℝ) * psi ((k' : ℝ) / (n' : ℝ)))
          = 2 * (k : ℝ) + (n' : ℝ) * psi ((k' : ℝ) / (n' : ℝ)) := by
        field_simp
      rw [hexp, hIH, hstep]
      ring
