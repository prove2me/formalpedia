-- Prove2me | solution 1 for GDGen3.referenceXi_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:32:24.196422+00:00
-- url     : https://prove2.me/submissions/38c57963-0590-4a22-8f63-ea810d341c82

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_referenceXi_pos

lemma pow_slope_strictMono (z : ℝ) (hz : 1 < z) :
    StrictMono (fun n : ℕ => (z ^ (n + 1) - 1) / ((n : ℝ) + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hsum : (∑ k ∈ range (n + 1), z ^ k) < ((n : ℝ) + 1) * z ^ (n + 1) := by
    calc
      _ < ∑ k ∈ range (n + 1), z ^ (n + 1) := by
        apply sum_lt_sum
        · intro k hk; exact le_of_lt (pow_lt_pow_right₀ hz (mem_range.mp hk))
        · exact ⟨0, by simp, pow_lt_pow_right₀ hz (by omega)⟩
      _ = _ := by simp
  have hm := mul_lt_mul_of_pos_right hsum (by linarith : 0 < z - 1)
  rw [geom_sum_mul] at hm
  apply (div_lt_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)
    (by positivity : 0 < ((n + 1 : ℕ) : ℝ) + 1)).2
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  rw [pow_succ] at hm
  nlinarith

lemma reference_power_bound (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    1 / r ^ i < 1 + (i : ℝ) * (1 + r) := by
  have hz : 1 < 1 / r := (lt_div_iff₀ hr).2 (by simpa using hr1)
  have hs := pow_slope_strictMono (1 / r) hz (by omega : i - 1 < N - 1)
  dsimp at hs
  have hN : 1 ≤ N := by omega
  rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hN] at hs
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  have hcN : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
  rw [hci, hcN, div_pow, div_pow, one_pow, one_pow] at hs
  have hip : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs' := (div_lt_div_iff₀ hip hNp).mp hs
  have hm := mul_le_mul_of_nonneg_left hbranch (le_of_lt hip)
  nlinarith

end GDGen3Proof_referenceXi_pos

open GDGen3Proof_referenceXi_pos

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) : 0 < referenceXi r i := by
  have h := reference_power_bound r hr hr1 N i hi hiN hbranch
  unfold referenceXi
  exact div_pos (by linarith) (by positivity)
