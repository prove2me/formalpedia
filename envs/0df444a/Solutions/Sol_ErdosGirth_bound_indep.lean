-- Prove2me | solution 1 for ErdosGirth.bound_indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:33.567157+00:00
-- url     : https://prove2.me/submissions/1014e0d4-8522-4dec-815e-48e19df39093

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Theorems.Thm_ErdosGirth_two_mul_pow_le_exp

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution (a q t : ℕ) (hq : 6 * 2 ^ (a + 3) * (a + 3).factorial ≤ q)
    (ht : t = q ^ (a + 1)) (m : ℝ) (hm0 : 0 ≤ m) (hm2 : m ≤ ((q : ℝ) + 1) ^ (a + 2)) :
    m ^ t * (1 - 1 / (q : ℝ) ^ a) ^ t.choose 2 ≤ 1 / 2 := by
  have hq1n : 1 ≤ q := le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1n
  have hqa : (1 : ℝ) ≤ (q : ℝ) ^ a := one_le_pow₀ hq1
  set p : ℝ := 1 / (q : ℝ) ^ a with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one (by positivity)]; exact hqa
  have ht1 : 1 ≤ t := by rw [ht]; exact Nat.one_le_pow _ _ hq1n
  have hexp1 : (1 - p) ^ t.choose 2 ≤ Real.exp (t.choose 2 * -p) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) _
  have hpt : (q : ℝ) - 1 ≤ p * ((t : ℝ) - 1) := by
    have : p * ((t : ℝ) - 1) = q - p := by
      rw [hp, ht]; push_cast; field_simp; ring
    rw [this]; linarith
  set b : ℝ := m * Real.exp (-p * ((t : ℝ) - 1) / 2) with hb
  have hb0 : 0 ≤ b := by positivity
  have hbb : b ≤ 1 / 2 := by
    have h2 := two_mul_pow_le_exp a q hq
    calc b ≤ ((q : ℝ) + 1) ^ (a + 2) * Real.exp (-(((q : ℝ) - 1) / 2)) := by
          rw [hb]
          exact mul_le_mul hm2 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
            (by positivity)
      _ ≤ 1 / 2 := by
          rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]; linarith
  calc m ^ t * (1 - p) ^ t.choose 2 ≤ m ^ t * Real.exp (t.choose 2 * -p) := by gcongr
    _ = b ^ t := by
        rw [hb, mul_pow, ← Real.exp_nat_mul, Nat.cast_choose_two]; congr 2; ring
    _ ≤ (1 / 2) ^ t := pow_le_pow_left₀ hb0 hbb t
    _ ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
end ErdosGirth
