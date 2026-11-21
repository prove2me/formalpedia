-- Prove2me | solution 1 for Champernowne.countOccurrences_champPrefix_sub_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:33.826298+00:00
-- url     : https://prove2.me/submissions/189c2b14-b853-4937-b5ef-02c17b02c2f9

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Theorems.Thm_Champernowne_base_pow_count_le
public import Theorems.Thm_Champernowne_le_base_pow_count
public import Theorems.Thm_Champernowne_tendsto_err_div_pow

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    (fun n => (countOccurrences w (champPrefix b n) : ℝ) - n / (b : ℝ) ^ w.length)
      =o[atTop] (fun n => (n : ℝ)) := by
  have hbR : (0 : ℝ) < (b : ℝ) ^ w.length := by positivity
  have hb1R : (1 : ℝ) ≤ (b : ℝ) ^ w.length := by
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_of_lt hb
    exact one_le_pow₀ this
  have hEo : (fun n => (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ))
      =o[atTop] (fun n => (n : ℝ)) := by
    rw [Asymptotics.isLittleO_iff_tendsto']
    · exact tendsto_err_div_pow hb w
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn h0
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact absurd h0 (ne_of_gt this)
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hEo
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [base_pow_count_le hb hw hwne, le_base_pow_count hb hw hwne]
    with n h1 h2
  -- Widen the lower transfer's error b^k·… to the upper's b^(2k)·… (ℕ level).
  have h2' : n ≤ b ^ w.length * countOccurrences w (champPrefix b n)
      + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n := by
    have hpow : b ^ w.length ≤ b ^ (2 * w.length) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hmul := Nat.mul_le_mul_right (b ^ champM b n)
      (Nat.mul_le_mul_left (7 * (w.length + 1)) hpow)
    omega
  have e1 : (b : ℝ) ^ w.length * countOccurrences w (champPrefix b n)
      ≤ n + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n := by exact_mod_cast h1
  have e2 : (n : ℝ) ≤ (b : ℝ) ^ w.length * countOccurrences w (champPrefix b n)
      + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n := by exact_mod_cast h2'
  have hEpos : (0 : ℝ) ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) :=
    by positivity
  have key : |(b : ℝ) ^ w.length * countOccurrences w (champPrefix b n) - n|
      ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg hEpos,
    show (countOccurrences w (champPrefix b n) : ℝ) - n / (b : ℝ) ^ w.length
      = ((b : ℝ) ^ w.length * countOccurrences w (champPrefix b n) - n) / (b : ℝ) ^ w.length by
        field_simp,
    abs_div, abs_of_pos hbR]
  calc |(b : ℝ) ^ w.length * countOccurrences w (champPrefix b n) - n| / (b : ℝ) ^ w.length
      ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) / (b : ℝ) ^ w.length := by
        exact div_le_div_of_nonneg_right key hbR.le
  _ ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) := by
        rw [div_le_iff₀ hbR]
        exact le_mul_of_one_le_right hEpos hb1R
end Champernowne
