-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma2b_eventually_leaves_strip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:30.512548+00:00
-- url     : https://prove2.me/submissions/31c1e9e5-d35b-4fa9-b299-62865dcf53e4

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma2a_real_growth
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {z : ℂ} (hz : ¬ OnRealAxis z) :
    ∃ n : ℕ, expIterate n z ∉ centralStrip := by
  by_contra hcontra
  push Not at hcontra
  have hstrip : ∀ n : ℕ, |(expIterate n z).im| ≤ Real.pi / 3 := fun n => hcontra n
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  -- Harrison's key estimate: |Im f^{n+1}| ≥ (2/5) e^{Re f^n} |Im f^n|
  have key : ∀ n : ℕ,
      (2 / 5 : ℝ) * Real.exp ((expIterate n z).re) * |(expIterate n z).im|
        ≤ |(expIterate (n + 1) z).im| := by
    intro n
    have hb : |(expIterate n z).im| ≤ Real.pi / 2 := by
      have := hstrip n; linarith
    have hsin : 2 / Real.pi * |(expIterate n z).im|
        ≤ |Real.sin ((expIterate n z).im)| := Real.mul_abs_le_abs_sin hb
    have hE : (0 : ℝ) < Real.exp ((expIterate n z).re) := Real.exp_pos _
    have h25 : (2 / 5 : ℝ) ≤ 2 / Real.pi := by
      rw [div_le_div_iff₀ (by norm_num) hpi]; linarith
    have heq : |(expIterate (n + 1) z).im|
        = Real.exp ((expIterate n z).re) * |Real.sin ((expIterate n z).im)| := by
      rw [expIterate_succ, Complex.exp_im, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [heq]
    calc (2 / 5 : ℝ) * Real.exp ((expIterate n z).re) * |(expIterate n z).im|
        = Real.exp ((expIterate n z).re) * ((2 / 5 : ℝ) * |(expIterate n z).im|) := by ring
      _ ≤ Real.exp ((expIterate n z).re) * (2 / Real.pi * |(expIterate n z).im|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h25 (abs_nonneg _)) hE.le
      _ ≤ Real.exp ((expIterate n z).re) * |Real.sin ((expIterate n z).im)| :=
            mul_le_mul_of_nonneg_left hsin hE.le
  -- the orbit never becomes real
  have hne : ∀ n : ℕ, (expIterate n z).im ≠ 0 := by
    intro n
    induction n with
    | zero => simpa [expIterate, OnRealAxis] using hz
    | succ n ih =>
        have hpos : 0 < |(expIterate n z).im| := abs_pos.mpr ih
        have hE : (0 : ℝ) < Real.exp ((expIterate n z).re) := Real.exp_pos _
        have hlt : 0 < |(expIterate (n + 1) z).im| :=
          lt_of_lt_of_le (by positivity) (key n)
        intro hc
        rw [hc] at hlt
        simp at hlt
  -- Lemma 2a iterated: the real part grows linearly
  have hre : ∀ n : ℕ, z.re + n * (1 - Real.log 2) ≤ (expIterate n z).re := by
    intro n
    induction n with
    | zero => simp [expIterate]
    | succ n ih =>
        have h2a := lemma2a_real_growth (hcontra n)
        rw [← expIterate_succ] at h2a
        push_cast
        linarith
  -- Linear real growth eventually makes the imaginary-part expansion factor exceed two.
  have hlog2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hlogpos : (0 : ℝ) < 1 - Real.log 2 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((Real.log 5 - z.re) / (1 - Real.log 2))
  have hNre : ∀ n : ℕ, N ≤ n → Real.log 5 ≤ (expIterate n z).re := by
    intro n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (Real.log 5 - z.re) / (1 - Real.log 2) < (n : ℝ) := lt_of_lt_of_le hN hcast
    rw [div_lt_iff₀ hlogpos] at h1
    have := hre n
    linarith
  -- past N the imaginary part at least doubles
  have hdouble : ∀ n : ℕ, N ≤ n →
      2 * |(expIterate n z).im| ≤ |(expIterate (n + 1) z).im| := by
    intro n hn
    have hexp : (5 : ℝ) ≤ Real.exp ((expIterate n z).re) := by
      have h := Real.exp_le_exp.mpr (hNre n hn)
      rwa [Real.exp_log (by norm_num)] at h
    have hk := key n
    nlinarith [abs_nonneg ((expIterate n z).im)]
  have hgeom : ∀ d : ℕ,
      2 ^ d * |(expIterate N z).im| ≤ |(expIterate (N + d) z).im| := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        have hidx : N + (d + 1) = (N + d) + 1 := by omega
        have h := hdouble (N + d) (Nat.le_add_right N d)
        rw [hidx]
        calc (2 : ℝ) ^ (d + 1) * |(expIterate N z).im|
            = 2 * (2 ^ d * |(expIterate N z).im|) := by ring
          _ ≤ 2 * |(expIterate (N + d) z).im| := by linarith
          _ ≤ |(expIterate ((N + d) + 1) z).im| := h
  -- Geometric growth of a nonzero imaginary part contradicts the fixed strip height.
  have hposN : 0 < |(expIterate N z).im| := abs_pos.mpr (hne N)
  obtain ⟨d, hd⟩ :=
    pow_unbounded_of_one_lt (Real.pi / 3 / |(expIterate N z).im|) (by norm_num : (1 : ℝ) < 2)
  rw [div_lt_iff₀ hposN] at hd
  have h2 := hgeom d
  have h3 := hstrip (N + d)
  linarith
end ExponentialJuliaSetMisiurewicz
