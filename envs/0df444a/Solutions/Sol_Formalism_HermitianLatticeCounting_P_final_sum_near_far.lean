-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.final_sum_near_far
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:46.615321+00:00
-- url     : https://prove2.me/submissions/32152d2d-9f86-4859-aa93-9edeae015131

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : FinalSum := by
  intro c A hc hA
  set c2 := min c 1 with hc2
  have hc20 : 0 < c2 := lt_min hc one_pos
  set L := 2 * Real.log (2 * (1 + 2 * A)) / c2 with hL
  refine ⟨c2 / 2, by positivity, max 3 ⌈L⌉₊, ?_⟩
  intro n f D Ds pr E₁ E₂ hn hf hD hDs hpr hpr2 hE1 hE2 hDeq
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hnL : L ≤ n := Nat.ceil_le.mp ((le_max_right _ _).trans hn)
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hn0 : (0:ℝ) < n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9; linarith
  have hlogn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  set x := (n:ℝ) * f * Real.log n with hx
  have hxn : (n:ℝ) ≤ x := by
    have : (n:ℝ) * 1 * 1 ≤ n * f * Real.log n := by gcongr
    linarith
  have hx0 : 0 ≤ x := by linarith
  set G := Real.exp (-(c2 / 2 * x)) with hG
  have hG0 : 0 < G := Real.exp_pos _
  have hG1 : G ≤ 1 := by
    rw [hG]; apply Real.exp_le_one_iff.mpr
    have : 0 ≤ c2 / 2 * x := by positivity
    linarith
  have hGA : 2 * (1 + 2 * A) * G ≤ 1 := by
    have hp : 0 < 2 * (1 + 2 * A) := by positivity
    have : 2 * (1 + 2 * A) = Real.exp (Real.log (2 * (1 + 2 * A))) := (Real.exp_log hp).symm
    rw [this, hG, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have h1 : L ≤ x := hnL.trans hxn
    rw [hL, div_le_iff₀ hc20] at h1
    linarith
  have he1 : Real.exp (-(c * n * f * Real.log n)) ≤ G * G := by
    rw [hG, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : c2 * x ≤ c * x := by
      apply mul_le_mul_of_nonneg_right (min_le_left _ _) hx0
    have e : c * n * f * Real.log n = c * x := by rw [hx]; ring
    rw [e]; linarith
  have he2 : Real.exp (-((n:ℝ) ^ 2 * f)) ≤ G * G := by
    rw [hG, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : c2 * x ≤ 1 * x := by
      apply mul_le_mul_of_nonneg_right (min_le_right _ _) hx0
    have h2 : x ≤ (n:ℝ) ^ 2 * f := by
      rw [hx]
      calc (n:ℝ) * f * Real.log n ≤ n * f * n := by gcongr
        _ = _ := by ring
    linarith
  have e3 : Real.exp (-(c2 / 2 * n * f * Real.log n)) = G := by
    rw [hG, hx]; congr 1; ring
  rw [e3]
  generalize Real.exp (-(c * n * f * Real.log n)) = e1 at *
  generalize Real.exp (-((n:ℝ) ^ 2 * f)) = e2 at *
  have hGG : 0 ≤ G * G := by positivity
  have b1 : |E₁| ≤ A * (G * G) * Ds := hE1.trans (by gcongr)
  have b2 : |E₂| ≤ A * (G * G) * D := hE2.trans (by gcongr)
  have b3 : |Ds * (pr - 1)| ≤ G * G * Ds := by
    rw [abs_mul, abs_of_nonneg hDs, mul_comm]
    apply mul_le_mul_of_nonneg_right _ hDs
    rw [abs_le]; constructor <;> linarith
  have hdiff : D - Ds = Ds * (pr - 1) + E₁ + E₂ := by rw [hDeq]; ring
  have b4 : |D - Ds| ≤ G * G * Ds + A * (G * G) * Ds + A * (G * G) * D := by
    rw [hdiff]
    calc _ ≤ |Ds * (pr - 1) + E₁| + |E₂| := abs_add_le _ _
      _ ≤ |Ds * (pr - 1)| + |E₁| + |E₂| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith
  have b5 : D ≤ Ds + |D - Ds| := by have := le_abs_self (D - Ds); linarith
  have hAG : A * (G * G) ≤ 1 / 4 := by
    have : A * G ≤ 1 / 4 := by nlinarith
    have h0 : 0 ≤ A * G := by positivity
    nlinarith
  have hAGG0 : 0 ≤ A * (G * G) := by positivity
  have b6 : A * (G * G) * D ≤ A * (G * G) * Ds + 1 / 4 * |D - Ds| := by
    calc A * (G * G) * D ≤ A * (G * G) * (Ds + |D - Ds|) := by gcongr
      _ = A * (G * G) * Ds + A * (G * G) * |D - Ds| := by ring
      _ ≤ _ := by gcongr
  have b7 : |D - Ds| ≤ 2 * (1 + 2 * A) * G * (G * Ds) := by
    have h0 : 0 ≤ G * G * Ds := by positivity
    have h1 : 0 ≤ A * (G * G) * Ds := by positivity
    nlinarith
  calc |D - Ds| ≤ 2 * (1 + 2 * A) * G * (G * Ds) := b7
    _ ≤ 1 * (G * Ds) := by gcongr
    _ = G * Ds := one_mul _
end Formalism.HermitianLatticeCounting.P
