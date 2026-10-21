-- Prove2me | solution 1 for GaussianMatrix.density_integral_le_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T05:24:53.952367+00:00
-- url     : https://prove2.me/submissions/f4f8fc4d-1264-4e5a-9462-04ac43b538d6

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_integral_power_exp_le
import Theorems.Thm_GaussianMatrix_tw_gamma_ratio_bound
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

theorem solution {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
      (2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
        / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
        * x ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-x / 2))
      ≤ ENNReal.ofReal ((1 / Real.Gamma ((k : ℝ) - r + 2))
        * (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)) := by
  set c : ℝ := (2 : ℝ) ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
      / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1)) with hc
  set a : ℝ := ((k : ℝ) - r - 1) / 2 with ha
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrk' : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hG1 : 0 < Real.Gamma (((k : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma ((r : ℝ) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG3 : 0 < Real.Gamma ((k : ℝ) - r + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hcp : 0 ≤ c := by
    rw [hc]
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (le_of_lt hG1))
      (le_of_lt (mul_pos hG2 hG3))
  have hC : 0 < c := by
    rw [hc]
    positivity
  have ha1 : -1 < a := by rw [ha]; linarith
  have ham1 : a + 1 = ((k : ℝ) - r + 1) / 2 := by rw [ha]; ring
  have hepos : 0 < ((k : ℝ) - r + 1) / 2 := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) - r + 1 := by linarith
    linarith
  have hGamma : Real.Gamma ((k : ℝ) - r + 2)
      = ((k : ℝ) - r + 1) * Real.Gamma ((k : ℝ) - r + 1) := by
    have hne : (k : ℝ) - r + 1 ≠ 0 := by linarith
    have h1 := Real.Gamma_add_one hne
    convert h1 using 1 <;> ring
  have hcC : c ≤ (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)
      / (2 * Real.Gamma ((k : ℝ) - r + 1)) := by
    rw [hc]
    exact tw_gamma_ratio_bound hr hrk
  have hpow2 : (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)
        * t ^ (((k : ℝ) - r + 1) / 2)
      = (t * (((k : ℝ) + r) / 2)) ^ (((k : ℝ) - r + 1) / 2) := by
    have h1 : 0 ≤ t := ht.le
    have h2 : 0 ≤ ((k : ℝ) + r) / 2 := by positivity
    rw [Real.mul_rpow h1 h2]
    ring
  have hnn : 0 ≤ t ^ (((k : ℝ) - r + 1) / 2) := Real.rpow_nonneg ht.le _
  have hGne : Real.Gamma ((k : ℝ) - r + 1) ≠ 0 := ne_of_gt hG3
  have hscalar : c * (t ^ (((k : ℝ) - r + 1) / 2) / (((k : ℝ) - r + 1) / 2))
      ≤ (1 / Real.Gamma ((k : ℝ) - r + 2))
        * (t * (((k : ℝ) + r) / 2)) ^ (((k : ℝ) - r + 1) / 2) := by
    calc c * (t ^ (((k : ℝ) - r + 1) / 2) / (((k : ℝ) - r + 1) / 2))
        ≤ (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)
            / (2 * Real.Gamma ((k : ℝ) - r + 1))
            * (t ^ (((k : ℝ) - r + 1) / 2) / (((k : ℝ) - r + 1) / 2)) :=
          mul_le_mul_of_nonneg_right hcC (div_nonneg hnn (le_of_lt hepos))
      _ = (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)
            * t ^ (((k : ℝ) - r + 1) / 2)
            / ((k : ℝ) - r + 1) / Real.Gamma ((k : ℝ) - r + 1) := by
        field_simp
      _ = (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)
            * t ^ (((k : ℝ) - r + 1) / 2) / Real.Gamma ((k : ℝ) - r + 2) := by
        rw [hGamma]
        field_simp
      _ = (t * (((k : ℝ) + r) / 2)) ^ (((k : ℝ) - r + 1) / 2)
            / Real.Gamma ((k : ℝ) - r + 2) := by
        rw [hpow2]
      _ = (1 / Real.Gamma ((k : ℝ) - r + 2))
            * (t * (((k : ℝ) + r) / 2)) ^ (((k : ℝ) - r + 1) / 2) := by
        field_simp
  -- pull the constant out of the lower Lebesgue integral
  have hmeas : MeasurableSet (Set.Ioc (0 : ℝ) t) := measurableSet_Ioc
  have hgn : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ a * Real.exp (-x / 2))) := by
    fun_prop
  have hsplit : ∀ x ∈ Set.Ioc (0 : ℝ) t,
      ENNReal.ofReal (c * (x ^ a * Real.exp (-x / 2)))
        = ENNReal.ofReal c * ENNReal.ofReal (x ^ a * Real.exp (-x / 2)) := by
    intro x hx
    rw [ENNReal.ofReal_mul hcp]
  have hconst : (∫⁻ x in Set.Ioc (0 : ℝ) t, ENNReal.ofReal
        (c * (x ^ a * Real.exp (-x / 2))))
      = ENNReal.ofReal c * (∫⁻ x in Set.Ioc (0 : ℝ) t,
        ENNReal.ofReal (x ^ a * Real.exp (-x / 2))) := by
    have h1 : (∫⁻ x in Set.Ioc (0 : ℝ) t, ENNReal.ofReal
          (c * (x ^ a * Real.exp (-x / 2))))
        = (∫⁻ x in Set.Ioc (0 : ℝ) t,
            (fun x : ℝ => ENNReal.ofReal c
              * ENNReal.ofReal (x ^ a * Real.exp (-x / 2))) x) :=
      MeasureTheory.setLIntegral_congr_fun hmeas hsplit
    have hset : (∫⁻ x in Set.Ioc (0 : ℝ) t,
            (fun x : ℝ => ENNReal.ofReal c
              * ENNReal.ofReal (x ^ a * Real.exp (-x / 2))) x)
          = ∫⁻ x, (fun x : ℝ => ENNReal.ofReal c
              * ENNReal.ofReal (x ^ a * Real.exp (-x / 2))) x
            ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)) := rfl
    rw [h1, hset]
    exact MeasureTheory.lintegral_const_mul (ENNReal.ofReal c) hgn
  -- the power-exponential bound
  have hile : ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (x ^ a * Real.exp (-x / 2))
      ≤ ENNReal.ofReal (t ^ (a + 1) / (a + 1)) :=
    integral_power_exp_le (a := a) ha1 (t := t) ht.le
  -- assemble
  have hmain : ∫⁻ x in Set.Ioc (0 : ℝ) t, ENNReal.ofReal
      (c * (x ^ a * Real.exp (-x / 2)))
      ≤ ENNReal.ofReal (c * (t ^ (a + 1) / (a + 1))) := by
    rw [hconst]
    have hnonneg : (0 : ENNReal) ≤ ENNReal.ofReal c :=
      le_of_lt (ENNReal.ofReal_pos.mpr hC)
    have hofReal : ENNReal.ofReal (c * (t ^ (a + 1) / (a + 1)))
        = ENNReal.ofReal c * ENNReal.ofReal (t ^ (a + 1) / (a + 1)) :=
      ENNReal.ofReal_mul (by linarith)
    rw [hofReal]
    exact mul_le_mul_of_nonneg_left hile hnonneg
  have hscalar' : c * (t ^ (a + 1) / (a + 1))
      ≤ (1 / Real.Gamma ((k : ℝ) - r + 2))
        * (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2) := by
    rw [ham1]
    have heq : t * (((k : ℝ) + r) / 2) = t * ((k : ℝ) + r) / 2 := by ring
    rw [← heq]
    exact hscalar
  have hmain2 : ENNReal.ofReal (c * (t ^ (a + 1) / (a + 1)))
      ≤ ENNReal.ofReal ((1 / Real.Gamma ((k : ℝ) - r + 2))
        * (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)) :=
    ENNReal.ofReal_le_ofReal hscalar'
  -- put the target back together
  have hLHS : ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
      (2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
        / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
        * x ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-x / 2))
      = ∫⁻ x in Set.Ioc (0 : ℝ) t, ENNReal.ofReal
        (c * (x ^ a * Real.exp (-x / 2))) := by
    congr 1
    funext x
    rw [hc, ha]
    ring
  rw [hLHS]
  exact hmain.trans hmain2
