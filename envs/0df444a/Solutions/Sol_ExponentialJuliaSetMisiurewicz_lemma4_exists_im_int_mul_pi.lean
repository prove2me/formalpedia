-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma4_exists_im_int_mul_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:50.079443+00:00
-- url     : https://prove2.me/submissions/c693415b-5ab4-4394-9160-97e6c962ef26

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_continuous_expIterate


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {V : Set ℂ} (hVconn : IsConnected V)
    (h : ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      Real.pi ≤ |(expIterate n w).im - (expIterate n z).im|) :
    ∃ (n : ℕ) (y : ℂ) (k : ℤ), y ∈ V ∧ (expIterate n y).im = k * Real.pi := by
  obtain ⟨n, w, z, hw, hz, hfar⟩ := h
  set F : ℂ → ℝ := fun y => (expIterate n y).im with hF
  have hcont : ContinuousOn F V :=
    (Complex.continuous_im.comp (continuous_expIterate n)).continuousOn
  have hpi : 0 < Real.pi := Real.pi_pos
  -- work with the pair in increasing order
  rcases le_total (F z) (F w) with hle | hle
  · have hgap : Real.pi ≤ F w - F z := by
      rw [abs_of_nonneg (by linarith)] at hfar; linarith
    set k : ℤ := ⌈F z / Real.pi⌉ with hk
    have hdiv : F z / Real.pi * Real.pi = F z := div_mul_cancel₀ _ (ne_of_gt hpi)
    have hlow : F z ≤ (k : ℝ) * Real.pi := by
      have hc := Int.le_ceil (F z / Real.pi)
      have h2 := mul_le_mul_of_nonneg_right hc (le_of_lt hpi)
      rwa [hdiv] at h2
    have hhigh : (k : ℝ) * Real.pi ≤ F w := by
      have hc := Int.ceil_lt_add_one (F z / Real.pi)
      have h2 := mul_lt_mul_of_pos_right hc hpi
      rw [add_mul, one_mul, hdiv] at h2
      linarith
    obtain ⟨y, hy, hyval⟩ := hVconn.isPreconnected.intermediate_value hz hw hcont
      ⟨hlow, hhigh⟩
    exact ⟨n, y, k, hy, hyval⟩
  · have hgap : Real.pi ≤ F z - F w := by
      rw [abs_of_nonpos (by linarith)] at hfar; linarith
    set k : ℤ := ⌈F w / Real.pi⌉ with hk
    have hdiv : F w / Real.pi * Real.pi = F w := div_mul_cancel₀ _ (ne_of_gt hpi)
    have hlow : F w ≤ (k : ℝ) * Real.pi := by
      have hc := Int.le_ceil (F w / Real.pi)
      have h2 := mul_le_mul_of_nonneg_right hc (le_of_lt hpi)
      rwa [hdiv] at h2
    have hhigh : (k : ℝ) * Real.pi ≤ F z := by
      have hc := Int.ceil_lt_add_one (F w / Real.pi)
      have h2 := mul_lt_mul_of_pos_right hc hpi
      rw [add_mul, one_mul, hdiv] at h2
      linarith
    obtain ⟨y, hy, hyval⟩ := hVconn.isPreconnected.intermediate_value hw hz hcont
      ⟨hlow, hhigh⟩
    exact ⟨n, y, k, hy, hyval⟩
end ExponentialJuliaSetMisiurewicz
