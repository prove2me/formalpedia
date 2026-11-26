-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma4_exists_im_odd_mul_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:46.984108+00:00
-- url     : https://prove2.me/submissions/823fa45c-c1ec-4a8c-bcf6-4643c3309452

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
      2 * Real.pi ≤ |(expIterate n w).im - (expIterate n z).im|) :
    ∃ (n : ℕ) (y : ℂ) (k : ℤ),
      y ∈ V ∧ Odd k ∧ (expIterate n y).im = (k : ℝ) * Real.pi := by
  obtain ⟨n, w, z, hw, hz, hfar⟩ := h
  set F : ℂ → ℝ := fun y => (expIterate n y).im with hF
  have hcont : ContinuousOn F V :=
    (Complex.continuous_im.comp (continuous_expIterate n)).continuousOn
  have hpi : 0 < Real.pi := Real.pi_pos
  have main : ∀ a b : ℂ, a ∈ V → b ∈ V → 2 * Real.pi ≤ F b - F a →
      ∃ (y : ℂ) (k : ℤ), y ∈ V ∧ Odd k ∧ F y = (k : ℝ) * Real.pi := by
    intro a b ha hb hgap
    have hdiv : F a / Real.pi * Real.pi = F a := div_mul_cancel₀ _ (ne_of_gt hpi)
    have hlow0 : F a ≤ ((⌈F a / Real.pi⌉ : ℤ) : ℝ) * Real.pi := by
      have hc := Int.le_ceil (F a / Real.pi)
      have h2 := mul_le_mul_of_nonneg_right hc (le_of_lt hpi)
      rwa [hdiv] at h2
    have hhigh0 : ((⌈F a / Real.pi⌉ : ℤ) : ℝ) * Real.pi < F a + Real.pi := by
      have hc := Int.ceil_lt_add_one (F a / Real.pi)
      have h2 := mul_lt_mul_of_pos_right hc hpi
      rw [add_mul, one_mul, hdiv] at h2
      exact h2
    obtain ⟨k, hkodd, hk1, hk2⟩ :
        ∃ k : ℤ, Odd k ∧ F a ≤ (k : ℝ) * Real.pi ∧ (k : ℝ) * Real.pi ≤ F b := by
      rcases Int.even_or_odd ⌈F a / Real.pi⌉ with hev | hodd
      · refine ⟨⌈F a / Real.pi⌉ + 1, Even.add_one hev, ?_, ?_⟩
        · push_cast
          nlinarith
        · push_cast
          nlinarith
      · exact ⟨⌈F a / Real.pi⌉, hodd, hlow0, by nlinarith⟩
    obtain ⟨y, hy, hyval⟩ :=
      hVconn.isPreconnected.intermediate_value ha hb hcont ⟨hk1, hk2⟩
    exact ⟨y, k, hy, hkodd, hyval⟩
  rcases le_total (F z) (F w) with hle | hle
  · have hgap : 2 * Real.pi ≤ F w - F z := by
      rw [abs_of_nonneg (by linarith)] at hfar; linarith
    obtain ⟨y, k, hy, hodd, hval⟩ := main z w hz hw hgap
    exact ⟨n, y, k, hy, hodd, hval⟩
  · have hgap : 2 * Real.pi ≤ F z - F w := by
      rw [abs_of_nonpos (by linarith)] at hfar; linarith
    obtain ⟨y, k, hy, hodd, hval⟩ := main w z hw hz hgap
    exact ⟨n, y, k, hy, hodd, hval⟩
end ExponentialJuliaSetMisiurewicz
