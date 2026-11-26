-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_binomialUpperTail_le_sqrt_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:19.264871+00:00
-- url     : https://prove2.me/submissions/3fdeabfe-6c37-4faf-ba0b-713fe2a59103

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_stirlingCore_ratio_eq_sqrt_exp
import Theorems.Thm_FirstPassageLinearTransport_stirlingSqrtPrefactor_le_of_quarter
import Theorems.Thm_FirstPassageLinearTransport_exists_binomialUpperTail_le_stirlingCore_ratio

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r k : ℕ, 0 < r → 0 < k → k < r →
        (r : ℝ) * (1 / 2 + t₀) ≤ (k : ℝ) →
        (r : ℝ) / 4 ≤ (k : ℝ) →
        (r : ℝ) / 4 ≤ ((r - k : ℕ) : ℝ) →
        (binomialUpperTail r k : ℝ) ≤
          (C / Real.sqrt r) * Real.exp (binomialLogWeight r k) := by
  obtain ⟨C₀, hC₀, htail⟩ :=
    exists_binomialUpperTail_le_stirlingCore_ratio ht₀
  refine ⟨4 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro r k hr hk hkr hgap hkLower hrkLower
  have h := htail r k hr hk hkr hgap
  have h' :
      (binomialUpperTail r k : ℝ) ≤
        C₀ * (stirlingCore r /
          (stirlingCore k * stirlingCore (r - k))) := by
    calc
      (binomialUpperTail r k : ℝ) ≤
          C₀ * stirlingCore r /
            (stirlingCore k * stirlingCore (r - k)) := h
      _ = C₀ * (stirlingCore r /
          (stirlingCore k * stirlingCore (r - k))) := by ring
  rw [stirlingCore_ratio_eq_sqrt_exp hk hkr] at h'
  have hpref := stirlingSqrtPrefactor_le_of_quarter
    hr hk hkr hkLower hrkLower
  have hCnonneg : 0 ≤ C₀ := hC₀.le
  have hexpNonneg : 0 ≤ Real.exp (binomialLogWeight r k) :=
    (Real.exp_pos _).le
  calc
    (binomialUpperTail r k : ℝ) ≤
        C₀ * (Real.sqrt (2 * r) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (r - k))) *
            Real.exp (binomialLogWeight r k)) := h'
    _ ≤ C₀ * ((4 / Real.sqrt r) *
          Real.exp (binomialLogWeight r k)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpref hexpNonneg) hCnonneg
    _ = ((4 * C₀) / Real.sqrt r) *
          Real.exp (binomialLogWeight r k) := by ring
end FirstPassageLinearTransport
