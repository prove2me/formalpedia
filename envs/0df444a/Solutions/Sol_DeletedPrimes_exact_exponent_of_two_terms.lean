-- Prove2me | solution 1 for DeletedPrimes.exact_exponent_of_two_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:21:41.241386+00:00
-- url     : https://prove2.me/submissions/1d20c4ef-cc11-48b7-bdce-958b06127efe

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
import Theorems.Thm_DeletedPrimes_le_of_frequently_rpow_le


set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {f : ℝ → ℝ} {a c β β' C : ℝ} (hc : c ≠ 0) (hβ' : β' < β)
    (h : ∀ x : ℝ, 1 ≤ x → |f x - a * x - c * x ^ β| ≤ C * x ^ β') :
    (∃ C' : ℝ, ∀ x : ℝ, 1 ≤ x → |f x - a * x| ≤ C' * x ^ β) ∧
    ∀ θ : ℝ, θ < β → ¬ ∃ C' : ℝ, ∀ x : ℝ, 1 ≤ x → |f x - a * x| ≤ C' * x ^ θ := by
  have hC : 0 ≤ C := by
    have := h 1 le_rfl
    simp only [Real.one_rpow, mul_one] at this
    exact le_trans (abs_nonneg _) this
  refine ⟨⟨|c| + C, fun x hx => ?_⟩, fun θ hθ ⟨C', hC'⟩ => ?_⟩
  · have h1 := h x hx
    have h2 : x ^ β' ≤ x ^ β := Real.rpow_le_rpow_of_exponent_le hx hβ'.le
    have h3 : 0 ≤ x ^ β := by positivity
    have e : |f x - a * x| = |(f x - a * x - c * x ^ β) + c * x ^ β| := by congr 1; ring
    rw [e]
    calc |(f x - a * x - c * x ^ β) + c * x ^ β|
        ≤ |f x - a * x - c * x ^ β| + |c * x ^ β| := by
          have h7 := abs_sub (f x - a * x - c * x ^ β) (-(c * x ^ β))
          rwa [sub_neg_eq_add, abs_neg] at h7
      _ ≤ C * x ^ β' + |c| * x ^ β := by rw [abs_mul, abs_of_nonneg h3]; linarith
      _ ≤ (|c| + C) * x ^ β := by nlinarith
  · set m := max θ β' with hm
    have hmβ : m < β := max_lt hθ hβ'
    have hfreq : ∃ᶠ X in atTop, |c| * X ^ β ≤ (|C'| + C) * X ^ m := by
      refine Filter.Eventually.frequently ?_
      filter_upwards [eventually_ge_atTop 1] with x hx
      have h1 := h x hx
      have h2 := hC' x hx
      have h3 : 0 ≤ x ^ β := by positivity
      have hθm : x ^ θ ≤ x ^ m := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
      have hβ'm : x ^ β' ≤ x ^ m := Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ _)
      have hxθ : 0 ≤ x ^ θ := by positivity
      have e : |c| * x ^ β = |c * x ^ β| := by rw [abs_mul, abs_of_nonneg h3]
      have htri : |c * x ^ β| ≤ |f x - a * x| + |f x - a * x - c * x ^ β| := by
        have h6 := abs_sub (f x - a * x) (f x - a * x - c * x ^ β)
        rwa [show f x - a * x - (f x - a * x - c * x ^ β) = c * x ^ β by ring] at h6
      have h4 : C' * x ^ θ ≤ |C'| * x ^ m :=
        calc C' * x ^ θ ≤ |C'| * x ^ θ := mul_le_mul_of_nonneg_right (le_abs_self _) hxθ
          _ ≤ |C'| * x ^ m := mul_le_mul_of_nonneg_left hθm (abs_nonneg _)
      have h5 : C * x ^ β' ≤ C * x ^ m := mul_le_mul_of_nonneg_left hβ'm hC
      rw [e]
      linarith
    have := le_of_frequently_rpow_le (abs_pos.mpr hc) hfreq
    linarith
end DeletedPrimes
