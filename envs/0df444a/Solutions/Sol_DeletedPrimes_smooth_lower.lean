-- Prove2me | solution 1 for DeletedPrimes.smooth_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:21:56.637811+00:00
-- url     : https://prove2.me/submissions/658cdb88-b79d-49a1-bd7d-9e3e4306b95a

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Smooth
import Theorems.Thm_DeletedPrimes_piS_two_mul
import Theorems.Thm_DeletedPrimes_liAlpha_two_mul_sub

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {α δ c₀ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδα : δ < α)
    (hc₀ : 0 < c₀) (hπ : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |(piS S x : ℝ) - c₀ * liAlpha α x| ≤ C * x ^ δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, c * X ^ α / Real.log X ≤ intervalCount S X := by
  obtain ⟨C, hC⟩ := hπ
  have hC0 : 0 ≤ C := by
    have h := hC 2 le_rfl
    have h2 : (0 : ℝ) < 2 ^ δ := by positivity
    by_contra hneg
    push Not at hneg
    have : C * 2 ^ δ < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [abs_nonneg ((piS S 2 : ℝ) - c₀ * liAlpha α 2)]
  set c := c₀ * 2 ^ (α - 2) / 2 with hcdef
  have hc : 0 < c := by positivity
  set C' := C * (2 ^ δ + 1) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set ε := c / (C' + 1) with hεdef
  have hεpos : 0 < ε := by positivity
  have hCε : C' * ε ≤ c := by
    rw [hεdef, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  have hlog := (isLittleO_log_rpow_atTop (sub_pos.mpr hδα)).bound hεpos
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with X hlX hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg hL.le, Real.norm_of_nonneg (by positivity)] at hlX
  have hN : (intervalCount S X : ℝ) = piS S (2 * X) - piS S X := by
    rw [piS_two_mul (S := S) (by linarith : (1 : ℝ) ≤ X)]; push_cast; ring
  have h1 := hC (2 * X) (by linarith)
  have h2 := hC X hX
  rw [abs_le] at h1 h2
  have h3 := liAlpha_two_mul_sub hα1.le hX
  have e : (2 * X) ^ δ = 2 ^ δ * X ^ δ := Real.mul_rpow (by norm_num) hX0.le
  have h3' : 2 * (c * X ^ α / Real.log X) ≤ c₀ * (liAlpha α (2 * X) - liAlpha α X) := by
    have := mul_le_mul_of_nonneg_left h3 hc₀.le
    calc 2 * (c * X ^ α / Real.log X) = c₀ * (2 ^ (α - 2) * X ^ α / Real.log X) := by
          rw [hcdef]; field_simp
      _ ≤ _ := this
  have hC'e : C' * X ^ δ = C * (2 * X) ^ δ + C * X ^ δ := by rw [hC', e]; ring
  have h4 : 2 * (c * X ^ α / Real.log X) - C' * X ^ δ ≤ (intervalCount S X : ℝ) := by
    rw [hN, hC'e]
    linarith [h1.1, h2.2]
  have e3 : X ^ δ * X ^ (α - δ) = X ^ α := by rw [← Real.rpow_add hX0]; ring_nf
  have h5 : C' * X ^ δ * Real.log X ≤ c * X ^ α := by
    calc C' * X ^ δ * Real.log X ≤ C' * X ^ δ * (ε * X ^ (α - δ)) :=
          mul_le_mul_of_nonneg_left hlX (by positivity)
      _ = (C' * ε) * (X ^ δ * X ^ (α - δ)) := by ring
      _ = (C' * ε) * X ^ α := by rw [e3]
      _ ≤ c * X ^ α := mul_le_mul_of_nonneg_right hCε (by positivity)
  have h6 : C' * X ^ δ ≤ c * X ^ α / Real.log X := by rw [le_div_iff₀ hL]; exact h5
  linarith
end DeletedPrimes
