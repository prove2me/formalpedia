-- Prove2me | solution 1 for DeletedPrimes.composite_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:17:32.105341+00:00
-- url     : https://prove2.me/submissions/391a8e75-fd7c-4468-91ec-18f45023f8ed

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
import Theorems.Thm_DeletedPrimes_le_of_forall_small
import Theorems.Thm_DeletedPrimes_le_two_theta2_of_frequently
import Theorems.Thm_DeletedPrimes_meanSq_lower_composite
import Theorems.Thm_DeletedPrimes_kappaK_lt_half
import Theorems.Thm_DeletedPrimes_kappaK_pos
import Theorems.Thm_DeletedPrimes_theta2_nonneg


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) (Q : Quantization S) {k : ℕ} (hk : 1 ≤ k) :
    dim S * kappaK k (dim S) ≤ 2 * theta2 S := by
  set α := dim S with hαdef
  have hθ0 := theta2_nonneg S
  have hkap := kappaK_lt_half hk hα0 hα1
  by_cases hθα : α ≤ theta2 S
  · nlinarith [kappaK_pos hk hα0 hα1]
  push Not at hθα
  obtain ⟨m, hm1, hM⟩ := Q hθα
  have hm : (0 : ℝ) < m := by exact_mod_cast hm1
  have hκ : ∀ κ : ℝ, 0 < κ → κ < kappaK k α → κ * α ≤ 2 * theta2 S := by
    intro κ hκ0 hκ
    obtain ⟨η₀, hη₀, h⟩ := meanSq_lower_composite hα0 hα1 F hm hM hk hκ0 hκ
    apply le_of_forall_small hκ0 hη₀
    intro η hη hηlt
    obtain ⟨c, hc, hfr⟩ := h η hη hηlt
    exact le_two_theta2_of_frequently hc hfr
  by_contra hlt; push Not at hlt
  set κ := (2 * theta2 S / α + kappaK k α) / 2 with hκdef
  have hlt' : 2 * theta2 S / α < kappaK k α := by rw [div_lt_iff₀ hα0]; linarith
  have hκ0 : 0 < κ := by
    have : 0 ≤ 2 * theta2 S / α := div_nonneg (by linarith) hα0.le
    rw [hκdef]; linarith
  have hκ1 : κ < kappaK k α := by rw [hκdef]; linarith
  have h1 := hκ κ hκ0 hκ1
  have h2 : 2 * theta2 S < κ * α := by
    have : 2 * theta2 S / α < κ := by rw [hκdef]; linarith
    rw [div_lt_iff₀ hα0] at this; linarith
  linarith
end DeletedPrimes
