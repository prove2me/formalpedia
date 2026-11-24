-- Prove2me | solution 1 for DeletedPrimes.prime_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:22:13.780655+00:00
-- url     : https://prove2.me/submissions/d24e018a-0b34-4697-a80d-177c56c50243

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
import Theorems.Thm_DeletedPrimes_meanSq_lower_prime
import Theorems.Thm_DeletedPrimes_le_two_theta2_of_frequently
import Theorems.Thm_DeletedPrimes_kappaK_one
import Theorems.Thm_DeletedPrimes_kappaK_pos
import Theorems.Thm_DeletedPrimes_theta2_nonneg


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) : dim S * kappaOne (dim S) ≤ 2 * theta2 S := by
  set α := dim S
  have hk1 : 0 < kappaOne α := by rw [← kappaK_one]; exact kappaK_pos le_rfl hα0 hα1
  have hκ : ∀ κ : ℝ, 0 < κ → κ < kappaOne α → α * κ ≤ 2 * theta2 S := by
    intro κ hκ0 hκ
    have : ∀ ε : ℝ, 0 < ε → α * κ - ε ≤ 2 * theta2 S := by
      intro ε hε
      obtain ⟨c, hc, hfr⟩ := meanSq_lower_prime hα0 hα1 F hκ0 hκ hε
      exact le_two_theta2_of_frequently hc hfr
    by_contra hlt; push Not at hlt
    have := this ((α * κ - 2 * theta2 S) / 2) (by linarith); linarith
  by_contra hlt; push Not at hlt
  set κ := (2 * theta2 S / α + kappaOne α) / 2 with hκdef
  have hθ0 := theta2_nonneg S
  have hlt' : 2 * theta2 S / α < kappaOne α := by
    rw [div_lt_iff₀ hα0]; linarith
  have hκ0 : 0 < κ := by
    have : 0 ≤ 2 * theta2 S / α := div_nonneg (by linarith) hα0.le
    rw [hκdef]; linarith
  have hκ1 : κ < kappaOne α := by rw [hκdef]; linarith
  have h1 := hκ κ hκ0 hκ1
  have h2 : 2 * theta2 S < α * κ := by
    have : 2 * theta2 S / α < κ := by rw [hκdef]; linarith
    rw [div_lt_iff₀ hα0] at this; linarith
  linarith
end DeletedPrimes
