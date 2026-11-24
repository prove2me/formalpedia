-- Prove2me | solution 1 for DeletedPrimes.le_two_theta2_of_frequently
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:11:59.143469+00:00
-- url     : https://prove2.me/submissions/1fa04422-5cb3-4c43-8427-e2a94ab7170c

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
import Theorems.Thm_DeletedPrimes_IsMSRegular_mono
import Theorems.Thm_DeletedPrimes_IsRegular_mono
import Theorems.Thm_DeletedPrimes_isMSRegular_of_theta2_lt
import Theorems.Thm_DeletedPrimes_le_of_frequently_rpow_le


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {a c : ℝ} (hc : 0 < c)
    (h : ∃ᶠ X : ℝ in atTop, c * X ^ a ≤ meanSq S X) : a ≤ 2 * theta2 S := by
  have key : ∀ θ' : ℝ, theta2 S < θ' → a ≤ 2 * θ' := by
    intro θ' hθ'
    obtain ⟨C, hC⟩ := isMSRegular_of_theta2_lt hθ'
    apply le_of_frequently_rpow_le hc (C := C)
    refine (h.and_eventually (eventually_ge_atTop 1)).mono fun X ⟨h1, h2⟩ => ?_
    exact le_trans h1 (hC X h2)
  by_contra hlt
  push Not at hlt
  have := key ((theta2 S + a / 2) / 2) (by linarith)
  linarith
end DeletedPrimes
