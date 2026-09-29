-- Prove2me | solution 1 for Freiman.background_restricted
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:29:53.491701+00:00
-- url     : https://prove2.me/submissions/764dcf90-5b11-4a62-b086-6f6424055581

import Theorems.Thm_Freiman_background_small_digit
import Theorems.Thm_Freiman_background_large_neighbor
import Theorems.Thm_Freiman_background_two_away_small
import Theorems.Thm_Freiman_background_outward_admissible
import Theorems.Thm_Freiman_background_reference_greatest
import Theorems.Thm_Freiman_background_short_tail_bound
import Theorems.Thm_Freiman_background_U_value
import Theorems.Thm_Freiman_background_constant_order

open Freiman

theorem solution (a : ℤ → ℕ+) (ha : ∀ i : ℤ, (a i : ℕ) ≤ 4)
    (h14 : AvoidsBlock a [1,4]) (h41 : AvoidsBlock a [4,1])
    (h31313 : AvoidsBlock a [3,1,3,1,3]) (i : ℤ) (hi : (a i : ℕ) ≤ 3) :
    localValue a i ≤ 4 * Real.sqrt 462 / 19 := by
  have hc := background_constant_order.1
  by_cases hsmall : (a i : ℕ) ≤ 2
  · have hlocal := background_small_digit a i hsmall
    linarith
  have hi3 : (a i : ℕ) = 3 := by omega
  by_cases hneighbor : 2 ≤ (a (i - 1) : ℕ) ∨ 2 ≤ (a (i + 1) : ℕ)
  · have hlocal := background_large_neighbor a i hi hneighbor
    linarith
  have hl1 : (a (i - 1) : ℕ) = 1 := by
    have hp := (a (i - 1)).pos
    omega
  have hr1 : (a (i + 1) : ℕ) = 1 := by
    have hp := (a (i + 1)).pos
    omega
  have hs := background_outward_admissible a i ha h14 h41 h31313 hi3
  have hu : ∀ r : Bool, cfValue (backgroundOutward a i r) ≤
      (2 * Real.sqrt 462 - 28) / 19 := by
    intro r
    obtain ⟨hd, hp, hadm⟩ := hs r
    have h := background_reference_greatest true (backgroundOutward a i r) hd hp hadm
    simpa [backgroundReference, background_U_value] using h
  have hir : ((a i : ℕ) : ℝ) = 3 := by exact_mod_cast hi3
  have hlocal : localValue a i = 3 + cfValue (backgroundOutward a i false) +
      cfValue (backgroundOutward a i true) := by
    dsimp only [localValue, backgroundOutward]
    rw [hir]
    rfl
  obtain hl2 | hr2 := background_two_away_small a i ha h14 h41 h31313 hi3 hl1 hr1
  · obtain ⟨hd, hp, hadm⟩ := hs false
    have h0 : (backgroundOutward a i false 0 : ℕ) = 1 := by
      simpa [backgroundOutward] using hl1
    have h1 : (backgroundOutward a i false 1 : ℕ) ≤ 2 := by
      simpa [backgroundOutward, sub_sub] using hl2
    have hshort := background_short_tail_bound (backgroundOutward a i false) hd hp hadm h0 h1
    rw [hlocal]
    linarith [hu true]
  · obtain ⟨hd, hp, hadm⟩ := hs true
    have h0 : (backgroundOutward a i true 0 : ℕ) = 1 := by
      simpa [backgroundOutward] using hr1
    have h1 : (backgroundOutward a i true 1 : ℕ) ≤ 2 := by
      simpa [backgroundOutward, add_assoc] using hr2
    have hshort := background_short_tail_bound (backgroundOutward a i true) hd hp hadm h0 h1
    rw [hlocal]
    linarith [hu false]
