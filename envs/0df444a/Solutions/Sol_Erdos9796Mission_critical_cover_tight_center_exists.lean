-- Prove2me | solution 1 for Erdos9796Mission.critical_cover_tight_center_exists
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-12T20:44:21.453147+00:00
-- url     : https://prove2.me/submissions/854360b5-d1a1-4276-82ef-06fde552c97b

import Definitions.Def_Erdos9796Mission

open Erdos9796Mission
open Classical

theorem solution
    (A : Finset Plane)
    (hcover : ∀ x ∈ A, ∃ p ∈ A.erase x, ∃ r : ℝ,
      0 < r ∧ dist p x = r ∧
      (A.filter (fun q => dist p q = r)).card = 4 ∧
      ∀ s : ℝ, 0 < s →
        4 ≤ (A.filter (fun q => dist p q = s)).card → s = r)
    (x : Plane) (hx : x ∈ A) :
    ∃ p₀ ∈ A, ∃ r₀ : ℝ,
      0 < r₀ ∧ dist p₀ x = r₀ ∧
      (A.filter (fun q => dist p₀ q = r₀)).card = 4 ∧
      ∀ s : ℝ, 0 < s →
        4 ≤ (A.filter (fun q => dist p₀ q = s)).card → s = r₀ := by
  obtain ⟨p, hp, r, h0, hdist, hcard, huniq⟩ := hcover x hx
  exact ⟨p, Finset.mem_of_mem_erase hp, r, h0, hdist, hcard, huniq⟩
