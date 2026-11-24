-- Prove2me | solution 1 for DeletedPrimes.floor_of_forall_k
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:07:00.5528+00:00
-- url     : https://prove2.me/submissions/d0dbead5-5bde-450e-a36c-65476fbdb1f8

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
import Theorems.Thm_DeletedPrimes_tendsto_kappaK

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α θ : ℝ} (h1 : α < 1)
    (h : ∀ k : ℕ, 1 ≤ k → α * kappaK k α ≤ 2 * θ) : α / 2 * min (1 / 2) (1 - α) ≤ θ := by
  have hlim := (tendsto_kappaK h1).const_mul α
  have : α * min (1 / 2) (1 - α) ≤ 2 * θ :=
    le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun k hk => h k hk⟩)
  linarith
end DeletedPrimes
