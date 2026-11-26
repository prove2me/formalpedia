-- Prove2me | solution 1 for EdenVerified.s10_rational_common_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:56.109367+00:00
-- url     : https://prove2.me/submissions/d3b15af7-61f8-4e40-b814-e8f61c7430ad

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_frequency_torus_common_period
import Theorems.Thm_Eden_frequency_torus_not_equilibrium


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (a b : ℕ) (_ha : 0 < a) (hb : 0 < b)
    (p : PhaseSpace) (hp : p ∈ torus) :
    0 < 2 * Real.pi * b ∧
    Function.Periodic (fun t : ℝ => frequencyEvolution c ((a : ℝ)/(b : ℝ)) t p)
      (2 * Real.pi * b) ∧
    frequencyVectorField c ((a : ℝ)/(b : ℝ)) p ≠ 0 := by
  have h := frequency_torus_common_period c (a := (a : ℤ)) hb
    (show (a : ℝ)/(b : ℝ) = ((a : ℤ) : ℝ)/(b : ℝ) by rw [Int.cast_natCast]) hp
  exact ⟨h.1, h.2, frequency_torus_not_equilibrium c _ hp⟩
end EdenVerified
