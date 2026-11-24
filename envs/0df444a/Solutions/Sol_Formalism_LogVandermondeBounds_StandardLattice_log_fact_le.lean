-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.log_fact_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:37:42.49887+00:00
-- url     : https://prove2.me/submissions/71f63812-9174-44cc-bab5-0ad27d3d180a

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioUpperBoundOfUpperPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution {M k : ℕ} (hM : M - 1 ≤ 2 * k) (hk : 1 ≤ k) :
    Real.log (((M - 1).factorial : ℕ) : ℝ) ≤ 2 * k * Real.log (2 * k) := by
  have h1 : (M - 1).factorial ≤ (2 * k) ^ (2 * k) := by
    calc (M - 1).factorial ≤ (M - 1) ^ (M - 1) := Nat.factorial_le_pow _
      _ ≤ (2 * k) ^ (M - 1) := Nat.pow_le_pow_left hM _
      _ ≤ (2 * k) ^ (2 * k) := Nat.pow_le_pow_right (by omega) hM
  have h2 : (((M - 1).factorial : ℕ) : ℝ) ≤ (2 * (k : ℝ)) ^ (2 * k) := by exact_mod_cast h1
  have hpos : (0 : ℝ) < ((M - 1).factorial : ℕ) := by exact_mod_cast Nat.factorial_pos _
  calc Real.log _ ≤ Real.log ((2 * (k : ℝ)) ^ (2 * k)) := Real.log_le_log hpos h2
    _ = 2 * k * Real.log (2 * k) := by rw [Real.log_pow]; push_cast; ring
end Formalism.LogVandermondeBounds.StandardLattice
