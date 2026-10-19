-- Prove2me | solution 1 for CohnElkies.unitBallVolume_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/dbce5d48-5254-441b-a83c-2b66750dea16

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution (k : ℕ) :
    unitBallVolume (2 * k + 1) =
      Real.pi ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ) := by
  have hhalf :
      ((↑(2 * k + 1) : ℝ) / 2) = (k : ℝ) + 1 / 2 := by
    push_cast
    ring
  have hgamma :
      Real.Gamma (((↑(2 * k + 1) : ℝ) / 2) + 1) =
        ((2 * k + 1)‼ : ℝ) * Real.sqrt Real.pi /
          (2 : ℝ) ^ (k + 1) := by
    rw [hhalf]
    convert! Real.Gamma_nat_add_one_add_half k using 1; ring_nf
  have hpi :
      Real.pi ^ (((2 * k + 1 : ℕ) : ℝ) / 2) =
        Real.pi ^ k * Real.sqrt Real.pi := by
    rw [hhalf, Real.rpow_add Real.pi_pos,
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hdouble : (0 : ℝ) < ((2 * k + 1)‼ : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos (2 * k + 1)
  unfold unitBallVolume
  rw [hpi, hgamma]
  field_simp
end CohnElkies
