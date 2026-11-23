-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_pow_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:30.855363+00:00
-- url     : https://prove2.me/submissions/1a1331e9-2df9-4766-8014-e4a961bf3d53

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (m : ℕ) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    b ^ m * (t ^ m * Real.exp (-(b * t))) ≤ (m.factorial : ℝ) := by
  have hx : 0 ≤ b * t := mul_nonneg hb ht
  have hf : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h1 : (b * t) ^ m ≤ Real.exp (b * t) * (m.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (b * t) hx m
    rwa [div_le_iff₀ hf] at h
  calc b ^ m * (t ^ m * Real.exp (-(b * t))) = (b * t) ^ m * Real.exp (-(b * t)) := by
        rw [mul_pow]; ring
    _ ≤ (Real.exp (b * t) * (m.factorial : ℝ)) * Real.exp (-(b * t)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (m.factorial : ℝ) := by
        rw [mul_comm (Real.exp (b * t)), mul_assoc, ← Real.exp_add]; simp
end Formalism.HermitianLattices.Ext.PrimesInProgressions
