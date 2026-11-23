-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_one_sub_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:30.000823+00:00
-- url     : https://prove2.me/submissions/ad4042df-3a94-4e46-ba64-2e92bba2f491

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
theorem _root_.solution {a : ℝ} (ha : 0 < a) : a / (1 + a) ≤ 1 - Real.exp (-a) := by
  have hpos : 0 < 1 + a := by linarith
  have h4 : Real.exp (-a) * (1 + a) ≤ 1 := by
    calc Real.exp (-a) * (1 + a) ≤ Real.exp (-a) * Real.exp a :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp a]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [div_le_iff₀ hpos]
  have e : (1 - Real.exp (-a)) * (1 + a) = (1 + a) - Real.exp (-a) * (1 + a) := by ring
  rw [e]; linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
