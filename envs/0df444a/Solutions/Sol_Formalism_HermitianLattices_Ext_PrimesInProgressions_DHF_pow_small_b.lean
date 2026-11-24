-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.pow_small_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:48.322778+00:00
-- url     : https://prove2.me/submissions/662c8e3e-8341-4e0c-8648-89692b8bd86c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
theorem _root_.solution (q : ℝ) (hq0 : 0 ≤ q) (K : ℕ) (hK3 : 3 ≤ K) :
    (K : ℝ) * (q / 4) ^ K ≤ q ^ K / 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 3 := ⟨K - 3, by omega⟩
  have hB : (1 : ℝ) + (m : ℕ) * 3 ≤ (1 + 3) ^ m := one_add_mul_le_pow (by norm_num) _
  rw [div_pow]
  have h4 : (4 : ℝ) ^ (m + 3) = 64 * 4 ^ m := by ring
  rw [h4]
  have hq3 : 0 ≤ q ^ (m + 3) := by positivity
  have h4p : (0 : ℝ) < 4 ^ m := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  push_cast
  norm_num at hB
  have : ((m : ℝ) + 3) * 8 ≤ 64 * 4 ^ m := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hq3]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
