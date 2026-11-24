-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.pow_small_a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:47.943859+00:00
-- url     : https://prove2.me/submissions/d1cc0c3b-a2f6-469c-8ed3-bfc65f1212db

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
theorem _root_.solution (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) (hK3 : 3 ≤ K) :
    (K : ℝ) * (q ^ 2 / 8) ^ (K - 1) ≤ q ^ K / 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 3 := ⟨K - 3, by omega⟩
  have hB : (1 : ℝ) + (m + 1 : ℕ) * 7 ≤ (1 + 7) ^ (m + 1) := one_add_mul_le_pow (by norm_num) _
  push_cast at hB ⊢
  rw [div_pow, ← pow_mul]
  have h8 : (0 : ℝ) < 8 ^ (m + 2) := by positivity
  have hq' : q ^ (2 * (m + 2)) = q ^ (m + 3) * q ^ (m + 1) := by rw [← pow_add]; congr 1; ring
  have hqm : q ^ (m + 1) ≤ 1 := pow_le_one₀ hq0 hq1
  have hq3 : 0 ≤ q ^ (m + 3) := by positivity
  rw [hq', mul_div_assoc', div_le_div_iff₀ h8 (by norm_num)]
  have : (8 : ℝ) ^ (m + 2) = 8 * 8 ^ (m + 1) := by ring
  rw [this]
  have h1 : ((m : ℝ) + 3) ≤ 8 ^ (m + 1) := by norm_num at hB; linarith
  have h2 : ((m : ℝ) + 3) * (q ^ (m + 3) * q ^ (m + 1)) ≤ ((m : ℝ) + 3) * q ^ (m + 3) := by
    have : 0 ≤ (m : ℝ) + 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hqm hq3]
  nlinarith [mul_le_mul_of_nonneg_right h1 hq3]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
