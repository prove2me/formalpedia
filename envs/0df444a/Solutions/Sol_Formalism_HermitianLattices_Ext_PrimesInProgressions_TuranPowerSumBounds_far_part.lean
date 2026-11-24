-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.far_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:30.970906+00:00
-- url     : https://prove2.me/submissions/b52d7296-516b-484e-bb78-b0bb8b4b3835

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_UbTerms
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_rr_gt


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (a : ℕ) (S : ℝ) (j : ℕ) (hj2 : 2 ≤ j) (hS : S ≤ 1 + j) :
    eps a ^ (j - 2) * S ≤ rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
  have hRpos : 0 < rr a := by linarith [rr_gt a]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  have hinv : eps a ^ k = 1 / rr a ^ k := by
    unfold eps; rw [one_div_pow]
  have hJ0 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hSX : S ≤ (((k + 2 : ℕ) : ℝ) + 1) ^ 2 := by linarith [sq_nonneg ((k + 2 : ℕ) : ℝ)]
  have e : rr a ^ 2 * (((k + 2 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ (k + 2)
      = (((k + 2 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ k := by
    rw [pow_add (rr a) k 2, mul_comm (rr a ^ k) (rr a ^ 2),
      mul_div_mul_left _ _ (pow_ne_zero 2 hRpos.ne')]
  rw [hinv, e, one_div_mul_eq_div]
  gcongr
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
