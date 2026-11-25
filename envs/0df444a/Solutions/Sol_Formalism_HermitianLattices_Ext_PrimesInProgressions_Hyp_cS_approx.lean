-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cS_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:17.015677+00:00
-- url     : https://prove2.me/submissions/d7dd45ce-0716-401c-9766-2f7d0f236db0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
import Theorems.Thm_Formalism_FX_l_function_partial_sum
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_character_sum_Icc_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (hχ : χ ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖DirichletCharacter.LFunction χ 1 - cS χ N‖ ≤ 4 * ((q : ℝ) + 1) / N := by
  have h := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) (Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ)
    1 (by simp) N hN
  have e : Icc 1 N = Ioc 0 N := by ext x; simp; omega
  have e2 : ∑ n ∈ Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-(1 : ℂ)) = cS χ N := by
    rw [e, cS]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.cpow_neg_one, div_eq_mul_inv]
  rw [e2] at h
  have e3 : (N : ℝ) ^ (-(1 : ℂ).re) = (N : ℝ)⁻¹ := by simp [Real.rpow_neg_one]
  rw [e3] at h
  simp only [norm_one, Complex.one_re, div_one] at h
  calc _ ≤ 2 * ((q : ℝ) + 1) * (1 + 1) * (N : ℝ)⁻¹ := h
    _ = 4 * ((q : ℝ) + 1) / N := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
