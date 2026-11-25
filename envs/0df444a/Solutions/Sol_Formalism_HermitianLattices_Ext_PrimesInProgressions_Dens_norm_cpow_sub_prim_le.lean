-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_cpow_sub_prim_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:57:07.534023+00:00
-- url     : https://prove2.me/submissions/8eadad01-78b5-4ab3-a8d5-b349326dae45

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_cpow_neg_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution {i : ℕ} (hi : 1 ≤ i) {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 - w ≠ 0) :
    ‖((i + 1 : ℕ) : ℂ) ^ (-w) - (((i + 1 : ℕ) : ℂ) ^ (1 - w) - (i : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      ‖w‖ / i := by
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hi0 : (0 : ℝ) < i := by linarith
  have hle : (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc (i : ℝ) ((i : ℝ) + 1) := by
    rw [Set.uIcc_of_le hle]; intro h; linarith [h.1]
  have hr : -w ≠ -1 := by
    intro h; apply hw1; linear_combination h
  have hint := integral_cpow (a := (i : ℝ)) (b := (i : ℝ) + 1) (r := -w) (Or.inr ⟨hr, h0⟩)
  have e : -w + 1 = 1 - w := by ring
  have e1 : (((i : ℝ) : ℂ)) = (i : ℂ) := by push_cast; rfl
  have e2 : ((((i : ℝ) + 1 : ℝ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [e, e1, e2] at hint
  set c : ℂ := ((i + 1 : ℕ) : ℂ) ^ (-w) with hc
  have hconst : ∫ _x : ℝ in (i : ℝ)..((i : ℝ) + 1), c = c := by
    rw [intervalIntegral.integral_const]; simp
  have hsub : c - (((i + 1 : ℕ) : ℂ) ^ (1 - w) - (i : ℂ) ^ (1 - w)) / (1 - w) =
      ∫ x : ℝ in (i : ℝ)..((i : ℝ) + 1), (c - (x : ℂ) ^ (-w)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_cpow (Or.inr h0)), hconst, hint]
  rw [hsub]
  have hb : ∀ x ∈ Set.uIoc (i : ℝ) ((i : ℝ) + 1), ‖c - (x : ℂ) ^ (-w)‖ ≤ ‖w‖ / i := by
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    have hx1 : 1 ≤ x := by linarith [hx.1]
    have hx0 : 0 < x := by linarith
    have h := norm_cpow_neg_sub_le (a := x) (b := (i : ℝ) + 1) hx1 hx.2 hw
    rw [e2] at h
    refine h.trans ?_
    have : ((i : ℝ) + 1 - x) / x ≤ 1 / i :=
      div_le_div₀ zero_le_one (by linarith [hx.1]) hi0 hx.1.le
    calc ‖w‖ * (((i : ℝ) + 1 - x) / x) ≤ ‖w‖ * (1 / i) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖w‖ / i := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
