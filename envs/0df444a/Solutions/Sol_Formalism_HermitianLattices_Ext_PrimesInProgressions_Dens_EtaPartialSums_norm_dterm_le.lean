-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.norm_dterm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:58.326206+00:00
-- url     : https://prove2.me/submissions/54789f7e-0d35-4b61-8989-ba5a2ef619ea

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_dterm_zero
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_dterm_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Filter Topology
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
open Formalism.FX.LFunctionPartialSum
variable (f : ℕ → ℂ)
private lemma natCast_cpow_neg_sub_succ_eq_mul_integral (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s) = s * ∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hne : -s - 1 ≠ -1 := by
    intro h
    apply hs0
    linear_combination -h
  rw [integral_cpow (Or.inr ⟨hne, h0⟩)]
  have e : -s - 1 + 1 = -s := by ring
  rw [e]
  push_cast
  field_simp
  ring
private lemma norm_cpow_neg_sub_succ_le_norm_mul_rpow (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [natCast_cpow_neg_sub_succ_eq_mul_integral s hs n hn, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (n : ℝ) ^ (-s.re - 1)) ?_) (le_of_eq ?_)
  · intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have htp : 0 < t := lt_trans hnpos ht.1
    show ‖(t : ℂ) ^ (-s - 1)‖ ≤ (n : ℝ) ^ (-s.re - 1)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htp]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_nonpos hnpos (le_of_lt ht.1) (by linarith)
  · rw [add_sub_cancel_left, abs_one, mul_one]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
end
end

set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
open Formalism.FX.LFunctionPartialSum
variable (f : ℕ → ℂ)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dterm f s n‖ ≤ B * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dterm_zero, norm_zero]
    exact mul_nonneg hB0 (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · rw [dterm, norm_mul]
    exact mul_le_mul (hB n) (norm_cpow_neg_sub_succ_le_norm_mul_rpow s hs n (by omega)) (norm_nonneg _) hB0
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
