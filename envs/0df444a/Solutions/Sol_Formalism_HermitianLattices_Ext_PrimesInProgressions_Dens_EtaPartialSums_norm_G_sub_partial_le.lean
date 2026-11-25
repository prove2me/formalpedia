-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.norm_G_sub_partial_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:38.224811+00:00
-- url     : https://prove2.me/submissions/de9e0f6c-2d94-4355-9a0d-ddb884f1b7fd

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_summable_dterm
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_partial_identity
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_tail_le
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_natCast_add_one_eq
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_partial_identity
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_summable_dterm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
open Formalism.FX.LFunctionPartialSum
variable (f : ℕ → ℂ)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖G f s - ∑ n ∈ Finset.Icc 1 N, f n * (n : ℂ) ^ (-s)‖ ≤
      B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  rw [← partial_identity f s N]
  have hsum := summable_dterm f hB hs
  have hG : G f s = ∑ n ∈ Finset.range (N + 1), dterm f s n + ∑' i, dterm f s (i + (N + 1)) :=
    (hsum.sum_add_tsum_nat_add (N + 1)).symm
  rw [hG]
  have e : ∑ n ∈ Finset.range (N + 1), dterm f s n + ∑' i, dterm f s (i + (N + 1)) -
      (∑ n ∈ Finset.range (N + 1), dterm f s n + Ap f N * ((N : ℂ) + 1) ^ (-s)) =
      ∑' i, dterm f s (i + (N + 1)) - Ap f N * ((N : ℂ) + 1) ^ (-s) := by ring
  rw [e]
  have h1 := norm_tail_le f hB hs N
  have h2 : ‖Ap f N * ((N : ℂ) + 1) ^ (-s)‖ ≤ B * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB N) (Real.rpow_nonneg (by positivity) _)
  calc ‖∑' i, dterm f s (i + (N + 1)) - Ap f N * ((N : ℂ) + 1) ^ (-s)‖
      ≤ ‖∑' i, dterm f s (i + (N + 1))‖ + ‖Ap f N * ((N : ℂ) + 1) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) + B * ((N : ℝ) + 1) ^ (-s.re) := add_le_add h1 h2
    _ = B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
