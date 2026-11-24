-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.partial_tendsto_G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:55.571728+00:00
-- url     : https://prove2.me/submissions/a2110da1-128e-414d-912a-fd25da591590

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_summable_dterm
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_partial_identity
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_partial_identity
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_summable_dterm

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
private lemma norm_Ap_mul_succ_cpow_neg_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) (s : ℂ) (M : ℕ) :
    ‖Ap f M * ((M : ℂ) + 1) ^ (-s)‖ ≤ B * ((M : ℝ) + 1) ^ (-s.re) := by
  have e : ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) := by simp
  rw [norm_mul, e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (hB M) (Real.rpow_nonneg (by positivity) _)
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
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s)) atTop (𝓝 (G f s)) := by
  have e : (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s)) =
      fun M => ∑ n ∈ Finset.range (M + 1), dterm f s n + Ap f M * ((M : ℂ) + 1) ^ (-s) :=
    funext fun M => (partial_identity f s M).symm
  rw [e, ← add_zero (G f s)]
  refine Filter.Tendsto.add ?_ ?_
  · exact ((summable_dterm f hB hs).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  · have h3 : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h4 := ((tendsto_rpow_neg_atTop hs).comp h3).const_mul B
    rw [mul_zero] at h4
    exact squeeze_zero_norm (norm_Ap_mul_succ_cpow_neg_le f hB s) h4
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
