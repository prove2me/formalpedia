-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.norm_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:51.376566+00:00
-- url     : https://prove2.me/submissions/c41471b7-d0e7-4f74-9312-43fa0ff7a6bd

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_dterm_le__f583cacc7f6d
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_summable_dterm
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_summable_dterm
import Theorems.Thm_P2M_Formalism_FX_LFunctionPartialSum_norm_dterm_le__3de663e13059

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
private lemma sum_range_rpow_neg_telescope (σ : ℝ) (N M : ℕ) :
    ∑ i ∈ Finset.range M, ((((i + (N + 1) : ℕ) : ℝ)) ^ (-σ) - ((((i + (N + 1) : ℕ) : ℝ)) + 1) ^ (-σ)) =
      ((N : ℝ) + 1) ^ (-σ) - (((M + N + 1 : ℕ) : ℝ)) ^ (-σ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring_nf
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
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' i, dterm f s (i + (N + 1))‖ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hc : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hsum : Summable (fun i => dterm f s (i + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).2 (summable_dterm f hB hs)
  refine le_of_tendsto' (hsum.hasSum.tendsto_sum_nat.norm) (fun M => ?_)
  calc ‖∑ i ∈ Finset.range M, dterm f s (i + (N + 1))‖
        ≤ ∑ i ∈ Finset.range M, ‖dterm f s (i + (N + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range M, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
          ((((i + (N + 1) : ℕ) : ℝ)) + 1) ^ (-s.re))) :=
        Finset.sum_le_sum fun i _ => norm_dterm_le' f hB hs (by omega)
    _ = B * (‖s‖ / s.re) * (((N : ℝ) + 1) ^ (-s.re) - (((M + N + 1 : ℕ) : ℝ)) ^ (-s.re)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, sum_range_rpow_neg_telescope]
        ring
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
        have h5 : 0 ≤ (((M + N + 1 : ℕ) : ℝ)) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h6 : 0 ≤ B * (‖s‖ / s.re) := mul_nonneg hB0 hc
        nlinarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
