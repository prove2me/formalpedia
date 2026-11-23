-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.partial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:13.162218+00:00
-- url     : https://prove2.me/submissions/caf02f57-a557-496f-81fe-d4f3cbeba2b0

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_Ap_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_Ap_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_dterm_zero
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_Ap_succ
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_Ap_zero
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_dterm_zero


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
theorem _root_.solution (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), dterm f s n + Ap f M * ((M : ℂ) + 1) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s) := by
  induction M with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero, dterm_zero, Ap_zero, zero_mul, add_zero, add_zero]
    exact (Finset.sum_eq_zero (fun i hi => by rw [Finset.mem_Icc] at hi; omega)).symm
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ← ih, dterm, Ap_succ]
    push_cast
    ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
