-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.Ap_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:19.912435+00:00
-- url     : https://prove2.me/submissions/6c7b0e64-8e3d-4d72-a0cc-1c3f15f30304

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA

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
theorem _root_.solution (n : ℕ) : Ap f (n + 1) = Ap f n + f (n + 1) := by
  unfold Ap
  exact Finset.sum_Icc_succ_top (by omega) f
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
