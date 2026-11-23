-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.rootNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:20.500321+00:00
-- url     : https://prove2.me/submissions/a2babdab-fd65-4e59-8377-3b922e5084db

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_RootNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
theorem _root_.solution (N : ℕ) (_hN : 0 < N) (k : ℕ) : ‖cexp (2 * Real.pi * I / N) ^ k‖ = 1 := by

  rw [norm_pow, (Complex.isPrimitiveRoot_exp N (by omega)).norm'_eq_one (by omega), one_pow]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
