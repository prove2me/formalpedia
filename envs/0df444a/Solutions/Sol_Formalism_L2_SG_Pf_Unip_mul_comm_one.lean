-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.mul_comm_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:45.109558+00:00
-- url     : https://prove2.me/submissions/13c91754-b65c-4f01-9441-6b8d1ca6ad0c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
variable {lv : ι → ℕ} {T k : ℕ}
variable {J J' : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution {M N : Matrix ι ι K} (h : M * N = 1) : N * M = 1 := by
  first
  | exact mul_eq_one_comm.mp h
  | exact (by
      rw [← Matrix.inv_eq_right_inv h]
      exact Matrix.nonsing_inv_mul M (Matrix.isUnit_det_of_right_inverse h))
end Formalism.L2.SG.Pf.Unip
