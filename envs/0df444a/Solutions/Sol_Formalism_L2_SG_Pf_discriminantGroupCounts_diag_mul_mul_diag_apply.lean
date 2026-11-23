-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.diag_mul_mul_diag_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:00.005552+00:00
-- url     : https://prove2.me/submissions/2fd59724-7b23-4005-83cd-57dcabe10b6d

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.HermitianLattices.Ext.L3
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantGroupCounts
variable {A : Type*} [CommRing A] [StarRing A]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : m → A}
namespace Formalism.L2.SG.Pf.discriminantGroupCounts
theorem _root_.solution (d : m → A) (T : Matrix m m A) (i j : m) :
    (diagonal d * T * diagonal d) i j = d i * T i j * d j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
end Formalism.L2.SG.Pf.discriminantGroupCounts
