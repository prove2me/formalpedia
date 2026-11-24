-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.mem_tSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:18:38.216921+00:00
-- url     : https://prove2.me/submissions/b6c58fa9-785f-421c-a304-b6101b927850

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_diag_mul_mul_diag_apply

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
theorem _root_.solution (d : m → A) (T : Matrix m m A) : T ∈ tSet d ↔ T ∈ hermD d := by
  show (Tᴴ = T ∧ diagonal d * T * diagonal d = 0) ↔ (Tᴴ = T ∧ ∀ i j, d i * T i j * d j = 0)
  refine and_congr_right fun _ => ?_
  constructor
  · intro h i j
    rw [← diag_mul_mul_diag_apply d T i j, h, Matrix.zero_apply]
  · intro h
    ext i j
    rw [diag_mul_mul_diag_apply, h i j, Matrix.zero_apply]
end Formalism.L2.SG.Pf.discriminantGroupCounts
