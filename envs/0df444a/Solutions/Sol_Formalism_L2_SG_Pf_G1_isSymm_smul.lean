-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.isSymm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:32.32533+00:00
-- url     : https://prove2.me/submissions/9fd6c2cb-4c0f-493f-9ae4-2d44826e2ce5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_G1_smul_apply__0d8f4fa04092
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K}
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {c : K} (hc : star c = c) :
    (c • h).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [smul_apply', smul_apply', map_mul, hs.eq x y, starRingEnd_apply, hc]
end Formalism.L2.SG.Pf.G1
