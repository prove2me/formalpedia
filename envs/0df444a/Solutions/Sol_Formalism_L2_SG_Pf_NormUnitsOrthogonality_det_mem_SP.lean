-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NormUnitsOrthogonality.det_mem_SP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:33:04.059222+00:00
-- url     : https://prove2.me/submissions/45e46362-0358-4131-8982-2998bb1ce254

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinIndOrth
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFSubspace
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DetUnitOfSelfdual
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NormUnitsOrthogonality
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
  Formalism.L2.SG.Pf.UnitPairSolutions
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) :
    G.det ∈ SP K 𝔭 := by
  have e : G.det = (SP K 𝔭).subtype
      (Matrix.det (Matrix.of fun i j => (⟨G i j, hG i j⟩ : SP K 𝔭))) := by
    rw [RingHom.map_det]; rfl
  rw [e]
  exact SetLike.coe_mem _
end Formalism.L2.SG.Pf.NormUnitsOrthogonality
