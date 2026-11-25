-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G8.isLattice_latW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:12.643835+00:00
-- url     : https://prove2.me/submissions/ee0b2674-3704-46d2-843c-97a7ce18b7b2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFMapSubtype
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GmapEqSelfOfFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IncOInjective
import Theorems.Thm_Formalism_L2_SG_Pf_G8_resF_apply
import Theorems.Thm_Formalism_L2_SG_Pf_G8_map_latW
import Theorems.Thm_Formalism_L2_SG_Pf_G8_incO_injective
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero


attribute [local simp] Formalism.L2.SG.Pf.G8.resF_apply

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G8
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G8
theorem _root_.solution {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) :
    Submodule.IsLattice K (latW W T) := by
  refine ⟨Submodule.fg_of_fg_map_injective _ (incO_injective W) (by rw [map_latW hT]; exact hT.1), ?_⟩
  apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.val_injective
  have himg : (Subtype.val '' ((latW W T : Submodule (𝓞 K) W) : Set W)) = (T : Set V) := by
    have e := congrArg (fun S : Submodule (𝓞 K) V => (S : Set V)) (map_latW hT)
    simpa [Submodule.map_coe] using e
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Submodule.coe_subtype, himg, hT.2]
end Formalism.L2.SG.Pf.G8
