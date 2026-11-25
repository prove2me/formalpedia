-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NormUnitsOrthogonality.NU.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:19.205075+00:00
-- url     : https://prove2.me/submissions/a1d89ce0-deb6-4bb7-b48b-ce395ddfc20a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DualFormInverse
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinIndOrth
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



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NormUnitsOrthogonality
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]
namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality
namespace NU
theorem _root_.solution {x : K} (hx : NU 𝔭 x) : NU 𝔭 x⁻¹ := by
  obtain ⟨a, ha, h1, h2⟩ := hx
  have hs : star a⁻¹ = (star a)⁻¹ := by
    first | exact star_inv₀ a | exact star_inv' a | simp
  have e : x⁻¹ * (a⁻¹ * star a⁻¹) = (x * (a * star a))⁻¹ := by
    rw [hs, mul_inv, mul_inv]
  refine ⟨a⁻¹, inv_ne_zero ha, ?_, ?_⟩
  · rw [e]
    exact h2
  · rw [e, inv_inv]
    exact h1
end NU
end Formalism.L2.SG.Pf.NormUnitsOrthogonality
