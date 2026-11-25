-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalizedFibreSets.map_phiQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:47.728798+00:00
-- url     : https://prove2.me/submissions/20732936-9c2b-45d0-8946-4b881effe166

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
import Theorems.Thm_Formalism_L2_SG_Pf_LocalizedFibreSets_map_diagQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
namespace Formalism.L2.SG.Pf.LocalizedFibreSets
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))) :
    (phiQ K 𝔭 (k + 1) a Y).map (piQ K 𝔭 k) = phiQ K 𝔭 k a (Y.map (piQ K 𝔭 k)) := by
  have hs : Function.Semiconj (piQ K 𝔭 k) star star := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    unfold piQ
    rw [star_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, star_mk]
  have hd := map_diagQ (K := K) 𝔭 k a
  unfold phiQ
  rw [Matrix.map_add (piQ K 𝔭 k) (map_add (piQ K 𝔭 k)), Matrix.map_add (piQ K 𝔭 k) (map_add (piQ K 𝔭 k)),
    Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ hs, hd]
end Formalism.L2.SG.Pf.LocalizedFibreSets
