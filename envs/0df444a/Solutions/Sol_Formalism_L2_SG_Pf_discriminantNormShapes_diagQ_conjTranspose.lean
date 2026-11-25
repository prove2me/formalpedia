-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.diagQ_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:39.356728+00:00
-- url     : https://prove2.me/submissions/de06ee19-6c8a-4c34-aa67-7249884a133c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagQConjTranspose
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
namespace Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
private theorem star_algebraMap_ringOfIntegers (x : 𝓞 F) :
    star (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := by
  have h := Formalism.HermitianLattices.Ext.L3.localizedQuotients.star_ι (K := K) (F := F) Fact.out x
  exact FaithfulSMul.algebraMap_injective (𝓞 K) K h
end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (diagQ K 𝔭 k a)ᴴ = diagQ K 𝔭 k a := by
  unfold diagQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply, star_mk, star_algebraMap_ringOfIntegers]
end Formalism.L2.SG.Pf.discriminantNormShapes
