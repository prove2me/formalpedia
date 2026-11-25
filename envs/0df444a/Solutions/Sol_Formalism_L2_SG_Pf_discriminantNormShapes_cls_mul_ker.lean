-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.cls_mul_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:08.778313+00:00
-- url     : https://prove2.me/submissions/2912b79c-79bd-4b14-8e9d-ba3a3fbdb2b4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_cls_eq_iff

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.HermitianLattices.Ext.L3.localValuationFiltration Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F}
    (ha : ∀ i, a i ≠ 0) {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) (S : skSet K 𝔭 k a) (T : kerSet K 𝔭 k a) :
    cls h𝔭 ha hk ⟨S.1 * T.1, mul_mem_skSet S.2 T.2.1⟩ = cls h𝔭 ha hk S := by
  rw [cls_eq_iff]
  obtain ⟨Y, hY⟩ := T.2.2
  refine ⟨S.1 * Y, ?_⟩
  show S.1 * T.1 - S.1 = S.1 * Y * diagQ K 𝔭 k a
  rw [hY, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left, Matrix.mul_assoc]
end Formalism.L2.SG.Pf.discriminantNormShapes
