-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.mem_kerSet_of_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:45.837956+00:00
-- url     : https://prove2.me/submissions/183bb5ba-ef91-47b8-93aa-2655ab734aa6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_inv_mem_skSet
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
    (ha : ∀ i, a i ≠ 0) {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) {S X : skSet K 𝔭 k a}
    (hSX : cls h𝔭 ha hk S = cls h𝔭 ha hk X) : S.1⁻¹ * X.1 ∈ kerSet K 𝔭 k a := by
  obtain ⟨Z, hZ⟩ := (cls_eq_iff h𝔭 ha hk S X).mp hSX
  have hu := isUnit_det h𝔭 ha hk S.2
  refine ⟨mul_mem_skSet (inv_mem_skSet S.2 hu) X.2, -(S.1⁻¹ * Z), ?_⟩
  have hX : X.1 = S.1 - Z * diagQ K 𝔭 k a := by rw [← hZ]; abel
  rw [hX, Matrix.mul_sub, Matrix.nonsing_inv_mul _ hu, Matrix.neg_mul, Matrix.mul_assoc,
    sub_eq_add_neg]
end Formalism.L2.SG.Pf.discriminantNormShapes
