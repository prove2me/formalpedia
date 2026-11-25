-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.orbitCount_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:38.460261+00:00
-- url     : https://prove2.me/submissions/accf1bf3-8e9d-47f0-8b6a-c08d63167e18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_mem_kerSet_of_cls
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_cls_mul_ker
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadAdj_exists_rep


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
theorem _root_.solution (hL : LiftOnto) : OrbitCount := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk
  have hk' : vJof 𝔭 a + 1 ≤ k := by omega

  have hs : ∀ q : udQ K 𝔭 k a, ∃ X : skSet K 𝔭 k a, cls h𝔭 ha hk' X = q := by
    intro q
    obtain ⟨Y, rfl⟩ := Quotient.exists_rep q
    obtain ⟨X, hX, Z, hZ⟩ := hL K F hK 𝔭 h𝔭 m a ha k hk Y
    exact ⟨⟨X, hX⟩, Quotient.sound ⟨Z, hZ⟩⟩
  choose s hs using hs
  have hu : ∀ X : skSet K 𝔭 k a, IsUnit X.1.det := fun X => isUnit_det h𝔭 ha hk' X.2

  let e : skSet K 𝔭 k a ≃ udQ K 𝔭 k a × kerSet K 𝔭 k a :=
    { toFun := fun X => (cls h𝔭 ha hk' X, ⟨(s (cls h𝔭 ha hk' X)).1⁻¹ * X.1,
          mem_kerSet_of_cls h𝔭 ha hk' (hs _)⟩)
      invFun := fun p => ⟨(s p.1).1 * p.2.1, mul_mem_skSet (s p.1).2 p.2.2.1⟩
      left_inv := fun X => Subtype.ext (Matrix.mul_nonsing_inv_cancel_left _ _ (hu _))
      right_inv := fun p => by
        obtain ⟨q, T⟩ := p
        have hc : cls h𝔭 ha hk' ⟨(s q).1 * T.1, mul_mem_skSet (s q).2 T.2.1⟩ = q := by
          rw [cls_mul_ker, hs]
        refine Prod.ext hc (Subtype.ext ?_)
        show (s (cls h𝔭 ha hk' ⟨(s q).1 * T.1, _⟩)).1⁻¹ * ((s q).1 * T.1) = T.1
        rw [hc]
        exact Matrix.nonsing_inv_mul_cancel_left _ _ (hu _) }
  rw [Nat.card_congr e, Nat.card_prod]
end Formalism.L2.SG.Pf.discriminantNormShapes
