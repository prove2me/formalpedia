-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.akCount_eq_skSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:16:14.07281+00:00
-- url     : https://prove2.me/submissions/8ffcb9bf-2c27-44bc-bd22-a67242dd5f80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapes
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_linearIndependent_of_jordan
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U3_akCount_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_akCount_eq
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
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [Fact (IsFixF K F)]
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b : Fin (finrank K (⊤ : Submodule K V)) → V}
    {a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F} (hb : IsJordanIn h ⊤ L 𝔭 b a) (k : ℕ) :
    akCount h L 𝔭 k = Nat.card (skSet K 𝔭 k a) := by
  have hli := linearIndependent_of_jordan hb
  have hcard : Fintype.card (Fin (finrank K (⊤ : Submodule K V))) = finrank K V := by
    simp [finrank_top]
  have hB : ⇑(Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm)) = b :=
    Basis.coe_mk _ _
  have hH : ∀ i j, algebraMap (𝓞 K) K
      ((Matrix.diagonal fun i => algebraMap (𝓞 F) (𝓞 K) (a i)) i j) =
      h (Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm) i)
        (Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm) j) := by
    intro i j
    rw [hB]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, hb.2.2.2.1 i]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero]
      exact (hb.2.2.1 i j hij).symm
  rw [integralBasisSpans.akCount_eq h h𝔭 _ (by
    have h2 := hb.2.1
    rw [← hB] at h2
    exact h2) hH k]
  have hd : (Matrix.diagonal fun i => algebraMap (𝓞 F) (𝓞 K) (a i)).map
      (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = diagQ K 𝔭 k a := by
    rw [diagQ, Matrix.diagonal_map (map_zero _)]
  rw [hd]
  rfl
end Formalism.L2.SG.Pf.discriminantNormShapes
