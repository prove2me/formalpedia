-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.linearIndependent_of_jordan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:49.188608+00:00
-- url     : https://prove2.me/submissions/95a08f64-2ddd-41cf-88af-b30ab103ce77

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapes
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
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} {b : Fin (finrank K (⊤ : Submodule K V)) → V}
    {a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F} (hb : IsJordanIn h ⊤ L 𝔭 b a) :
    LinearIndependent K b := by
  obtain ⟨-, -, horth, hdiag, hne⟩ := hb
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 : h (b i) (∑ j ∈ s, g j • b j) = 0 := by rw [hg, map_zero]
  rw [map_sum, Finset.sum_eq_single i] at h1
  · rw [map_smul, smul_eq_mul, hdiag] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (by simpa using h2) (hne i)
  · intro j _ hji
    rw [map_smul, horth i j (Ne.symm hji), smul_zero]
  · intro hi'
    exact absurd hi hi'
end Formalism.L2.SG.Pf.discriminantNormShapes
