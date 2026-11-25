-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalizedFibreSets.card_U_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:54:33.67649+00:00
-- url     : https://prove2.me/submissions/9fbb0b17-69c6-462d-9315-01527954adb7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsoCountOneInert
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_PhiCountingHolds
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_algebraMap_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IsotropicCounts_isoCount_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_conjO
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)]
namespace Formalism.L2.SG.Pf.LocalizedFibreSets
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : ι → 𝓞 F) (hb : ∀ i, b i ∉ 𝔭) :
    (Nat.card {γ : Matrix ι ι (𝓞 K ⧸ extP K 𝔭 ^ 1) //
      γᴴ * diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i))) * γ =
        diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i)))} : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ (Fintype.card ι ^ 2) * alphaStd K 𝔭 (Fintype.card ι) := by
  classical
  set n := Fintype.card ι with hn
  let e : ι ≃ Fin n := Fintype.equivFin ι
  set d : ι → 𝓞 K ⧸ extP K 𝔭 ^ 1 := fun i =>
    Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i)) with hd
  let u : Fin n → 𝓞 K := fun i => algebraMap (𝓞 F) (𝓞 K) (b (e.symm i))
  have hD : (diagonal u).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)) =
      Matrix.reindex e e (diagonal d) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [u, d, Matrix.reindex_apply]
    · have hij' : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
      simp [u, d, Matrix.reindex_apply, Matrix.diagonal_apply_ne _ hij,
        Matrix.diagonal_apply_ne _ hij']
  have hcard : Nat.card {γ : Matrix ι ι (𝓞 K ⧸ extP K 𝔭 ^ 1) // γᴴ * diagonal d * γ = diagonal d} =
      Nat.card {X : Matrix (Fin n) (Fin n) (𝓞 K ⧸ extP K 𝔭 ^ 1) //
        Xᴴ * Matrix.reindex e e (diagonal d) * X = Matrix.reindex e e (diagonal d)} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Matrix.reindex e e) fun γ => ?_)
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    refine ⟨fun h => by rw [h], fun h => (Matrix.reindex e e).injective ?_⟩
    simpa only [Matrix.reindex_apply] using h
  have hu : ∀ i, Formalism.HermitianLattices.Ext.L3.conjO K (u i) = u i := fun i => by
    apply IsFractionRing.injective (𝓞 K) K
    rw [Formalism.HermitianLattices.Ext.L3.BallB.algebraMap_conjO, (Fact.out : IsFixF K F)]
    refine ⟨((b (e.symm i) : 𝓞 F) : F), ?_⟩
    show algebraMap F K (algebraMap (𝓞 F) F (b (e.symm i))) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K]
  have hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤ := fun i => by
    have hF : Ideal.span {b (e.symm i)} ⊔ 𝔭 = ⊤ := by
      refine h𝔭.1.2 _ (lt_of_le_of_ne le_sup_right fun h => hb (e.symm i) ?_)
      rw [h]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have h2 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hF
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_top] at h2
    exact h2
  rw [hcard, ← hD]
  exact Formalism.HermitianLattices.Ext.L3.IsotropicCounts.isoCount_one hK h𝔭 u hu hunit
end Formalism.L2.SG.Pf.LocalizedFibreSets
