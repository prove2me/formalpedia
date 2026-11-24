-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.waveSiteAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:49:48.829264+00:00
-- url     : https://prove2.me/submissions/c3ca63e8-ee91-418a-b11c-a80e239ca55e

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Theorems.Thm_Formalism_FourierDecayAlt_P5_fsv_mul_fsv_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P5_fsv_neg_mul_fsv
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pOp_fsv_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pbOp_fsv_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_radSp_regular
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_ext
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_mul_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_mul_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_one_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_one_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_alg_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_alg_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P5.mkPair_fst'
attribute [local simp] Formalism.FourierDecayAlt.P5.mkPair_snd'
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_mul_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_mul_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_add_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_add_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_one_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_one_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_alg_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_alg_snd

set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution : WaveSiteAll := by
  intro Wp Wq _ _ _ _ P z z' π π' X L hL l s Wv Wv' hW hW'
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hop : ∀ i (Φ : RadSp P.k P.r z z' π π'),
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) :=
    fun i Φ => X.op_apply l i Φ
  have hWW' : Wv * Wv' = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]
  have hW'W : Wv' * Wv = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]

  have hcomm : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (u : ℂ → ℂ),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        u (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ i : Fin 6, (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5) → W * X.op l i = X.op l i * W := by
    intro W u hWu i hi
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, hWu, hop, crd]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [opL, cOp, ciOp, cbOp, cbiOp] <;> exact smul_comm _ _ _
  have hsite : ∀ f : Pr (RadSp P.k P.r z z' π π'), (site L l).p = L.p l ∧ (site L l).c = L.c l ∧
      (site L l).ci = L.ci l := fun _ => ⟨rfl, rfl, rfl⟩
  obtain ⟨hsp, hsc, hsci⟩ := hsite 0
  rw [hsp, hsc, hsci, hp l, hc l, hci l]
  refine ⟨⟨pr_ext ?_ ?_, pr_ext ?_ ?_, rfl⟩, pr_ext ?_ ?_, pr_ext ?_ ?_, pr_ext ?_ ?_⟩
  · simpa using hWW'
  · simpa using hWW'
  · simpa using hW'W
  · simpa using hW'W
  · simpa using hcomm Wv _ hW1 1 (by decide)
  · simpa using (hcomm Wv' _ hW2 4 (by decide)).symm
  · simpa using hcomm Wv _ hW1 2 (by decide)
  · simpa using (hcomm Wv' _ hW2 5 (by decide)).symm
  · simp only [mkPair_fst', pr_mul_fst, pr_add_fst, pr_alg_fst]
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    obtain ⟨hd, h0⟩ := radSp_regular Φ g c
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add,
      Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hop, crd, hW1, opL]
    rw [pOp_fsv_smul s l _ c hd h0]
    simp only [cOp]
  · simp only [mkPair_snd', pr_mul_snd, pr_add_snd, pr_alg_snd]
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    obtain ⟨hd, h0⟩ := radSp_regular Φ g c
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
      Submodule.coe_add, Submodule.coe_neg, Submodule.coe_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hop,
      crd, hW2, opL]
    rw [pbOp_fsv_smul s l _ c hd h0]
    simp only [cbOp]
    module
end Formalism.FourierDecayAlt.P5
