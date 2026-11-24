-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.phi_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:42.975179+00:00
-- url     : https://prove2.me/submissions/e803a7d8-d35b-47ef-90b2-257b2b2f4f2d

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_nondeg
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_X_gen
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_E
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_add_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_smul_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t)
include hadm
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    T.phi p L i (glAct p L (T.pos i + 1 + 1) c d x) = glAct p L (T.pos i + 1 + 1) c d (T.phi p L i x) := by
  classical
  obtain ⟨h, hva, hvb⟩ := hadm.2.1 i
  set a : Fin N := ⟨T.pos i, by omega⟩ with ha
  set b : Fin N := ⟨T.pos i + 1, h⟩ with hb
  have hE : ∀ (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      glAct p L (T.pos i + 1 + 1) c d (Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) y) =
        Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (glAct p L (T.pos i + 1 + 1) c d y) := by
    intro c d y
    simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply]
    rw [Formalism.GM.M.FB.glAct_mul]
    have h0 : glAct p L (T.pos i + 1 + 1) c d (∑ e : Fin r, X (a, e) * X (b, e)) = 0 := by
      rw [map_sum]
      have : ∀ e : Fin r, glAct p L (T.pos i + 1 + 1) c d (X (a, e) * X (b, e)) =
          (if e = c then -(X (a, c) * X (b, d)) else 0) + (if e = d then X (a, c) * X (b, d) else 0) := by
        intro e
        have hXa : glAct p L (T.pos i + 1 + 1) c d (X (a, e)) = if e = d then X (a, c) else 0 := by
          rw [glAct_X_gen, if_pos (show (a : ℕ) < T.pos i + 1 + 1 by show T.pos i < _; omega), hva]; simp
        have hXb : glAct p L (T.pos i + 1 + 1) c d (X (b, e)) = if e = c then -X (b, d) else 0 := by
          rw [glAct_X_gen, if_pos (show (b : ℕ) < T.pos i + 1 + 1 by show T.pos i + 1 < _; omega), hvb]; simp
        rw [Formalism.GM.M.FB.glAct_mul, hXa, hXb]
        split_ifs with h1 h2 h2
        · subst h1; subst h2; ring
        · subst h1; ring
        · subst h2; ring
        · ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [h0, mul_zero, add_zero]
  have hF : ∀ (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      glAct p L (T.pos i + 1 + 1) c d (Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) y) =
        Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (glAct p L (T.pos i + 1 + 1) c d y) := by
    intro c d y
    rw [← sub_eq_zero]
    apply fock_nondeg
    intro u
    rw [gammaIntegralityLemmas.fock_symm, sub_eq_add_neg, gammaIntegralityLemmas.fock_symm, gammaIntegralityLemmas.fock_add_left, ← neg_one_smul ℚ_[p],
      gammaIntegralityLemmas.fock_smul_left, fock_glAct, gammaIntegralityLemmas.fock_symm _ (glAct p L (T.pos i + 1 + 1) d c u),
      ← gammaIntegralityLemmas.fock_E, ← hE, gammaIntegralityLemmas.fock_symm, ← fock_glAct,
      gammaIntegralityLemmas.fock_symm (Formalism.GM.tieF _ _ _) u, ← gammaIntegralityLemmas.fock_E, gammaIntegralityLemmas.fock_symm _ (Formalism.GM.tieE _ _ u)]
    ring
  have cE : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))) := by
    rw [commute_iff_eq]; exact LinearMap.ext fun y => hE c d y
  have cF : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))) := by
    rw [commute_iff_eq]; exact LinearMap.ext fun y => hF c d y
  have cP : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (T.phi p L i) := by
    unfold TieData.phi
    rw [dif_pos h]
    unfold tiePhiAt Formalism.GM.tiePhi
    refine Commute.sum_right _ _ _ fun j _ => Commute.smul_right ?_ _
    rw [← Module.End.mul_eq_comp]
    exact (cE.pow_right j).mul_right (cF.pow_right j)
  exact (LinearMap.congr_fun cP.eq x).symm
end Formalism.CountingSumsFrames.TO
