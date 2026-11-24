-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.bigOp_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:04.880465+00:00
-- url     : https://prove2.me/submissions/09b96667-b1fc-4343-8300-f87055ab63f7

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_eq_sum
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isL_monomial_ltr
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_wh
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_pol
import Theorems.Thm_Formalism_CountingSumsFrames_TO_mul_ltr_pol
import Theorems.Thm_Formalism_CountingSumsFrames_TO_psi_id
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isHW_iff
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_int
import Theorems.Thm_Formalism_CountingSumsFrames_TO_int_of_mul_monomial
import Theorems.Thm_Formalism_CountingSumsFrames_TO_int_monomial_one
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isWt_iff_wh
import Theorems.Thm_Formalism_CountingSumsFrames_TO_piPsi_mem
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_mul
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
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
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi) (hφ : IsEqC L j0 J M φ)
include hPi
include hφ
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution
    (hint : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) →
      φ v ∈ IntPol p (Fin N × Fin r))
    (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ HWC p L j0 univ la ⊓ Pol p r L)
    (hxi : x ∈ IntPol p (Fin N × Fin r)) :
    ((p : ℚ_[p]) ^ e) • bigOp L j0 Pi φ x ∈ IntPol p (Fin N × Fin r) := by
  classical
  obtain ⟨hxH, hxP⟩ := Submodule.mem_inf.mp hx
  obtain ⟨hxW, hxE⟩ := (isHW_iff L j0 la x).mpr hxH
  rw [bigOp, ext_eq_sum (fsj N r j0) _ x (x.support.image (ltr (fsj N r j0)))
    (fun m hm => Finset.mem_image_of_mem _ hm), Finset.smul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
  set s := slc (fsj N r j0) (ltr (fsj N r j0) m') x with hs
  have hsP : s ∈ Pol p r (Lz L j0) := slc_pol L j0 _ hxP
  have hsI : s ∈ IntPol p (Fin N × Fin r) := slc_int j0 _ hxi
  have hmd : MultiDeg L m' := ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hxP) hm'
  have hsm : s * monomial (ltr (fsj N r j0) m') 1 ∈ PolZ p r L :=
    Submodule.mem_inf.mpr ⟨mul_ltr_pol L j0 hsP hmd, FrozenVariableLemmas.intPol_mul p hsI (int_monomial_one _)⟩
  have h1 := hPi.int _ hsm
  rw [hPi.mul _ _ (isL_monomial_ltr (fsj N r j0) m' 1), ← smul_mul_assoc] at h1
  have hvI : ((p : ℚ_[p]) ^ e) • Pi s ∈ IntPol p (Fin N × Fin r) := int_of_mul_monomial _ _ h1
  have hPs : Pi s ∈ Cset p L j0 J M := by
    have := piPsi_mem L j0 e J M Pi hPi s
    rwa [psi_id L j0 hsP] at this
  have hvC : ((p : ℚ_[p]) ^ e) • Pi s ∈ Cset p L j0 J M := Submodule.smul_mem _ _ hPs
  have hsW : s ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) la :=
    slc_wh L le_rfl _ ((isWt_iff_wh L j0 la x).mp hxW)
  have hvH : (GA p L j0).IsHW la (((p : ℚ_[p]) ^ e) • Pi s) := by
    refine ⟨(isWt_iff_wh L j0 la _).mpr (Submodule.smul_mem _ _ (hPi.wh la _ hsW)), fun a b hab => ?_⟩
    show glAct p L j0 a b _ = 0
    have h0 : glAct p L j0 a b x = 0 := hxE a b hab
    rw [map_smul, ← hPi.comm, hs, ← slc_glAct L le_rfl a b, h0, map_zero, map_zero, smul_zero]
  have h2 := hint la _ hvC hvH hvI
  rw [map_smul] at h2
  have e3 : inOp L j0 Pi φ s = φ (Pi s) := by
    simp only [inOp, LinearMap.comp_apply]; rw [psi_id L j0 hsP]
  rw [e3, ← smul_mul_assoc]
  exact FrozenVariableLemmas.intPol_mul p h2 (int_monomial_one _)
end Formalism.CountingSumsFrames.TO
