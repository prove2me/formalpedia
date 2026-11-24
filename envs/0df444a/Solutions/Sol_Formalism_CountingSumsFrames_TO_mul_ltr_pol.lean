-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.mul_ltr_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:36.649994+00:00
-- url     : https://prove2.me/submissions/b8062c36-dd38-40cc-a8d8-5825e4aeed45

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
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
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (L : Letters N) (j0 : ℕ) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : g ∈ Pol p r (Lz L j0))
    {m' : Fin N × Fin r →₀ ℕ} (hm : MultiDeg L m') : g * monomial (ltr (fsj N r j0) m') 1 ∈ Pol p r L := by
  unfold Formalism.GM.M.Pol at hg ⊢
  rw [mem_restrictSupport_iff] at hg ⊢
  intro d hd
  rw [Finset.mem_coe] at hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hd)
  have hb' := support_monomial_subset hb
  rw [Finset.mem_singleton] at hb'
  subst hb'
  have hma : Formalism.GM.M.MultiDeg (Lz L j0) a := hg (Finset.mem_coe.mpr ha)
  intro i
  have h1 := hma i
  have h2 := hm i
  simp only [Formalism.GM.DimensionMonotonicity.Lz] at h1
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  split_ifs at h1 with hi
  · rw [h1]
    have h3 : ∑ c, ltr (fsj N r j0) m' (i, c) = 0 :=
      Finset.sum_eq_zero fun c _ => by simp [ltr, Finsupp.filter_apply, fsj, hi]
    rw [h3, add_zero]
  · rw [h1, zero_add, ← h2]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [ltr, Finsupp.filter_apply, fsj, hi]
end Formalism.CountingSumsFrames.TO
