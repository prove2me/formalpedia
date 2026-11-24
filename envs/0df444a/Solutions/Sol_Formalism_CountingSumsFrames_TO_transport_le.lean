-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.transport_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:58.011235+00:00
-- url     : https://prove2.me/submissions/27271daf-03c9-4fbb-a775-84023eceba16

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_C_stable
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_eqExt
import Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_C
import Theorems.Thm_Formalism_CountingSumsFrames_TO_bigOp_Y
import Theorems.Thm_Formalism_CountingSumsFrames_TO_bigOp_slc
import Theorems.Thm_Formalism_CountingSumsFrames_TO_bigOp_span
import Theorems.Thm_Formalism_CountingSumsFrames_TO_eq_of_slc
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isHW_zero
import Theorems.Thm_Formalism_CountingSumsFrames_TO_C_finW
import Theorems.Thm_Formalism_CountingSumsFrames_TO_Y_fd
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_span
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi)
  {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
  (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhC : ∀ i, h i ∈ Cset p L j0 J M)
  (hli : LinearIndependent ℚ_[p] h) (hsp : Cset p (r := r) L j0 J M ≤ ⨆ i, (GA p L j0).gS {h i})
include hPi hh hhC hli hsp
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (i0 : ι) (v : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hv : (GA p L j0).IsHW (la i0) v)
    (hvC : v ∈ Cset p L j0 J M) (hv0 : v ≠ 0) :
    Module.finrank ℚ_[p] (YYs L j0 J M (h i0)) ≤ Module.finrank ℚ_[p] (YYs L j0 J M v) := by
  classical
  obtain ⟨φ, -, hφE, hφC, hφg, hφinj, -, hφ0⟩ := GlX.eqExt (GA p (r := r) L j0) (C_stable L j0 J M)
    (C_finW L j0 J M) h (fun k => if k = i0 then v else 0) la hh hhC hli hsp
    (fun k => by
      by_cases hk : k = i0
      · subst hk; simpa using hv
      · simpa [hk] using isHW_zero (GA p (r := r) L j0) (la k))
    (fun k => by
      by_cases hk : k = i0
      · simpa [hk] using hvC
      · simp [hk])
  have hEq : IsEqC L j0 J M φ := ⟨hφE, hφC⟩
  have hVF : ∀ g ∈ Cset p L j0 J M, φ g ∈ (GA p (r := r) L j0).gS {v} := by
    intro g hg
    refine Submodule.iSup_induction _ (motive := fun x => φ x ∈ (GA p (r := r) L j0).gS {v}) (hsp hg) ?_
      (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    intro k x hx
    by_cases hk : k = i0
    · subst hk
      have := hφg k x hx
      simpa using this
    · rw [hφ0 k (by simp [hk]) x hx]; exact zero_mem _
  have hgSC : (GA p (r := r) L j0).gS {h i0} ≤ Cset p L j0 J M :=
    (GA p (r := r) L j0).gS_le (by simpa using hhC i0) (C_stable L j0 J M)
  have hmap : ∀ z ∈ YYs L j0 J M (h i0), bigOp L j0 Pi φ z ∈ YYs L j0 J M v := fun z hz =>
    Submodule.mem_inf.mpr ⟨bigOp_Y L j0 e J M Pi φ hPi hEq z (Submodule.mem_inf.mp hz).1,
      bigOp_span L j0 e J M Pi φ hPi hEq _ hVF z⟩
  have hinj : ∀ z ∈ YYs L j0 J M (h i0), bigOp L j0 Pi φ z = 0 → z = 0 := by
    intro z hz h0
    apply eq_of_slc (fsj N r j0)
    intro m
    have h1 : slc (fsj N r j0) m z ∈ (GA p (r := r) L j0).gS {h i0} :=
      slc_span L j0 _ (hgSC.trans inf_le_left) (Submodule.mem_inf.mp hz).2 m
    have h2 := bigOp_slc L j0 e J M Pi φ hPi hEq m z
    rw [h0, map_zero, inOp_C L j0 e J M Pi φ hPi _ (hgSC h1)] at h2
    rw [map_zero]
    exact hφinj i0 (by simpa using hv0) _ h1 h2.symm
  have hfd := Y_fd (p := p) (r := r) L J M
  have : FiniteDimensional ℚ_[p] (YYs L j0 J M v) :=
    Submodule.finiteDimensional_of_le (inf_le_left : YYs L j0 J M v ≤ Y p L J M)
  refine LinearMap.finrank_le_finrank_of_injective (f := (bigOp L j0 Pi φ).restrict hmap) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply Subtype.ext
  apply hinj z.1 z.2
  exact congrArg Subtype.val hz
end Formalism.CountingSumsFrames.TO
