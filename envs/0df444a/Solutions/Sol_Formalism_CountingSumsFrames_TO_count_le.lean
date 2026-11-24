-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.count_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:57.727892+00:00
-- url     : https://prove2.me/submissions/e5a03f1a-354b-401f-8a71-7ac52a937f9b

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_C
import Theorems.Thm_Formalism_CountingSumsFrames_TO_C_stable
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_eqExt
import Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_C
import Theorems.Thm_Formalism_CountingSumsFrames_TO_bigOp_Y
import Theorems.Thm_Formalism_CountingSumsFrames_TO_bigOp_slc
import Theorems.Thm_Formalism_CountingSumsFrames_TO_bigOp_span
import Theorems.Thm_Formalism_CountingSumsFrames_TO_eq_of_slc
import Theorems.Thm_Formalism_CountingSumsFrames_TO_finrank_biSup_le
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isHW_zero
import Theorems.Thm_Formalism_CountingSumsFrames_TO_C_finW
import Theorems.Thm_Formalism_CountingSumsFrames_TO_Y_fd
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
theorem _root_.solution (bad : ι → Prop) [DecidablePred bad]
    (ϖ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hϖ : IsEqC L j0 J M ϖ) (hgood : ∀ i, ¬ bad i → ∀ x ∈ (GA p L j0).gS {h i}, ϖ x = x)
    (hbad : ∀ i, bad i → ∀ x ∈ (GA p L j0).gS {h i}, ϖ x = 0) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) -
      Module.finrank ℚ_[p] ((Y p L J M ⊓ LinearMap.ker (bigOp L j0 Pi ϖ - LinearMap.id) :
        Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
      ∑ i ∈ univ.filter bad, Module.finrank ℚ_[p] (YYs L j0 J M (h i)) := by
  classical
  have hex : ∀ i : ι, ∃ φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      IsEqC L j0 J M φ ∧ (∀ x ∈ (GA p (r := r) L j0).gS {h i}, φ x = x) ∧
        (∀ k, k ≠ i → ∀ x ∈ (GA p (r := r) L j0).gS {h k}, φ x = 0) := by
    intro i
    obtain ⟨φ, -, hφE, hφC, -, -, hφ1, hφ0⟩ := GlX.eqExt (GA p (r := r) L j0) (C_stable L j0 J M)
      (C_finW L j0 J M) h (fun k => if k = i then h k else 0) la hh hhC hli hsp
      (fun k => by
        by_cases hk : k = i
        · simpa [hk] using hh i
        · simpa [hk] using isHW_zero (GA p (r := r) L j0) (la k))
      (fun k => by
        by_cases hk : k = i
        · simpa [hk] using hhC i
        · simp [hk])
    exact ⟨φ, ⟨hφE, hφC⟩, hφ1 i (by simp), fun k hk => hφ0 k (by simp [hk])⟩
  choose π hπEq hπ1 hπ0 using hex

  have hπVF : ∀ i, ∀ g ∈ Cset p L j0 J M, π i g ∈ (GA p (r := r) L j0).gS {h i} := by
    intro i g hg
    refine Submodule.iSup_induction _ (motive := fun x => π i x ∈ (GA p (r := r) L j0).gS {h i}) (hsp hg) ?_
      (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    intro k x hx
    by_cases hk : k = i
    · subst hk; rw [hπ1 k x hx]; exact hx
    · rw [hπ0 i k hk x hx]; exact zero_mem _

  have hdec : ∀ g ∈ Cset p L j0 J M, g - ϖ g = ∑ i ∈ univ.filter bad, π i g := by
    intro g hg
    refine Submodule.iSup_induction _ (motive := fun x => x - ϖ x = ∑ i ∈ univ.filter bad, π i x) (hsp hg) ?_
      (by simp) (fun x y hx hy => by
        simp only [map_add, Finset.sum_add_distrib, ← hx, ← hy]; abel)
    intro k x hx
    by_cases hk : bad k
    · rw [hbad k hk x hx, sub_zero, Finset.sum_eq_single k (fun i _ hik => hπ0 i k (Ne.symm hik) x hx)
        (fun hk' => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) hk'), hπ1 k x hx]
    · rw [hgood k hk x hx, sub_self]
      refine (Finset.sum_eq_zero fun i hi => hπ0 i k ?_ x hx).symm
      rintro rfl
      exact hk (Finset.mem_filter.mp hi).2

  have hdecY : ∀ y ∈ Y p L J M, y - bigOp L j0 Pi ϖ y = ∑ i ∈ univ.filter bad, bigOp L j0 Pi (π i) y := by
    intro y hy
    apply eq_of_slc (fsj N r j0)
    intro m
    have hc := slc_C L j0 J M hy m
    rw [map_sub, map_sum, bigOp_slc L j0 e J M Pi ϖ hPi hϖ m y, inOp_C L j0 e J M Pi ϖ hPi _ hc, hdec _ hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bigOp_slc L j0 e J M Pi (π i) hPi (hπEq i) m y, inOp_C L j0 e J M Pi (π i) hPi _ hc]
  have hfd := Y_fd (p := p) (r := r) L J M
  set Z : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := ⨆ i ∈ univ.filter bad, YYs L j0 J M (h i) with hZ
  have hZY : Z ≤ Y p L J M := iSup₂_le fun i _ => inf_le_left
  have hZfd : FiniteDimensional ℚ_[p] Z := Submodule.finiteDimensional_of_le hZY
  set f : Y p (r := r) L J M →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
    (bigOp L j0 Pi ϖ - LinearMap.id) ∘ₗ (Y p (r := r) L J M).subtype with hf
  have hran : LinearMap.range f ≤ Z := by
    rintro _ ⟨y, rfl⟩
    have h1 : f y = -(∑ i ∈ univ.filter bad, bigOp L j0 Pi (π i) y.1) := by
      rw [← hdecY y.1 y.2]; simp [hf]
    rw [h1]
    refine Z.neg_mem (Submodule.sum_mem _ fun i hi => ?_)
    refine (le_iSup₂ (f := fun i (_ : i ∈ univ.filter bad) => YYs L j0 J M (h i)) i hi) ?_
    exact Submodule.mem_inf.mpr ⟨bigOp_Y L j0 e J M Pi (π i) hPi (hπEq i) y.1 y.2,
      bigOp_span L j0 e J M Pi (π i) hPi (hπEq i) _ (hπVF i) y.1⟩
  have hker : Module.finrank ℚ_[p] (LinearMap.ker f) =
      Module.finrank ℚ_[p] ((Y p L J M ⊓ LinearMap.ker (bigOp L j0 Pi ϖ - LinearMap.id) :
        Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) := by
    rw [hf, LinearMap.ker_comp, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have h1 : Module.finrank ℚ_[p] (LinearMap.range f) ≤ Module.finrank ℚ_[p] Z := Submodule.finrank_mono hran
  have h2 : Module.finrank ℚ_[p] Z ≤ ∑ i ∈ univ.filter bad, Module.finrank ℚ_[p] (YYs L j0 J M (h i)) :=
    finrank_biSup_le (Y p (r := r) L J M) (fun i => YYs L j0 J M (h i)) (fun i => inf_le_left) (univ.filter bad)
  rw [← hker]
  omega
end Formalism.CountingSumsFrames.TO
