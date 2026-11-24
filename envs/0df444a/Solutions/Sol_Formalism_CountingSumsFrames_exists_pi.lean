-- Prove2me | solution 1 for Formalism.CountingSumsFrames.exists_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:49.975322+00:00
-- url     : https://prove2.me/submissions/c49848ed-e569-4d57-8a07-9eb7186adab5

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_span_hw
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_indep_hw
import Theorems.Thm_Formalism_CountingSumsFrames_proj_exists
import Theorems.Thm_Formalism_CountingSumsFrames_proj_sum
import Theorems.Thm_Formalism_CountingSumsFrames_proj_comm
import Theorems.Thm_Formalism_CountingSumsFrames_C_stable
import Theorems.Thm_Formalism_CountingSumsFrames_polynomial_finite_weights
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_stable
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
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhP : ∀ i, h i ∈ Pol p r (Lz L j0))
    (hli : LinearIndependent ℚ_[p] h)
    (hsp : ∀ μ v, v ∈ Pol p r (Lz L j0) → (GA p L j0).IsHW μ v → v ∈ Submodule.span ℚ_[p] (Set.range h))
    (hspC : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v →
      v ∈ Submodule.span ℚ_[p] (h '' {i | h i ∈ Cset p L j0 J M})) :
    ∃ π : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ i x, π i x ∈ (GA p L j0).gS {h i}) ∧ (∀ i, ∀ x ∈ (GA p L j0).gS {h i}, π i x = x) ∧
      (∀ i j, j ≠ i → ∀ x ∈ (GA p L j0).gS {h j}, π i x = 0) ∧
      (∀ x ∈ Pol p r (Lz L j0), ∑ i, π i x = x) ∧
      (∀ i, ∀ x ∈ Cset p L j0 J M, π i x ∈ Cset p L j0 J M) ∧
      (∀ i, h i ∉ Cset p L j0 J M → ∀ x ∈ Cset p L j0 J M, π i x = 0) ∧
      (∀ i, ∀ x ∈ Pol p r (Lz L j0), ∀ c d, π i (glAct p L j0 c d x) = glAct p L j0 c d (π i x)) ∧
      (∀ i, ∀ x ∈ Pol p r (Lz L j0), ∀ ν, π i ((GA p L j0).comp ν x) = (GA p L j0).comp ν (π i x)) := by
  classical
  have hP1s : (GA p L j0).Stable (Pol p r (Lz L j0)) := pol_stable L (Lz L j0) j0
  obtain ⟨S, hS⟩ := polynomial_finite_weights (p := p) (r := r) L j0
  have hind := GlX.indep_hw (GA p L j0) hP1s hS h la hh hhP hli
  have hRW : ∀ i, (GA p L j0).gS {h i} ≤ Pol p r (Lz L j0) := fun i =>
    (GA p L j0).gS_le (by simpa using hhP i) hP1s
  have hWR := GlX.span_hw (GA p L j0) hP1s hS h la hh hhP (fun i => hli.ne_zero i) hsp
  obtain ⟨π, h1, h2, h3⟩ := proj_exists (W := Pol p r (Lz L j0)) (fun i => (GA p L j0).gS {h i}) hind hRW hWR
  have hCs := C_stable (p := p) (r := r) L j0 J M
  have hCW : Cset p L j0 J M ≤ Pol p r (Lz L j0) := inf_le_left
  have hCR : Cset p L j0 J M ≤ ⨆ (j : {j // h j ∈ Cset p L j0 J M}), (GA p L j0).gS {h j} := by
    refine GlX.span_hw (GA p L j0) hCs (fun x hx => hS x (hCW hx)) (fun j : {j // h j ∈ Cset p L j0 J M} => h j)
      (fun j => la j) (fun j => hh j) (fun j => j.2) (fun j => hli.ne_zero (j : ι)) ?_
    intro μ v hv hvh
    have := hspC μ v hv hvh
    rwa [Set.image_eq_range] at this
  refine ⟨π, h1, h2, h3, proj_sum _ hWR π h2 h3, fun i x hx => ?_, fun i hi x hx => ?_, fun i x hx c d => ?_,
    fun i x hx ν => ?_⟩
  · refine Submodule.iSup_induction _ (motive := fun x => π i x ∈ Cset p L j0 J M) (hCR hx) (fun j y hy => ?_)
      (by simp) (fun x y hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
    by_cases hji : (j : ι) = i
    · rw [h2 i y (hji ▸ hy)]
      exact (GA p L j0).gS_le (by simpa using j.2) hCs hy
    · rw [h3 i j hji y hy]; exact Submodule.zero_mem _
  · refine Submodule.iSup_induction _ (motive := fun x => π i x = 0) (hCR hx) (fun j y hy => ?_)
      (by simp) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
    exact h3 i j (fun hji => hi (hji ▸ j.2)) y hy
  · exact proj_comm _ hWR π h2 h3 (glAct p L j0 c d) (fun j x hx => (GA p L j0).gS_stable _ c d x hx) i x hx
  · exact proj_comm _ hWR π h2 h3 ((GA p L j0).comp ν)
      (fun j x hx => (GA p L j0).graded_of ((GA p L j0).gS_stable _) ν x hx) i x hx
end Formalism.CountingSumsFrames
