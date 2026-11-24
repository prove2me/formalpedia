-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.ycond_mul_cov
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:56.301815+00:00
-- url     : https://prove2.me/submissions/2956dd21-4c6b-4ee4-b4eb-33ab2b05e683

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_wt_le_of_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_wt_add
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_lw
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_wOut_zero
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_stable
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution [NeZero r] (LL : Letters N) (J : ℕ) (M : WithTop ℤ) (i0 : Fin N) (hi0 : (i0 : ℕ) < J)
    (hv : LL.vec i0 = false) {e : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (he : e ∈ weightedHomogeneousSubmodule ℚ_[p] (wOut N r i0) 0) :
    ∀ F ∈ YCond p LL J M, e * F ∈ YCond p LL J M := by
  classical
  let H := weightedHomogeneousSubmodule ℚ_[p] (wOut N r i0) 0
  have hH : ∀ c d, ∀ x ∈ H, glAct p LL J c d x ∈ H := fun c d x hx =>
    glAct_lw LL J c d (wOut N r i0) (fun i c c' => rfl) hx
  let S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    Submodule.span ℚ_[p] {x | ∃ e ∈ H, ∃ y ∈ YCond p LL J M, x = e * y}
  have hwa : ∀ a : Fin N × Fin r →₀ ℕ, Finsupp.weight (wOut N r i0) a = 0 → wt LL J 0 a ≤ 0 := by
    intro a ha
    have hz := wOut_zero ha
    unfold wt
    rw [Finset.sum_eq_single i0]
    · simp [hi0, hv]
    · intro b _ hb; rw [hz (b, 0) hb]; simp
    · simp
  have hS1 : S ≤ MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL J 0 m : ℤ) : WithTop ℤ) ≤ M} := by
    rw [Submodule.span_le]
    rintro _ ⟨e, he, y, hy, rfl⟩
    rw [SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul e y hm)
    have h1 := hwa a (he (mem_support_iff.mp ha))
    have h2 := Formalism.GM.FrozenVariableComponents.wt_le_of_mem p LL J M y hy b hb
    show ((wt LL J 0 (a + b) : ℤ) : WithTop ℤ) ≤ M
    rw [wt_add]
    induction M using WithTop.recTopCoe with
    | top => exact le_top
    | coe M' =>
      rw [WithTop.coe_le_coe] at h2 ⊢
      omega
  have hS2 : GlStable p LL J S := by
    intro c d x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, y, hy, rfl⟩ := hx
      rw [Formalism.GM.M.FB.glAct_mul]
      refine S.add_mem (Submodule.subset_span ⟨e, he, _, Formalism.GM.FrozenVariableComponents.ycond_stable p LL J M c d y hy, rfl⟩) ?_
      rw [mul_comm]
      exact Submodule.subset_span ⟨_, hH c d e he, y, hy, rfl⟩
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact S.smul_mem a hx
  have hS : S ≤ YCond p LL J M := le_sSup ⟨hS1, hS2⟩
  intro F hF
  exact hS (Submodule.subset_span ⟨e, he, F, hF, rfl⟩)
end Formalism.GM.DimensionMonotonicity
