-- Prove2me | solution 1 for Formalism.CountingSumsFrames.finrank_of_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:18.552622+00:00
-- url     : https://prove2.me/submissions/701a2114-8369-49f7-b4c1-69af880ef800

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
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
namespace Formalism.CountingSumsFrames
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V] (Y : Submodule K V)
    [FiniteDimensional K Y] {ι : Type} [Fintype ι] [DecidableEq ι] (Q : ι → Submodule K V) (P : ι → V →ₗ[K] V)
    (hQY : ∀ i, Q i ≤ Y) (c1 : ∀ i, ∀ x ∈ Y, P i x ∈ Q i) (c2 : ∀ i, ∀ x ∈ Q i, P i x = x)
    (c3 : ∀ i j, i ≠ j → ∀ x ∈ Q j, P i x = 0) (c4 : ∀ x ∈ Y, ∑ i, P i x = x) :
    Module.finrank K Y = ∑ i, Module.finrank K (Q i) := by
  haveI : ∀ i, FiniteDimensional K (Q i) := fun i => Submodule.finiteDimensional_of_le (hQY i)
  let f : Y →ₗ[K] (∀ i, Q i) :=
    LinearMap.pi fun i => ((P i).comp Y.subtype).codRestrict (Q i) (fun x => c1 i x x.2)
  let g : (∀ i, Q i) →ₗ[K] Y := ∑ i, (Submodule.inclusion (hQY i)).comp (LinearMap.proj i)
  have hgf : ∀ x : Y, g (f x) = x := by
    intro x
    apply Subtype.ext
    simp only [g, f, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.pi_apply,
      LinearMap.codRestrict_apply, Submodule.coe_sum, Submodule.coe_inclusion, Submodule.subtype_apply]
    exact c4 x x.2
  have hfg : ∀ q, f (g q) = q := by
    intro q
    funext j
    apply Subtype.ext
    show P j (↑(g q)) = ↑(q j)
    simp only [g, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_sum,
      Submodule.coe_inclusion]
    rw [map_sum, Finset.sum_eq_single j]
    · exact c2 j _ (q j).2
    · intro i _ hij
      exact c3 j i (Ne.symm hij) _ (q i).2
    · intro hj
      exact absurd (Finset.mem_univ _) hj
  let e : Y ≃ₗ[K] (∀ i, Q i) := LinearEquiv.ofLinear f g (LinearMap.ext hfg) (LinearMap.ext hgf)
  rw [e.finrank_eq, Module.finrank_pi_fintype]
end Formalism.CountingSumsFrames
