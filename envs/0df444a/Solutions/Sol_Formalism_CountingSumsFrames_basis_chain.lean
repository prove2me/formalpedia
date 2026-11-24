-- Prove2me | solution 1 for Formalism.CountingSumsFrames.basis_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:16.979247+00:00
-- url     : https://prove2.me/submissions/4b382062-74bf-490d-9c17-132f4d2b92a2

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
open Finset
namespace Formalism.CountingSumsFrames
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V] (A B : Submodule K V) (hAB : A ≤ B)
    [FiniteDimensional K B] (e : V) (he : e ∈ A) :
    ∃ b : Finset V, ((b : Set V) ⊆ (B : Set V)) ∧ LinearIndepOn K id (b : Set V) ∧
      ((B : Set V) ⊆ Submodule.span K (b : Set V)) ∧ (e ≠ 0 → e ∈ b) ∧
      ((A : Set V) ⊆ Submodule.span K ((b : Set V) ∩ (A : Set V))) ∧
      ∀ [DecidablePred (· ∈ A)], (b.filter (· ∈ A)).card = Module.finrank K A := by
  classical
  have hs : LinearIndepOn K id {x : V | x = e ∧ e ≠ 0} := by
    by_cases h0 : e = 0
    · have : {x : V | x = e ∧ e ≠ 0} = ∅ := by ext x; simp [h0]
      rw [this]; exact linearIndepOn_empty K id
    · have : {x : V | x = e ∧ e ≠ 0} = {e} := by ext x; simp [h0]
      rw [this]; exact LinearIndepOn.singleton (by simpa using h0)
  have hst : {x : V | x = e ∧ e ≠ 0} ⊆ (A : Set V) := by rintro x ⟨rfl, -⟩; exact he
  obtain ⟨bA, hbA, hsbA, hAsp, hliA⟩ := exists_linearIndepOn_id_extension hs hst
  obtain ⟨b, hbB, hbAb, hBsp, hli⟩ := exists_linearIndepOn_id_extension hliA (hbA.trans hAB)
  have hfin : b.Finite := by
    have h1 : LinearIndependent K (fun x : b => (⟨x.1, hbB x.2⟩ : B)) := by
      apply LinearIndependent.of_comp B.subtype
      exact hli
    have := h1.finite
    exact Set.toFinite b
  have hbA' : b ∩ (A : Set V) = bA := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxb, hxA⟩
      by_contra hx
      have h2 : LinearIndependent K (fun x : b => (x : V)) := hli
      have h3 := h2.notMem_span_image (s := {y : b | (y : V) ∈ bA}) (x := ⟨x, hxb⟩) (by simpa using hx)
      apply h3
      have e1 : (fun x : b => (x : V)) '' {y : b | (y : V) ∈ bA} = bA := by
        ext z; constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hz; exact ⟨⟨z, hbAb hz⟩, hz, rfl⟩
      rw [e1]; exact hAsp hxA
    · intro x hx; exact ⟨hbAb hx, hbA hx⟩
  refine ⟨hfin.toFinset, by simpa using hbB, by simpa using hli, by simpa using hBsp,
    fun h0 => by simpa using hbAb (hsbA ⟨rfl, h0⟩), by simpa [hbA'] using hAsp, ?_⟩
  intro _
  have e2 : ((hfin.toFinset.filter (· ∈ A) : Finset V) : Set V) = bA := by
    rw [← hbA']; ext x; simp
  have h4 : LinearIndepOn K id ((hfin.toFinset.filter (· ∈ A) : Finset V) : Set V) := by rw [e2]; exact hliA
  have e3 : Submodule.span K bA = A := le_antisymm (Submodule.span_le.mpr hbA) hAsp
  rw [← finrank_span_finset_eq_card h4, e2, e3]
end Formalism.CountingSumsFrames
