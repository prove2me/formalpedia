-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.abel_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:37.783089+00:00
-- url     : https://prove2.me/submissions/0453c0ce-7afa-4857-baba-13edfad60d84

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
variable {r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (r : ℕ) (δ t : ℕ → ℤ) (hD : ∀ k ≤ r, 0 ≤ ∑ c ∈ range k, δ c)
    (hT : ∑ c ∈ range r, δ c = 0) (ht : ∀ c, c + 1 < r → 2 ≤ t c - t (c + 1)) :
    0 ≤ ∑ c ∈ range r, t c * δ c ∧ (∑ c ∈ range r, t c * δ c = 0 → ∀ c < r, δ c = 0) := by
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℤ, ∀ k, D k = ∑ i ∈ range k, δ i := ⟨_, fun k => rfl⟩
  have hD0 : D 0 = 0 := by rw [hDdef]; simp
  have hDs : ∀ k, D (k + 1) = D k + δ k := fun k => by rw [hDdef, hDdef, Finset.sum_range_succ]
  have hDnn : ∀ k ≤ r, 0 ≤ D k := fun k hk => by rw [hDdef]; exact hD k hk
  have hDr : D r = 0 := by rw [hDdef]; exact hT
  have hid : ∀ n, ∑ c ∈ range n, t c * δ c =
      ∑ c ∈ range n, (t c - t (c + 1)) * D (c + 1) + t n * D n := by
    intro n
    induction n with
    | zero => simp [hD0]
    | succ n ih =>
      rw [Finset.sum_range_succ (fun c => t c * δ c), ih,
        Finset.sum_range_succ (fun c => (t c - t (c + 1)) * D (c + 1)), hDs n]
      ring
  have hterm : ∀ c ∈ range r, 0 ≤ (t c - t (c + 1)) * D (c + 1) := by
    intro c hc
    rw [Finset.mem_range] at hc
    by_cases hcr : c + 1 < r
    · exact mul_nonneg (by linarith [ht c hcr]) (hDnn (c + 1) (by omega))
    · have hc1 : c + 1 = r := by omega
      rw [hc1, hDr, mul_zero]
  rw [hid r, hDr, mul_zero, add_zero]
  refine ⟨Finset.sum_nonneg hterm, fun h0 c hc => ?_⟩
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h0
  have hDz : ∀ k, k ≤ r → D k = 0 := by
    intro k hk
    rcases k with _ | c'
    · exact hD0
    · by_cases hcr : c' + 1 < r
      · have h1 := hall c' (Finset.mem_range.mpr (by omega))
        have h2 := ht c' hcr
        rcases mul_eq_zero.mp h1 with h3 | h3
        · omega
        · exact h3
      · have hc1 : c' + 1 = r := by omega
        rw [hc1, hDr]
  have h5 := hDs c
  rw [hDz (c + 1) (by omega), hDz c (by omega)] at h5
  linarith
end Formalism.GM.DimensionMonotonicity
