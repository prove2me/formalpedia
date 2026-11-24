-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.cas_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:07.859628+00:00
-- url     : https://prove2.me/submissions/8ada2cbd-fe25-4395-a9e6-9ed1f0f371de

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_psum_range
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_abel_ineq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_casI_closed
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
theorem _root_.solution {μ ν : Fin r → ℤ} (hμ : DomW μ) (hν : DomW ν) (h : Dle μ ν) (hne : μ ≠ ν) :
    GlW.casI μ < GlW.casI ν := by
  obtain ⟨E, hE⟩ : ∃ E : (Fin r → ℤ) → ℕ → ℤ, ∀ κ k (h : k < r), E κ k = κ ⟨k, h⟩ :=
    ⟨fun κ k => if h : k < r then κ ⟨k, h⟩ else 0, fun κ k h => dif_pos h⟩
  have hsumE : ∀ κ : Fin r → ℤ, ∑ c : Fin r, κ c = ∑ k ∈ range r, E κ k := by
    intro κ
    rw [← Fin.sum_univ_eq_sum_range (E κ) r]
    exact Finset.sum_congr rfl fun c _ => (hE κ c c.isLt).symm
  have hpsum : ∀ (κ : Fin r → ℤ) k, k ≤ r → psum κ k = ∑ j ∈ range k, E κ j := by
    intro κ k hk
    unfold psum
    rw [hsumE (fun c => if (c : ℕ) < k then κ c else 0), ← psum_range (E κ) hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [hE _ j hj, Fin.val_mk]
  have hS : GlW.casI ν - GlW.casI μ =
      ∑ k ∈ range r, (E ν k + E μ k + ((r : ℤ) - 1 - 2 * k)) * (E ν k - E μ k) := by
    rw [casI_closed ν, casI_closed μ, ← Finset.sum_sub_distrib,
      hsumE (fun c => ν c * (ν c + ((r : ℤ) - 1 - 2 * (c : ℤ))) - μ c * (μ c + ((r : ℤ) - 1 - 2 * (c : ℤ))))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    simp only [hE _ k hk, Fin.val_mk]
    ring
  have hab := abel_ineq r (fun k => E ν k - E μ k) (fun k => E ν k + E μ k + ((r : ℤ) - 1 - 2 * k))
    (fun k hk => by
      show 0 ≤ ∑ c ∈ range k, (E ν c - E μ c)
      rw [Finset.sum_sub_distrib, ← hpsum ν k hk, ← hpsum μ k hk]
      linarith [h.1 k])
    (by
      show ∑ c ∈ range r, (E ν c - E μ c) = 0
      rw [Finset.sum_sub_distrib, ← hsumE ν, ← hsumE μ, h.2, sub_self])
    (fun c hc => by
      show 2 ≤ (E ν c + E μ c + ((r : ℤ) - 1 - 2 * ((c : ℕ) : ℤ))) -
        (E ν (c + 1) + E μ (c + 1) + ((r : ℤ) - 1 - 2 * ((c + 1 : ℕ) : ℤ)))
      have h1 := hμ ⟨c, by omega⟩ ⟨c + 1, hc⟩ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self c))
      have h2 := hν ⟨c, by omega⟩ ⟨c + 1, hc⟩ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self c))
      rw [hE ν c (by omega), hE μ c (by omega), hE ν (c + 1) hc, hE μ (c + 1) hc]
      push_cast
      linarith)
  have h0 : (0 : ℤ) ≤ ∑ k ∈ range r, (E ν k + E μ k + ((r : ℤ) - 1 - 2 * k)) * (E ν k - E μ k) := hab.1
  have hne0 : ∑ k ∈ range r, (E ν k + E μ k + ((r : ℤ) - 1 - 2 * k)) * (E ν k - E μ k) ≠ 0 := by
    intro hz
    apply hne
    funext c
    have h3 : E ν c - E μ c = 0 := hab.2 hz c c.isLt
    rw [hE ν c c.isLt, hE μ c c.isLt] at h3
    simp only [Fin.eta] at h3
    linarith
  rw [← hS] at h0 hne0
  omega
end Formalism.GM.DimensionMonotonicity
