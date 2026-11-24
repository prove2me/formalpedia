-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.rep_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:16.359638+00:00
-- url     : https://prove2.me/submissions/4747c29b-ab83-4f2d-a298-4bc2c3e27dd1

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_supp_of_supported
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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (VF : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) (j0 : ℕ)
    {z : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hz : z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ VF, ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)},
      x = g * q}) :
    ∃ s : Finset (Fin N × Fin r →₀ ℕ), ∃ a : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ b ∈ s, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → b v = 0) ∧ (∀ b, a b ∈ VF) ∧
        z = ∑ b ∈ s, a b * monomial b 1 := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, q, hq, rfl⟩ := hx
    refine ⟨q.support, fun b => coeff b q • g, ?_, fun b => VF.smul_mem _ hg, ?_⟩
    · intro b hb v hv
      by_contra hne
      have := supp_of_supported hq b hb v hne
      simp only [Set.mem_setOf_eq] at this
      omega
    · conv_lhs => rw [q.as_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_mul_assoc, ← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]
  | zero => exact ⟨∅, fun _ => 0, by simp, fun _ => VF.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s1, a1, hs1, ha1, rfl⟩ := hx
    obtain ⟨s2, a2, hs2, ha2, rfl⟩ := hy
    refine ⟨s1 ∪ s2, fun b => (if b ∈ s1 then a1 b else 0) + (if b ∈ s2 then a2 b else 0), ?_, ?_, ?_⟩
    · intro b hb; rcases Finset.mem_union.mp hb with h | h
      · exact hs1 b h
      · exact hs2 b h
    · intro b
      refine VF.add_mem ?_ ?_ <;> split_ifs <;> first | exact ha1 b | exact ha2 b | exact VF.zero_mem
    · simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]
  | smul c x _ hx =>
    obtain ⟨s, a, hs, ha, rfl⟩ := hx
    refine ⟨s, fun b => c • a b, hs, fun b => VF.smul_mem c (ha b), ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_assoc]
end Formalism.GM.DimensionMonotonicity
