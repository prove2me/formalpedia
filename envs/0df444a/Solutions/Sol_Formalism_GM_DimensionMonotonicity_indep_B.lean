-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.indep_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:25.742803+00:00
-- url     : https://prove2.me/submissions/e2592d21-36c0-41c3-812d-2921f37e6ad7

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (j0 : ℕ) (s : Finset (Fin N × Fin r →₀ ℕ)) (a : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hs : ∀ b ∈ s, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → b v = 0)
    (ha : ∀ b ∈ s, ∀ m ∈ (a b).support, ∀ v : Fin N × Fin r, j0 ≤ (v.1 : ℕ) → m v = 0)
    (h0 : ∑ b ∈ s, a b * monomial b 1 = 0) : ∀ b ∈ s, a b = 0 := by
  classical
  intro b0 hb0
  ext m
  rw [coeff_zero]
  by_contra hne
  have hmA : ∀ v : Fin N × Fin r, j0 ≤ (v.1 : ℕ) → m v = 0 := ha b0 hb0 m (mem_support_iff.mpr hne)
  have := congrArg (coeff (m + b0)) h0
  rw [coeff_zero, coeff_sum, Finset.sum_eq_single b0] at this
  · rw [coeff_mul_monomial', if_pos le_add_self, add_tsub_cancel_right, mul_one] at this
    exact hne this
  · intro b hb hbne
    rw [coeff_mul_monomial']
    split_ifs with hle
    · have : coeff (m + b0 - b) (a b) = 0 := by
        by_contra hc
        have hA := ha b hb (m + b0 - b) (mem_support_iff.mpr hc)
        apply hbne
        ext v
        by_cases hv : (v.1 : ℕ) < j0
        · rw [hs b hb v hv, hs b0 hb0 v hv]
        · have h1 := hA v (by omega)
          have h2 := hmA v (by omega)
          have h3 := hle v
          simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, h2, zero_add] at h1 h3
          omega
      rw [this, zero_mul]
    · rfl
  · intro h; exact absurd hb0 h
end Formalism.GM.DimensionMonotonicity
