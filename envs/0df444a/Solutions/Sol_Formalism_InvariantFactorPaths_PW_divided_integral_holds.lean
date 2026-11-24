-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.divided_integral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:59:37.791347+00:00
-- url     : https://prove2.me/submissions/ac830d09-c549-47b4-8705-e7c8c99e62c6

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_divPow_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_divPow_X_int
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_divPow_C_int
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


section
namespace Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
section fockForm
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end fockForm
section divided
variable {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A]
end divided
section glDivided
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
private theorem glAct_eq_sum_X_mul_pderiv (LL : Letters N) (j : ℕ) (c d : Fin r)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d F = ∑ i : Fin N, if (i : ℕ) < j then
      (if LL.vec i = true then X (i, c) * pderiv (i, d) F else -(X (i, d) * pderiv (i, c) F))
      else 0 := by
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp
end glDivided
private theorem glAct_mul_eq_mul_glAct_add_mul_glAct {p : ℕ} [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r)
    (a b : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d (a * b) = a * glAct p LL j c d b + b * glAct p LL j c d a := by
  rw [glAct_eq_sum_X_mul_pderiv, glAct_eq_sum_X_mul_pderiv, glAct_eq_sum_X_mul_pderiv, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Derivation.leibniz] <;> ring
end Formalism.InvariantFactorPaths.PW
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : DivInt := by
  intro p _ N r LL j c d hcd k x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
  let Pr : MvPolynomial (Fin N × Fin r) ℚ_[p] → Prop := fun z => ∀ k : ℕ,
    ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p LL j c d) ^ k) z ∈ IntPol p (Fin N × Fin r)
  have hmul : ∀ u w, Pr u → Pr w → Pr (u * w) := by
    intro u w hu hw k
    rw [divPow_mul (glAct p LL j c d) (glAct_mul_eq_mul_glAct_add_mul_glAct LL j c d) k u w]
    refine Submodule.sum_mem _ fun ij _ => ?_
    obtain ⟨u', hu'⟩ := LinearMap.mem_range.1 (hu ij.1)
    obtain ⟨w', hw'⟩ := LinearMap.mem_range.1 (hw ij.2)
    exact LinearMap.mem_range.2 ⟨u' * w', by rw [← hu', ← hw']; simp⟩
  have hadd : ∀ u w, Pr u → Pr w → Pr (u + w) := by
    intro u w hu hw k
    rw [map_add, smul_add]
    exact Submodule.add_mem _ (hu k) (hw k)
  have hall : ∀ y : MvPolynomial (Fin N × Fin r) ℤ_[p],
      Pr (MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) y) := by
    intro y
    induction y using MvPolynomial.induction_on
    next a =>
      rw [map_C]
      exact fun k => divPow_C_int LL j c d a k
    next u w hu hw =>
      rw [map_add]
      exact hadd _ _ hu hw
    next u v hu =>
      rw [map_mul, map_X]
      exact hmul _ _ hu (fun k => divPow_X_int LL j c d hcd v k)
  exact hall y k
end Formalism.InvariantFactorPaths.PW
