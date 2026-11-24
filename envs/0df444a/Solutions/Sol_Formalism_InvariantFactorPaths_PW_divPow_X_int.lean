-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.divPow_X_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:22.856451+00:00
-- url     : https://prove2.me/submissions/ed204fa8-a9d0-4427-b40a-5d8f0048323f

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_glAct_glAct_X
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_glAct_X_int
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
private theorem X_mem_intPol (w : Fin N × Fin r) :
    (X w : MvPolynomial (Fin N × Fin r) ℚ_[p]) ∈ IntPol p (Fin N × Fin r) :=
  LinearMap.mem_range.2 ⟨X w, by simp⟩
end glDivided
end Formalism.InvariantFactorPaths.PW
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (v : Fin N × Fin r) (k : ℕ) :
    ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p LL j c d) ^ k) (X v) ∈ IntPol p (Fin N × Fin r) := by
  rcases k with _ | _ | k
  · simpa using X_mem_intPol v
  · simpa using glAct_X_int LL j c d v
  · rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply,
      glAct_glAct_X LL j c d hcd v, map_zero, smul_zero]
    exact Submodule.zero_mem _
end Formalism.InvariantFactorPaths.PW
