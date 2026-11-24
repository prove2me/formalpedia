-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.diff_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:40.794198+00:00
-- url     : https://prove2.me/submissions/9878db09-c260-46ff-8bdb-83642561d834

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_full_mul
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_full_C
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_diff_gen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (ρ c : Fin r) (hc : c ≠ ρ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    X (Fin.last N, ρ) * pderiv (Fin.last N, c) (aeval (freezeSub p LL ρ) f) =
      aeval (freezeSub p LL ρ) (glAct p LL N c ρ f) := by
  induction f using MvPolynomial.induction_on
  · rename_i a
    rw [glAct_full_C, map_zero, aeval_C]
    simp
  · rename_i f g hf hg
    simp only [map_add, mul_add, hf, hg]
  · rename_i f x hf
    have e1 := diff_gen p LL ρ c hc x
    rw [map_mul (aeval (Formalism.GM.M.freezeSub p LL ρ)) f (X x), Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      glAct_full_mul, map_add (aeval (Formalism.GM.M.freezeSub p LL ρ)), map_mul (aeval (Formalism.GM.M.freezeSub p LL ρ)),
      map_mul (aeval (Formalism.GM.M.freezeSub p LL ρ)), ← hf, ← e1, aeval_X]
    ring
end Formalism.GM.FrozenVariableComponents
