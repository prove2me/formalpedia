-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.glAct_full_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:07.434748+00:00
-- url     : https://prove2.me/submissions/c92522d2-d3e7-49bc-8f8b-86be5b3aca7c

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_apply
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
theorem _root_.solution (LL : Letters N) (c ρ : Fin r) (b : Fin N) (d : Fin r) :
    glAct p LL N c ρ (X (b, d)) =
      if LL.vec b then (if d = ρ then X (b, c) else 0) else (if d = c then -X (b, ρ) else 0) := by
  rw [glAct_apply, Finset.sum_eq_single b]
  · rw [if_pos b.isLt]
    cases hv : LL.vec b
    · by_cases h2 : d = c
      · subst h2
        simp
      · simp [h2]
    · by_cases h1 : d = ρ
      · subst h1
        simp
      · simp [h1]
  · intro i _ hib
    simp [hib]
  · intro h
    exact absurd (Finset.mem_univ b) h
end Formalism.GM.FrozenVariableComponents
