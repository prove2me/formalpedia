-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.glAct_full_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:43.52851+00:00
-- url     : https://prove2.me/submissions/b1b0a2fa-ade9-4907-9c23-56929f0fb000

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_mul
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} (L : M.Letters K) (c ρ : Fin r)
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution (F : MvPolynomial (Fin K × Fin r) ℚ_[p]) (hF : M.glAct p L K c ρ F = 0)
    (k : ℕ) : M.glAct p L K c ρ (F ^ k) = 0 := by
  induction k with
  | zero => rw [pow_zero, ← C_1, glAct_full_C]
  | succ k ih => rw [pow_succ, glAct_full_mul, hF, ih, mul_zero, mul_zero, add_zero]
end Formalism.GM.FrozenVariableLemmas
