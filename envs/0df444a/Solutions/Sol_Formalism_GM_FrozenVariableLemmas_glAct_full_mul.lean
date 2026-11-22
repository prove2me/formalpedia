-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.glAct_full_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:37.361385+00:00
-- url     : https://prove2.me/submissions/908a5ead-4200-42e9-9250-8300d6febdc0

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_apply

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
theorem _root_.solution (F G : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    M.glAct p L K c ρ (F * G) = F * M.glAct p L K c ρ G + G * M.glAct p L K c ρ F := by
  rw [glAct_full_apply, glAct_full_apply, glAct_full_apply, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
end Formalism.GM.FrozenVariableLemmas
