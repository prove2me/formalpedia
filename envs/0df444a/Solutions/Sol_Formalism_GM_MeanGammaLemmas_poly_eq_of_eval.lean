-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.poly_eq_of_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:26.676152+00:00
-- url     : https://prove2.me/submissions/c2d05f8f-040f-4739-a6f1-347c9919775f

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [Fact p.Prime] (Q P : ℚ_[p][X]) (S : ℕ) (a : ℚ_[p])
    (h : ∀ n : ℕ, S ≤ n → Q.eval (n : ℚ_[p]) = a * P.eval (n : ℚ_[p])) : Q = C a * P := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + S : ℕ) : ℚ_[p])) ?_ ?_
  · intro x y hxy
    have := Nat.cast_injective hxy
    omega
  · intro n
    simp only [Set.mem_setOf_eq, eval_mul, eval_C]
    exact h _ (by omega)
end Formalism.GM.MeanGammaLemmas
