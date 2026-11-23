-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.aeval_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:26.940943+00:00
-- url     : https://prove2.me/submissions/0f456eca-7408-4ce6-bf8c-d89662895bb2

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (LL : Letters (N + 1)) (ρ : Fin r) (f : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    aeval (freezeSub p LL ρ) f = ∑ μ ∈ f.support,
      C (coeff μ f) * ∏ v : Fin (N + 1) × Fin r, freezeSub p LL ρ v ^ μ v := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  apply sum_congr rfl
  intro μ _
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.algebraMap_eq]
end Formalism.GM.gammaIntegralityLemmas
