-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldrow_prod_rowDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:09.7339+00:00
-- url     : https://prove2.me/submissions/6afd07cf-5e91-44b7-a363-a855414a7138

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R) (u : Fin k × Fin n →₀ ℕ) :
    (u.prod fun v e => t v.1 ^ e) = ∏ a : Fin k, t a ^ rowDeg u a := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun v => pow_zero _), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  show ∏ y, t a ^ u (a, y) = _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl
end Formalism.GradedWeylDivisibility
