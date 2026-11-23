-- Prove2me | solution 1 for Formalism.UG.P.prod_X_pow_fun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:06.703793+00:00
-- url     : https://prove2.me/submissions/9dfc8e64-3786-4c17-a210-d6ed3610d340

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (β : n → ℕ) :
    (∏ j, X j ^ β j : MvPolynomial n O) = monomial (Finsupp.equivFunOnFinite.symm β) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype]
  · rfl
  · intro i; simp
end Formalism.UG.P
