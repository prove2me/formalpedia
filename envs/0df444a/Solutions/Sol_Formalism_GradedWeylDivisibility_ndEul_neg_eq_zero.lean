-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ndEul_neg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:16.109005+00:00
-- url     : https://prove2.me/submissions/dd368683-cf5b-490a-819e-482833a3b678

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndEul_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
set_option linter.unusedSimpArgs false
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution [IsDomain R] [CharZero R] {g : MvPolynomial (Fin r × Fin n) R}
    (s : Fin n) (h : ndEul R r n s g = -g) : g = 0 := by
  ext m
  have h1 := congrArg (coeff m) h
  rw [ndEul_coeff, coeff_neg] at h1
  have h2 : ((Finsupp.weight (fun v => colW r n v s) m : R) + 1) * coeff m g = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (Nat.cast_add_one_ne_zero _)
  · simpa using h3
end Formalism.GradedWeylDivisibility
