-- Prove2me | solution 1 for BalancedAlgebra.quiver_star_idem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T15:45:12.52857+00:00
-- url     : https://prove2.me/submissions/b53fa247-ee28-4899-a848-dce617119e05

import Mathlib
import Definitions.Def_BalancedAlgebra_core

set_option linter.unusedSectionVars false

namespace BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra

/-- The two derived idempotence laws of a quiver. -/
theorem quiver_star_idem {A : Type*} (dom cod : A → A)
    (h1 : ∀ a : A, dom (cod a) = cod a) (h2 : ∀ a : A, cod (dom a) = dom a) (a : A) :
    cod (cod a) = cod a ∧ dom (dom a) = dom a := by
  constructor
  · have h := h2 (cod a)
    rwa [h1 a] at h
  · have h := h1 (dom a)
    rwa [h2 a] at h

end BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra in
theorem solution {A : Type*} (dom cod : A → A)
    (h1 : ∀ a : A, dom (cod a) = cod a) (h2 : ∀ a : A, cod (dom a) = dom a) (a : A) :
    cod (cod a) = cod a ∧ dom (dom a) = dom a :=
  BAFix.quiver_star_idem dom cod h1 h2 a
