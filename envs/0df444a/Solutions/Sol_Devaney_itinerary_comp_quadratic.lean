-- Prove2me | solution 1 for Devaney.itinerary_comp_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T21:11:51.848603+00:00
-- url     : https://prove2.me/submissions/12d6936d-81ac-48ca-8a66-1078ebe8d395

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DevFix

open Devaney

/-- Theorem 7.3: the itinerary map intertwines `Fμ` with the shift.  The hypothesis that `x`
lies in `Λ` is not needed: the identity is the reindexing `Fμⁿ(Fμ x) = Fμⁿ⁺¹(x)`, which holds
for every real `x`. -/
theorem itinerary_comp_quadratic (μ : ℝ) (x : ℝ) (hx : x ∈ Lambda μ) :
    itinerary μ (quadratic μ x) = shift (itinerary μ x) := by
  funext n
  show (if (quadratic μ)^[n] (quadratic μ x) ≤ 1 / 2 then (0 : Fin 2) else 1)
      = (if (quadratic μ)^[n + 1] x ≤ 1 / 2 then (0 : Fin 2) else 1)
  rw [← Function.iterate_succ_apply]

end DevFix

open Devaney in
theorem solution (μ : ℝ) (x : ℝ) (hx : x ∈ Lambda μ) :
    itinerary μ (quadratic μ x) = shift (itinerary μ x) :=
  DevFix.itinerary_comp_quadratic μ x hx
