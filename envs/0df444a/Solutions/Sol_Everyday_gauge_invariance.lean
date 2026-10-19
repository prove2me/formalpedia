-- Prove2me | solution 1 for Everyday.gauge_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:23:47.081612+00:00
-- url     : https://prove2.me/submissions/42676d64-50d6-4b2e-a210-b342775aeb93

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open Everyday
/-- Other forces: the gauge redundancy. On the discrete spacetime, the
field strength of A is unchanged when A is shifted along every edge by
the discrete gradient of an arbitrary function χ — A x y ↦ A x y +
(χ y - χ x), the discrete analogue of A_μ ↦ A_μ + ∂_μ χ — and so the
gauge sector's functional is unchanged by the shift. -/


theorem solution {X : Type} [Fintype X] (w : X → X → X → ℝ) (A : X → X → ℝ)
    (χ : X → ℝ) :
    gaugeAction w (fun x y => A x y + (χ y - χ x)) = gaugeAction w A := by
  simp only [gaugeAction, gaugeF]
  congr 1; ext x; congr 1; ext y; congr 1; ext z; ring


