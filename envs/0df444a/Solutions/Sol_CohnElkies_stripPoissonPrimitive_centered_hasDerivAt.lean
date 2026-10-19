-- Prove2me | solution 1 for CohnElkies.stripPoissonPrimitive_centered_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/65e09921-6d73-46eb-bbdd-c75552fddb9c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonPrimitive_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (r x : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        stripPoissonPrimitive σ (s + r) -
          stripPoissonPrimitive σ (s - r))
      (stripPoissonKernel σ (x + r) -
        stripPoissonKernel σ (x - r)) x := by
  have hplus :=
    (stripPoissonPrimitive_hasDerivAt hbelow habove (x + r)).comp x
      ((hasDerivAt_id x).add_const r)
  have hminus :=
    (stripPoissonPrimitive_hasDerivAt hbelow habove (x - r)).comp x
      ((hasDerivAt_id x).sub_const r)
  convert! hplus.sub hminus using 1
  all_goals simp
end CohnElkies
