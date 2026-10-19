-- Prove2me | solution 1 for CohnElkies.intervalIntegral_stripPoissonKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/dc98fe0c-1e03-4208-a21c-bee98745caf0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonPrimitive_hasDerivAt
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable

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
    (a b : ℝ) :
    (∫ x in a..b, stripPoissonKernel σ x) =
      stripPoissonPrimitive σ b -
        stripPoissonPrimitive σ a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact stripPoissonPrimitive_hasDerivAt hbelow habove x
  · exact (stripPoissonKernel_integrable hbelow habove).intervalIntegrable
end CohnElkies
