-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_integral_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/bedd5fcc-eb51-470c-aa29-2f65de10a48d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonPrimitive_hasDerivAt
import Theorems.Thm_CohnElkies_stripPoissonPrimitive_zero
import Theorems.Thm_CohnElkies_stripPoissonPrimitive_tendsto_atTop

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    (∫ T in Ioi (0 : ℝ), stripPoissonKernel σ T) =
      1 / 2 - stripAngle σ / (2 * Real.pi) := by
  calc
    (∫ T in Ioi (0 : ℝ), stripPoissonKernel σ T) =
        (1 / 2 : ℝ) - stripPoissonPrimitive σ 0 := by
      exact integral_Ioi_of_hasDerivAt_of_nonneg'
        (fun T _ => stripPoissonPrimitive_hasDerivAt hbelow habove T)
        (fun T _ => (stripPoissonKernel_pos hbelow habove T).le)
        (stripPoissonPrimitive_tendsto_atTop hbelow habove)
    _ = 1 / 2 - stripAngle σ / (2 * Real.pi) := by
      rw [stripPoissonPrimitive_zero hbelow habove]
end CohnElkies
