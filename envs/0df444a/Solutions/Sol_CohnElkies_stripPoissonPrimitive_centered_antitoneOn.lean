-- Prove2me | solution 1 for CohnElkies.stripPoissonPrimitive_centered_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/d10b49c3-993d-4cbe-9c5d-383624822aac

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_antitone_abs
import Theorems.Thm_CohnElkies_stripPoissonPrimitive_centered_hasDerivAt

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
    {r : ℝ} (hr : 0 ≤ r) :
    AntitoneOn
      (fun s : ℝ =>
        stripPoissonPrimitive σ (s + r) -
          stripPoissonPrimitive σ (s - r))
      (Ici (0 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro x hx
    exact
      (stripPoissonPrimitive_centered_hasDerivAt
        hbelow habove r x).continuousAt.continuousWithinAt
  · intro x hx
    exact
      (stripPoissonPrimitive_centered_hasDerivAt
        hbelow habove r x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxpos : 0 ≤ x := by
      have hx' : 0 < x := by simpa using! hx
      exact hx'.le
    rw [(stripPoissonPrimitive_centered_hasDerivAt
      hbelow habove r x).deriv]
    apply sub_nonpos.mpr
    apply stripPoissonKernel_antitone_abs hbelow habove
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    nlinarith [mul_nonneg hxpos hr]
end CohnElkies
