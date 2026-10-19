-- Prove2me | solution 1 for CohnElkies.upperShortShellVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/df6b0a99-3deb-4b20-afc3-4fff75a2b4fc

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε δ : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Set.Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a) :
    0 ≤ upperShortShellVariance ε δ := by
  unfold upperShortShellVariance
  apply intervalIntegral.integral_nonneg horder
  intro a ha
  have ha₀ : 0 < shortCutoff ε := by
    unfold shortCutoff
    positivity
  have hapos : 0 < a := ha₀.trans_le ha.1
  have hdensity : 0 ≤ -shortShellDensity ε a := by
    unfold shortShellDensity
    have hn : 0 ≤ shortMargin ε a * Real.exp (-2 * a) :=
      mul_nonneg (hmargin a ha) (Real.exp_pos _).le
    have hd : 0 < 2 * a ^ 2 * Real.cosh a := by
      positivity
    simpa using! div_nonneg hn hd.le
  exact mul_nonneg
    (mul_nonneg hdensity (sq_nonneg a))
    (Real.cosh_pos _).le
end CohnElkies
