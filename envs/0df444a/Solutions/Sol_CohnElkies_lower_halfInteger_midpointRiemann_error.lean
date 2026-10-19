-- Prove2me | solution 1 for CohnElkies.lower_halfInteger_midpointRiemann_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/c05bccc5-afd6-4bc3-bbd4-26dd0f39aebf

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerRiemannLog_monotoneOn
import Theorems.Thm_CohnElkies_monotone_midpointIntegral_error

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {T : ℝ} (hT : T ≠ 0)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    |ℓ * (∫ x in (0 : ℝ)..((k : ℝ) / ℓ), lowerRiemannLog T x) -
        ∑ j ∈ Finset.range k,
          lowerRiemannLog T (((j : ℝ) + 1 / 2) / ℓ)| ≤
      lowerRiemannLog T ((k : ℝ) / ℓ) - lowerRiemannLog T 0 := by
  have hscaled :
      MonotoneOn (fun x : ℝ => lowerRiemannLog T (x / ℓ))
        (Icc (0 : ℝ) (k : ℝ)) := by
    intro x hx y hy hxy
    apply lowerRiemannLog_monotoneOn hT
    · exact div_nonneg hx.1 hℓ.le
    · exact div_nonneg hy.1 hℓ.le
    · exact div_le_div_of_nonneg_right hxy hℓ.le
  have hmid := monotone_midpointIntegral_error
    (fun x : ℝ => lowerRiemannLog T (x / ℓ)) k hscaled
  have hscale :
      (∫ x in (0 : ℝ)..(k : ℝ), lowerRiemannLog T (x / ℓ)) =
        ℓ * ∫ x in (0 : ℝ)..((k : ℝ) / ℓ),
          lowerRiemannLog T x := by
    simpa using!
      (intervalIntegral.integral_comp_div
        (a := (0 : ℝ)) (b := (k : ℝ))
        (lowerRiemannLog T) hℓ.ne')
  rw [hscale] at hmid
  simpa using! hmid
end CohnElkies
