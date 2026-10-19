-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryCapped_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/d3fdc115-6da3-4525-ae9c-7e51da46be81

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_continuousOn
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_tendsto_atTop_zero

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R D : ℝ) :
    Continuous (lowerGammaBoundaryCapped ℓ R D) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst y
    have htail :
        ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ),
          D ≤ lowerGammaBoundaryLog ℓ R x :=
      (lowerGammaBoundaryLog_tendsto_atTop_zero
        hℓ R).eventually_ge_atTop D
    have hnear :
        ∀ᶠ x : ℝ in 𝓝 (0 : ℝ),
          x ≠ 0 → D ≤ lowerGammaBoundaryLog ℓ R x := by
      have h := (eventually_nhdsWithin_iff.mp htail)
      filter_upwards [h] with x hx
      intro hxzero
      apply hx
      simpa using! hxzero
    have hconstant :
        ContinuousAt (fun _ : ℝ => D) (0 : ℝ) :=
      continuousAt_const
    apply hconstant.congr_of_eventuallyEq
    filter_upwards [hnear] with x hx
    unfold lowerGammaBoundaryCapped
    split_ifs with hzero
    · rfl
    · exact min_eq_right (hx hzero)
  · have hopen : IsOpen ({(0 : ℝ)}ᶜ) :=
      isClosed_singleton.isOpen_compl
    have hmem : y ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := by
      simpa using! hy
    have hregular :
        ContinuousAt (lowerGammaBoundaryLog ℓ R) y := by
      apply (lowerGammaBoundaryLog_continuousOn hℓ R
        (S := {(0 : ℝ)}ᶜ)
        (by
          intro x hx
          simpa using! hx)).continuousAt
      exact hopen.mem_nhds hmem
    have hmin :
        ContinuousAt (fun x : ℝ =>
          min (lowerGammaBoundaryLog ℓ R x) D) y :=
      hregular.min continuousAt_const
    apply hmin.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hy] with x hx
    simp [lowerGammaBoundaryCapped, hx]
end CohnElkies
