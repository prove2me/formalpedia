-- Prove2me | solution 1 for CohnElkies.horizontalStripRealTraceExtension_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/a201f087-68f7-4ad4-bfbd-e04a9eb803c4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_horizontalStrip_closed_eq_open_union_edges

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {a b : ℝ} (hab : a < b)
    (H : ℂ → ℝ) (bottom top : ℝ → ℝ)
    (hH : ContinuousOn H (Complex.im ⁻¹' Ioo a b))
    (hbottom : Continuous bottom)
    (htop : Continuous top)
    (hbottomtrace : ∀ s : ℝ,
      Tendsto H
        (𝓝[Complex.im ⁻¹' Ioo a b]
          ((s : ℂ) + Complex.I * (a : ℂ)))
        (𝓝 (bottom s)))
    (htoptrace : ∀ s : ℝ,
      Tendsto H
        (𝓝[Complex.im ⁻¹' Ioo a b]
          ((s : ℂ) + Complex.I * (b : ℂ)))
        (𝓝 (top s))) :
    ContinuousOn
      (horizontalStripRealTraceExtension a b H bottom top)
      (Complex.im ⁻¹' Icc a b) := by
  let E : ℂ → ℝ :=
    horizontalStripRealTraceExtension a b H bottom top
  let O : Set ℂ := Complex.im ⁻¹' Ioo a b
  let L : Set ℂ := Complex.im ⁻¹' {a}
  let T : Set ℂ := Complex.im ⁻¹' {b}
  have hclosedL : IsClosed L := by
    exact isClosed_singleton.preimage Complex.continuous_im
  have hclosedT : IsClosed T := by
    exact isClosed_singleton.preimage Complex.continuous_im
  have hinterior : ∀ z ∈ O, E z = H z := by
    intro z hz
    have hza : z.im ≠ a := ne_of_gt hz.1
    have hzb : z.im ≠ b := ne_of_lt hz.2
    simp [E, horizontalStripRealTraceExtension,
      hza, hzb]
  intro z hz
  have hU : ContinuousWithinAt E O z := by
    by_cases hza : z.im = a
    · have hrepr :
          (z.re : ℂ) + Complex.I * (a : ℂ) = z := by
        apply Complex.ext
        · simp
        · simpa using! hza.symm
      have htrace := hbottomtrace z.re
      rw [hrepr] at htrace
      have hevent : E =ᶠ[𝓝[O] z] H :=
        mem_of_superset self_mem_nhdsWithin hinterior
      change Tendsto E (𝓝[O] z) (𝓝 (E z))
      have hvalue : E z = bottom z.re := by
        simp [E, horizontalStripRealTraceExtension, hza]
      rw [hvalue]
      exact htrace.congr' hevent.symm
    · by_cases hzb : z.im = b
      · have hrepr :
            (z.re : ℂ) + Complex.I * (b : ℂ) = z := by
          apply Complex.ext
          · simp
          · simpa using! hzb.symm
        have htrace := htoptrace z.re
        rw [hrepr] at htrace
        have hevent : E =ᶠ[𝓝[O] z] H :=
          mem_of_superset self_mem_nhdsWithin hinterior
        change Tendsto E (𝓝[O] z) (𝓝 (E z))
        have hvalue : E z = top z.re := by
          simp [E, horizontalStripRealTraceExtension,
            hzb, (ne_of_gt hab : b ≠ a)]
        rw [hvalue]
        exact htrace.congr' hevent.symm
      · have hzO : z ∈ O := by
          exact ⟨lt_of_le_of_ne hz.1 (Ne.symm hza),
            lt_of_le_of_ne hz.2 hzb⟩
        exact (hH z hzO).congr hinterior
          (hinterior z hzO)
  have hL : ContinuousWithinAt E L z := by
    by_cases hza : z ∈ L
    · have hreal : z.im = a := hza
      have hc : Continuous
          (fun w : ℂ => bottom w.re) :=
        hbottom.comp Complex.continuous_re
      apply hc.continuousAt.continuousWithinAt.congr
      · intro w hw
        have hwa : w.im = a := hw
        simp [E, horizontalStripRealTraceExtension, hwa]
      · simp [E, horizontalStripRealTraceExtension, hreal]
    · apply continuousWithinAt_of_notMem_closure
      rw [hclosedL.closure_eq]
      exact hza
  have hT : ContinuousWithinAt E T z := by
    by_cases hzb : z ∈ T
    · have hreal : z.im = b := hzb
      have hc : Continuous
          (fun w : ℂ => top w.re) :=
        htop.comp Complex.continuous_re
      apply hc.continuousAt.continuousWithinAt.congr
      · intro w hw
        have hwb : w.im = b := hw
        have hwa : w.im ≠ a := by
          rw [hwb]
          exact ne_of_gt hab
        simp [E, horizontalStripRealTraceExtension,
          hwb, (ne_of_gt hab : b ≠ a)]
      · have hza : z.im ≠ a := by
          rw [hreal]
          exact ne_of_gt hab
        simp [E, horizontalStripRealTraceExtension,
          hreal, (ne_of_gt hab : b ≠ a)]
    · apply continuousWithinAt_of_notMem_closure
      rw [hclosedT.closure_eq]
      exact hzb
  change ContinuousWithinAt E
    (Complex.im ⁻¹' Icc a b) z
  rw [horizontalStrip_closed_eq_open_union_edges hab]
  exact (hU.union hL).union hT
end CohnElkies
