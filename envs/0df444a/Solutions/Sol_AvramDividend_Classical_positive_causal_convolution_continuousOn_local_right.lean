-- Prove2me | solution 1 for AvramDividend.Classical.positive_causal_convolution_continuousOn_local_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T18:18:45.992142+00:00
-- url     : https://prove2.me/submissions/985a98cc-ef01-4e32-ba64-fa42821e2628

import Mathlib.Analysis.Convolution
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter

/-- An integrable positive-time kernel convolved with a continuous causal
right factor is continuous on positive times, without a global bound. -/
theorem solution
    (f g : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hg : Continuous ((Ioi (0 : ℝ)).indicator g)) :
    ContinuousOn
      (MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℝ) volume)
      (Ioi (0 : ℝ)) := by
  intro x hx
  let R : ℝ := x + 1
  have hxR : x < R := by dsimp [R]; linarith
  obtain ⟨χ, hχone, hχsupp, -, -⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (K := Icc (0 : ℝ) R) (V := Set.univ)
      isCompact_Icc isOpen_univ (subset_univ _)
  let gR : ℝ → ℝ := fun t => (Ioi (0 : ℝ)).indicator g t * χ t
  have hgR : Continuous gR := hg.mul χ.continuous
  have hCompact : HasCompactSupport gR := by
    exact (show HasCompactSupport (χ : ℝ → ℝ) from hχsupp).mul_left
  have hfi : Integrable ((Ioi (0 : ℝ)).indicator f) volume :=
    hf.integrable_indicator measurableSet_Ioi
  have hcont : Continuous
      (MeasureTheory.convolution ((Ioi (0 : ℝ)).indicator f) gR
        (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hCompact.continuous_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hfi.locallyIntegrable hgR
  have hlocal : ∀ y ∈ Ioo (0 : ℝ) R,
      MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℝ) volume y =
      MeasureTheory.convolution ((Ioi (0 : ℝ)).indicator f) gR
        (ContinuousLinearMap.mul ℝ ℝ) volume y := by
    intro y hy
    have heq := MeasureTheory.posConvolution_eq_convolution_indicator
      f g (ContinuousLinearMap.mul ℝ ℝ) volume
    rw [heq]
    simp only [MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards [] with t
    change ((Ioi (0 : ℝ)).indicator f t) *
        ((Ioi (0 : ℝ)).indicator g (y - t)) =
      ((Ioi (0 : ℝ)).indicator f t) * gR (y - t)
    by_cases ht : 0 < t
    · by_cases hyt : 0 < y - t
      · have hbound : y - t ∈ Icc (0 : ℝ) R := by
          constructor
          · exact le_of_lt hyt
          · have : y < R := hy.2
            linarith
        simp [gR, hχone hbound]
      · have hnot : y - t ∉ Ioi (0 : ℝ) := hyt
        simp only [gR, Set.indicator_of_notMem hnot, mul_zero, zero_mul]
    · have hnot : t ∉ Ioi (0 : ℝ) := ht
      simp only [Set.indicator_of_notMem hnot, zero_mul]
  have hev : (MeasureTheory.posConvolution f g
      (ContinuousLinearMap.mul ℝ ℝ) volume) =ᶠ[nhdsWithin x (Ioi (0 : ℝ))]
      (MeasureTheory.convolution ((Ioi (0 : ℝ)).indicator f) gR
        (ContinuousLinearMap.mul ℝ ℝ) volume) := by
    have hn : Ioo (0 : ℝ) R ∈ nhds x :=
      isOpen_Ioo.mem_nhds ⟨hx, hxR⟩
    have hne : ∀ᶠ y in nhds x, y ∈ Ioo (0 : ℝ) R := hn
    have hne' : ∀ᶠ y in nhdsWithin x (Ioi (0 : ℝ)), y ∈ Ioo (0 : ℝ) R :=
      hne.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    filter_upwards [hne'] with y hy
    exact hlocal y hy
  exact hcont.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem hev hx
