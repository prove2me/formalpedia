-- Prove2me | solution 1 for AvramDividend.Classical.positive_causal_convolution_continuousOn_locally_integrable_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T18:56:48.73108+00:00
-- url     : https://prove2.me/submissions/b4a9d017-62a5-4860-9a21-2f46b50f98f9

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuousOn_local_right

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical

/-- Locally integrable causal kernels yield continuous positive-time
convolutions against a continuous zero-extended right factor. -/
theorem solution (f g : ℝ → ℝ)
    (hf : ∀ R : ℝ, 0 < R → IntegrableOn f (Ioc (0 : ℝ) R) volume)
    (hg : Continuous ((Ioi (0 : ℝ)).indicator g)) :
    ContinuousOn
      (MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℝ) volume)
      (Ioi (0 : ℝ)) := by
  intro x hx
  let R : ℝ := x + 1
  have hxR : x < R := by dsimp [R]; linarith
  have hR : 0 < R := lt_trans hx hxR
  let fR : ℝ → ℝ := (Ioc (0 : ℝ) R).indicator f
  have hfR : IntegrableOn fR (Ioi (0 : ℝ)) volume :=
    ((hf R hR).integrable_indicator measurableSet_Ioc).integrableOn
  have hcont :=
    positive_causal_convolution_continuousOn_local_right fR g hfR hg
  have hlocal : ∀ y ∈ Ioo (0 : ℝ) R,
      MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℝ) volume y =
      MeasureTheory.posConvolution fR g (ContinuousLinearMap.mul ℝ ℝ) volume y := by
    intro y hy
    change (Ioi (0 : ℝ)).indicator
        (fun z => ∫ t in (0 : ℝ)..z, f t * g (z - t) ∂volume) y =
      (Ioi (0 : ℝ)).indicator
        (fun z => ∫ t in (0 : ℝ)..z, fR t * g (z - t) ∂volume) y
    rw [Set.indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy.1),
      Set.indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy.1)]
    rw [intervalIntegral.integral_of_le (le_of_lt hy.1),
      intervalIntegral.integral_of_le (le_of_lt hy.1)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hmem : t ∈ Ioc (0 : ℝ) R := ⟨ht.1, le_trans ht.2 (le_of_lt hy.2)⟩
    simp only [fR, Set.indicator_of_mem hmem]
  have hev : (MeasureTheory.posConvolution f g
      (ContinuousLinearMap.mul ℝ ℝ) volume) =ᶠ[nhdsWithin x (Ioi (0 : ℝ))]
      (MeasureTheory.posConvolution fR g
        (ContinuousLinearMap.mul ℝ ℝ) volume) := by
    have hn : Ioo (0 : ℝ) R ∈ nhds x :=
      isOpen_Ioo.mem_nhds ⟨hx, hxR⟩
    have hne : ∀ᶠ y in nhds x, y ∈ Ioo (0 : ℝ) R := hn
    have hne' : ∀ᶠ y in nhdsWithin x (Ioi (0 : ℝ)), y ∈ Ioo (0 : ℝ) R :=
      hne.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    filter_upwards [hne'] with y hy
    exact hlocal y hy
  exact (hcont x hx).congr_of_eventuallyEq_of_mem hev hx
