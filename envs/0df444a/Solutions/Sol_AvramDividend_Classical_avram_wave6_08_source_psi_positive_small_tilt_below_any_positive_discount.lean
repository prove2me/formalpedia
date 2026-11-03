-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:58:57.008295+00:00
-- url     : https://prove2.me/submissions/3a0fccbf-85cf-49eb-89dd-66452e2d85fc

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Neighborhoods
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ X.ψ θ < q := by
  have hcont : ContinuousWithinAt X.ψ (Ioi (0 : ℝ)) 0 :=
    ((levy_laplace_exponent_continuousOn_nonnegative X) 0
      (show (0 : ℝ) ∈ Ici 0 by simp)).mono (by
        intro y hy
        exact le_of_lt (Set.mem_Ioi.mp hy))
  have hnhds : (Iio q : Set ℝ) ∈ 𝓝 (X.ψ 0) := by
    rw [levy_laplace_exponent_zero X]
    exact IsOpen.mem_nhds isOpen_Iio hq
  have hEv : ∀ᶠ θ in 𝓝[Ioi (0 : ℝ)] (0 : ℝ), X.ψ θ < q :=
    hcont.tendsto.eventually hnhds
  have hEvPos : ∀ᶠ θ in 𝓝[Ioi (0 : ℝ)] (0 : ℝ), 0 < θ :=
    self_mem_nhdsWithin
  obtain ⟨θ, hθψ, hθpos⟩ := (hEv.and hEvPos).exists
  exact ⟨θ, hθpos, hθψ⟩
