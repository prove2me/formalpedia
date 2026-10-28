-- Prove2me | solution 1 for AvramDividend.Classical.levy_downward_grid_limsup_of_actual_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:25:32.789543+00:00
-- url     : https://prove2.me/submissions/0d69fa26-414e-4d2d-b7ae-8028ad1fe26c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_downward_grid_limsup_of_bracketed_jump
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal

/-- A genuine negative left jump of a spectrally negative Lévy sample path
is observed on every sufficiently fine convergent bracket grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → Finset (ℝ≥0 × ℝ≥0))
    (s u : ℕ → ℝ≥0) (ω : Ω) (t : ℝ≥0) (a : ℝ)
    (hgrid : ∀ n, (s n, u n) ∈ grid n)
    (hs : Tendsto s atTop (nhdsWithin t (Iio t)))
    (hu : Tendsto u atTop (nhdsWithin t (Ici t)))
    (hjump : ∃ left : ℝ,
      Tendsto (fun z : ℝ≥0 => X.X z ω)
        (nhdsWithin t (Iio t)) (nhds left) ∧
      X.X t ω - left < -a) :
    (fun z : ℝ≥0 => X.X z ω) ∈
      (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n},
        ⋃ ij ∈ grid n.1,
          {f : ℝ≥0 → ℝ | f ij.2 - f ij.1 < -a}) := by
  obtain ⟨left, hleft, hneg⟩ := hjump
  exact downward_grid_limsup_of_bracketed_jump grid s u
    (fun z : ℝ≥0 => X.X z ω) t left a hgrid
    (hleft.comp hs) ((X.rightCont ω t).tendsto.comp hu) hneg
