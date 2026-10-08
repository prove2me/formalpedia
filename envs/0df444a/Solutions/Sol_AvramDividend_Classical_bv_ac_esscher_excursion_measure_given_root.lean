-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_esscher_excursion_measure_given_root
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:17:21.963154+00:00
-- url     : https://prove2.me/submissions/bc934190-de44-4e74-944a-d7dc6be4a356
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_ac_tilted_log_derivative_shape_given_root
import Theorems.Thm_AvramDividend_Classical_atomless_positive_tail_measure_of_antitone_continuous
import Theorems.Thm_AvramDividend_Classical_interval_exponential_of_positive_log_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (V : ℝ → ℝ) (μ : Measure ℝ),
      NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        V b = V a * Real.exp (∫ t in a..b, μ.real (Ici t))) := by
  obtain ⟨V, g, hVpos, hgcont, hganti, hgnonneg, hglim, htilt, hVderiv⟩ :=
    bv_ac_tilted_log_derivative_shape_given_root
      X hX q hq W hW hbv hac φ hφ hroot
  obtain ⟨μ, hnull, hfinite, htail⟩ :=
    atomless_positive_tail_measure_of_antitone_continuous
      g hgcont hganti hgnonneg hglim
  have hExp :=
    interval_exponential_of_positive_log_derivative
      V g hVpos hgcont hVderiv
  refine ⟨V, μ, hnull, hfinite, htilt, ?_⟩
  intro a b ha hab
  have heq :
      (∫ t in a..b, g t) =
        (∫ t in a..b, μ.real (Ici t)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using hx
    exact (htail x (lt_of_lt_of_le ha hxI.1)).symm
  calc
    V b = V a * Real.exp (∫ t in a..b, g t) := hExp a b ha hab
    _ = V a * Real.exp (∫ t in a..b, μ.real (Ici t)) := by
      rw [heq]
