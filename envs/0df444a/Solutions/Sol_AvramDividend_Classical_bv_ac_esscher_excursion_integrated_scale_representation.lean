-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_esscher_excursion_integrated_scale_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:52:42.045681+00:00
-- url     : https://prove2.me/submissions/80001c25-670a-4201-8f6c-6b24fc69fbb2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
-- Submit only after these two authoritative child publications are verified.
import Theorems.Thm_AvramDividend_Classical_bv_ac_tilted_excursion_height_package
import Theorems.Thm_AvramDividend_Classical_esscher_interval_representation_transfer

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t))) := by
  obtain ⟨φ, V, μ, hφ, hnull, hfinite, hcont, htilt, hint⟩ :=
    AvramDividend.Classical.bv_ac_tilted_excursion_height_package
      X hX q hq W hW hbv hac
  refine ⟨φ, μ, hφ, hnull, hfinite, hcont, ?_⟩
  exact AvramDividend.Classical.esscher_interval_representation_transfer
    W V φ μ hcont htilt hint
