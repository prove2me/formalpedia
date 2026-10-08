-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_esscher_excursion_identity_given_root
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:15:43.001997+00:00
-- url     : https://prove2.me/submissions/745b136c-4084-4057-be33-f8f2999abacc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_excursion_measure_given_root
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_of_finite_pos_noAtoms

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
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (V : ℝ → ℝ) (μ : Measure ℝ),
      NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) ∧
      (∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        V b = V a * Real.exp (∫ t in a..b, μ.real (Ici t))) := by
  obtain ⟨V, μ, hnull, hfinite, htilt, hint⟩ :=
    bv_ac_esscher_excursion_measure_given_root
      X hX q hq W hW hbv hac φ hφ hroot
  letI : NullSingletonClass μ := hnull
  refine ⟨V, μ, hnull, hfinite, ?_, htilt, hint⟩
  exact continuousOn_measureReal_Ici_of_finite_pos_noAtoms μ hfinite
