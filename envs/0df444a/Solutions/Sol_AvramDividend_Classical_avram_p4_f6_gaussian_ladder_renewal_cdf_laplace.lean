-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_gaussian_ladder_renewal_cdf_laplace
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:25:54.109937+00:00
-- url     : https://prove2.me/submissions/524c233e-42f4-4cde-8da9-bc5ccbecfd6d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_atomless_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_exponential_tonelli

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ)
    (ν : Measure ℝ)
    (hSupp : ν (Iic (0 : ℝ)) = 0)
    (hAtom : ∀ x : ℝ, ν {x} = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤)
    (hLap : ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y))) (Ioi 0) ν ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) ∂ν = θ / X.ψ θ) :
    ∃ W₀ : ℝ → ℝ,
      (∀ y < 0, W₀ y = 0) ∧
      (∀ y, 0 ≤ y → 0 ≤ W₀ y) ∧
      ContinuousOn W₀ (Ici 0) ∧
      (∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y => Real.exp (-(θ * y)) * W₀ y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * W₀ y = (X.ψ θ)⁻¹) := by
  let W₀ : ℝ → ℝ :=
    fun x => if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0
  refine ⟨W₀, ?_, ?_, ?_, ?_⟩
  · intro y hy
    simp only [W₀, not_le.mpr hy, ↓reduceIte]
  · intro y hy
    simpa only [W₀, if_pos hy] using
      (ENNReal.toReal_nonneg : 0 ≤ (ν (Ioc (0 : ℝ) y)).toReal)
  · exact avram_p4_f6_renewal_cdf_atomless_continuous ν hAtom hFin
  · exact avram_p4_f6_renewal_cdf_exponential_tonelli
      X hX hσ ν hSupp hFin hLap
