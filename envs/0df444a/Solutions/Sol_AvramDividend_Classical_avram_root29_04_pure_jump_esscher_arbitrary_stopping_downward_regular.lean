-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_04_pure_jump_esscher_arbitrary_stopping_downward_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:38:41.637982+00:00
-- url     : https://prove2.me/submissions/d988772e-ce59-4691-b97b-49740e1c338e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_ae_negative_near_zero_of_grid
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_absolutelyContinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- An arbitrary genuine finite stopping time has immediately negative
post-stopping increments under the actual finite-clock Esscher law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    ∀ᵐ ω ∂(P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X T ω - (T : ℝ) * X.ψ θ)))),
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          X.X (τ ω + s) ω - X.X (τ ω) ω < 0 := by
  have hPath : Measurable
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) := by
    apply measurable_pi_lambda
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hSlope := ae_rogozin_slopes_of_infinite_small_jumps X hvar
  have hOrigReg : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 :=
    ae_negative_near_zero_of_ae_rogozin_negative_slopes X hSlope
  have hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0 := by
    filter_upwards [hOrigReg] with ω hω
    intro n
    exact (levy_negative_before_horizon_iff_dense_grid
      X times hdense ω (horizons n)).mp
      (hω (horizons n) (hpos n))
  have hStoppedReg : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (τ ω + s) ω - X.X (τ ω) ω < 0 :=
    levy_finiteStopping_ae_negative_near_zero_of_grid
      X τ hτ hstop hPath times horizons hcofinal hGridAE
  exact ae_negative_near_zero_of_absolutelyContinuous
    P
    (P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
    (fun s ω => X.X (τ ω + s) ω - X.X (τ ω) ω)
    (withDensity_absolutelyContinuous P _) hStoppedReg
