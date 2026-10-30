-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_04_esscher_pure_jump_path_law_downward_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:22:05.616997+00:00
-- url     : https://prove2.me/submissions/edc53ff4-4005-491c-b934-2c246006cd08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_esscher_fixed_horizon_downward_regular
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Theorems.Thm_AvramDividend_Classical_measurableSet_countable_schedule_negative_near_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- The actual finite-clock Esscher path pushforward law is downward regular. -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    ∀ᵐ f ∂Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω)
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp
          (θ * X.X T ω - (T : ℝ) * X.ψ θ)))),
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ f s < 0 := by
  let Q : Measure Ω := P.withDensity (fun ω : Ω =>
    ENNReal.ofReal (Real.exp
      (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
  have hPath : Measurable
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) := by
    apply measurable_pi_lambda
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hRegQ : ∀ᵐ ω ∂Q,
      ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 :=
    avram_root29_04_pure_jump_esscher_fixed_horizon_downward_regular
      X hvar θ hθ T
  have hGridQ : ∀ᵐ ω ∂Q, ∀ n : ℕ,
      ∃ m : ℕ, times m < horizons n ∧
        X.X (times m) ω < 0 := by
    filter_upwards [hRegQ] with ω hω
    intro n
    exact (levy_negative_before_horizon_iff_dense_grid
      X times hdense ω (horizons n)).mp
      (hω (horizons n) (hpos n))
  have hGridLaw : ∀ᵐ f ∂Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) Q,
      ∀ n : ℕ, ∃ m : ℕ,
        times m < horizons n ∧ f (times m) < 0 := by
    exact (ae_map_iff hPath.aemeasurable
      (measurableSet_countable_schedule_negative_near_zero
        times horizons)).mpr hGridQ
  filter_upwards [hGridLaw] with f hf
  intro ε hε
  obtain ⟨j, hj⟩ := hcofinal ε hε
  obtain ⟨m, hm, hneg⟩ := hf j
  exact ⟨times m, lt_of_lt_of_le hm hj, hneg⟩
