-- Prove2me | solution 1 for AvramDividend.Classical.ae_early_downward_jumps_of_infinite_negative_activity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T19:03:14.175495+00:00
-- url     : https://prove2.me/submissions/40158a4f-c7eb-46b9-b390-e1b559a5d220
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_levy_band_zero_count_laws
import Theorems.Thm_AvramDividend_Classical_poisson_band_zero_count_laws_of_infinite_activity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω)
            (nhdsWithin t (Iio t)) (nhds l) ∧
          X.X t ω < l := by
  have hTop : X.ν (Iio (0 : ℝ)) = ⊤ :=
    ENNReal.not_lt_top.mp hInfinite
  have hδpos : ∀ k : ℕ, 0 < ((k + 1 : ℕ) : ℝ≥0)⁻¹ := by
    intro k
    positivity
  have hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ k : ℕ, ((k + 1 : ℕ) : ℝ≥0)⁻¹ < ε := by
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt ((ε : ℝ))⁻¹
    refine ⟨m, ?_⟩
    have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
    have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hcast : ((((m + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = ((m : ℝ) + 1)⁻¹ := by
      push_cast
      ring_nf
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith [hmR]
    have hlt : ((ε : ℝ))⁻¹ < (m : ℝ) + 1 := lt_trans hm (by linarith [hmR])
    have hgoal : ((m : ℝ) + 1)⁻¹ < (ε : ℝ) := by
      conv_rhs => rw [← inv_inv (ε : ℝ)]
      exact (inv_lt_inv₀ hpos (inv_pos.mpr hεR)).mpr hlt
    have hback : ((((m + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) < (ε : ℝ) := by
      rw [hcast]
      exact hgoal
    exact_mod_cast hback
  obtain ⟨counts, hsubset, hzeroLaw⟩ :=
    AvramDividend.Classical.poisson_band_zero_count_laws_of_infinite_activity
      X hTop (fun k => ((k + 1 : ℕ) : ℝ≥0)⁻¹)
  exact AvramDividend.Classical.ae_early_downward_jumps_of_levy_band_zero_count_laws
    X hTop (fun k => ((k + 1 : ℕ) : ℝ≥0)⁻¹) hδpos hcofinal counts hsubset hzeroLaw
