-- Prove2me | solution 12 for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:07:48.588555+00:00
-- url     : https://prove2.me/submissions/733f7222-9dae-49a8-adcf-e5e3f92da671
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_negative_slopes_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_bv_finite_activity
import Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_levy_band_zero_count_laws
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
import Theorems.Thm_AvramDividend_Classical_poisson_band_zero_count_laws_of_infinite_activity
import Theorems.Thm_AvramDividend_Classical_scale_derivZeroPlus_top_of_bv_infinite_negative_activity
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top
import Theorems.Thm_AvramDividend_Classical_zero_probability_of_diverging_poisson_zero_count_bounds
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_derivZeroPlus_top
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  by_cases hbv : X.BoundedVariation
  · -- BV branch: Proved reduction + finite/infinite split (2026-10-27).
    have hDiv : dividendValue X q 0 (barrierStrategy X 0 0)
        = barrierSupValue X 0 q :=
      AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q 0
    have hSup : barrierSupValue X 0 q
        = ENNReal.ofReal (barrierValue W 0 0) := by
      by_cases hFinite : X.ν (Iio (0 : ℝ)) < ⊤
      · exact AvramDividend.Classical.zero_reflectedSupValue_bv_finite_activity
          X hX q hq W hW hbv hFinite
      · -- Infinite-activity sub-branch, proved-only (swap plan 28l, route B):
        have hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤ := hFinite
        have hder : derivZeroPlus W = ⊤ :=
          AvramDividend.Classical.scale_derivZeroPlus_top_of_bv_infinite_negative_activity
            X hX q hq W hW hbv hInfinite
        have hTop : X.ν (Iio (0 : ℝ)) = ⊤ :=
          ENNReal.not_lt_top.mp hInfinite
        set δ : ℕ → ℝ≥0 := fun k => ((k + 1 : ℕ) : ℝ≥0)⁻¹ with hδdef
        have hδpos : ∀ k : ℕ, 0 < δ k := by
          intro k
          rw [hδdef]
          positivity
        have hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ k : ℕ, δ k < ε := by
          intro ε hε
          obtain ⟨m, hm⟩ := exists_nat_gt ((ε : ℝ))⁻¹
          refine ⟨m, ?_⟩
          have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
          have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          have hcast : ((δ m : ℝ≥0) : ℝ) = (((m : ℝ) + 1))⁻¹ := by
            rw [hδdef]
            push_cast
            rfl
          have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith [hmR]
          have hlt : ((ε : ℝ))⁻¹ < (m : ℝ) + 1 := lt_trans hm (by linarith [hmR])
          have hgoal : (((m : ℝ) + 1))⁻¹ < (ε : ℝ) := by
            conv_rhs => rw [← inv_inv (ε : ℝ)]
            exact (inv_lt_inv₀ hpos (inv_pos.mpr hεR)).mpr hlt
          have hback : (δ m : ℝ) < (ε : ℝ) := by rw [hcast]; exact hgoal
          exact_mod_cast hback
        obtain ⟨counts, hsubset, hzeroLaw⟩ :=
          AvramDividend.Classical.poisson_band_zero_count_laws_of_infinite_activity
            X hTop δ
        have hJumps : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
            ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
              ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
                (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l :=
          AvramDividend.Classical.ae_early_downward_jumps_of_levy_band_zero_count_laws
            X hTop δ hδpos hcofinal counts hsubset hzeroLaw
        exact AvramDividend.Classical.zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
          X q W hJumps hder
    exact hDiv.trans hSup
  · -- ¬BV branch: exact Proved package application modulo one Open slope fact.
    have hnbv : ¬ X.BoundedVariation := hbv
    have hRog : ∀ᵐ ω ∂P, ∀ C : ℝ,
        ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
          X.X t ω < C * (t : ℝ) :=
      AvramDividend.Classical.ae_rogozin_negative_slopes_of_unbounded_variation
        X hnbv
    have hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 :=
      AvramDividend.Classical.ae_negative_near_zero_of_ae_rogozin_negative_slopes
        X hRog
    have hpack :=
      AvramDividend.Classical.barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
        X hX q hq W hW hnbv hNear
    exact hpack.2
