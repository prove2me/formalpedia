-- Prove2me | solution 17 for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T19:50:55.489607+00:00
-- url     : https://prove2.me/submissions/be22dfb6-7eeb-4576-a1c6-cb3237ec3fad
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
import Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_infinite_negative_activity
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
import Theorems.Thm_AvramDividend_Classical_scale_derivZeroPlus_top_of_bv_infinite_negative_activity
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
  · have hDiv : dividendValue X q 0 (barrierStrategy X 0 0)
        = barrierSupValue X 0 q :=
      AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q 0
    have hSup : barrierSupValue X 0 q
        = ENNReal.ofReal (barrierValue W 0 0) := by
      by_cases hFinite : X.ν (Iio (0 : ℝ)) < ⊤
      · exact AvramDividend.Classical.zero_reflectedSupValue_bv_finite_activity
          X hX q hq W hW hbv hFinite
      · have hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤ := hFinite
        have hder : derivZeroPlus W = ⊤ :=
          AvramDividend.Classical.scale_derivZeroPlus_top_of_bv_infinite_negative_activity
            X hX q hq W hW hbv hInfinite
        have hJumps : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
            ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
              ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
                (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l :=
          AvramDividend.Classical.ae_early_downward_jumps_of_infinite_negative_activity
            X hInfinite
        exact AvramDividend.Classical.zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
          X q W hJumps hder
    exact hDiv.trans hSup
  · have hnbv : ¬ X.BoundedVariation := hbv
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
