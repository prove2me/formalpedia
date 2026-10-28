-- Prove2me | solution 11 for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:16:09.524806+00:00
-- url     : https://prove2.me/submissions/90876be7-982b-466b-a85e-15c658a63321
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
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_levy_poisson_count_laws
import Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_infinite_negative_activity
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
import Theorems.Thm_AvramDividend_Classical_scale_derivZeroPlus_top_of_bv_infinite_negative_activity
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top
import Theorems.Thm_AvramDividend_Classical_zero_probability_of_diverging_poisson_zero_count_bounds
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_derivZeroPlus_top
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

-- Derivation for c2921c8c (Open): zero-barrier boundary identity.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION.
-- Principal route (unbounded-variation branch): Proved fd11e610
-- (barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero)
-- concludes `0 ≤ barrierValue W 0 0 ∧ dividendValue ... = ofReal ...`
-- from Standing + hnbv + hNear; its second conjunct is exactly this target.
-- Equivalent Proved alternative: 6e269fcd
-- (barrier_strategy_value_zero_all_capital_of_unbounded_ae_negative_near_zero)
-- at x = 0 with hx : 0 ≤ 0 concludes the target directly from the same
-- Standing + hnbv + hNear hypotheses.
-- Case split: by_cases on X.BoundedVariation.
--   * ¬BV branch reduces to hRog, which is exactly the conclusion shape of
--     Open 4502f364 (ae_rogozin_negative_slopes_of_unbounded_variation)
--     from hnbv; hNear (the Open 703dc740 shape) is then derived via Proved
--     b2e617e8. Hence the ¬BV branch is blocked only on Open 4502f364.
--   * BV branch (2026-10-27 refinement): reduce dividendValue to barrierSupValue
--     via Proved 11b589b7 (barrierValue_self_eq_barrierSupValue X q 0), then
--     split on finite negative-jump activity. Finite case is Proved cd185c75
--     (zero_reflectedSupValue_bv_finite_activity); infinite case closes via
--     single Proved closer 3d156c7e
--     (zero_reflectedSupValue_of_levy_poisson_count_laws) from
--     (hTop hδpos hcofinal hsubset hzeroLaw hder), with hder from Proved
--     0893ca6f, plus Proved 25e87aea (hRates below) for the analytic
-- rate-divergence half. Only remaining gap is the Poisson-count construction hCount.
-- Step 2026-10-27: ¬BV hNear now derived via Proved b2e617e8 from the single
-- Open slope obligation 4502f364 (was: generic Open 703dc740 sorry).
-- Callee-binder audit 2026-10-27 (fresh show reads, all exact): 11b589b7
-- (X q a) called as (X q 0); cd185c75 (X hX q hq W hW hBV hFinite) called in
-- order; 0893ca6f (X hX q hq W hW hBV hInfinite) called in order; 25e87aea
-- (nu hnu_int hnu_inf t ht) called as (X.nu X.nu_integrable hTop t ht);
-- 3d156c7e (X q W delta counts hnu_inf hdelta_pos hcofinal hsubset hzeroLaw
-- hder) called in order with hsubset/hzeroLaw verbatim; b2e617e8 (X hSlope)
-- called as (X hRog) with hRog matching hSlope binder-for-binder; fd11e610
-- (X hX q hq W hW hnbv hNear) called in order. No binder-order defect.
-- 2026-10-28: hCount eliminated via the count-free (ff758fb4 + 9228cae3) route; file is sorry-free.
-- hRog closed 2026-10-28 as an Open reduction dependency (4502f364); the
-- ¬BV branch is now sorry-free (SKETCH-shaped, remote-decided).
-- SKETCH-shaped (Open 4502f364 + Open ff758fb4 reduction deps, remote-decided);
-- submittable: zero sorry placeholders.
-- Header-equivalence audit 2026-10-27: file binders match the authoritative
-- show statement binder-for-binder (implicits Omega/mOmega/P/F, explicits
-- X hX q hq W hW, identical conclusion); only differences are the
-- line-split F binder and the required `theorem solution` entry name.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  by_cases hbv : X.BoundedVariation
  · -- BV branch: Proved reduction + finite/infinite split (2026-10-27).
    -- Step 1 (Proved 11b589b7): dividendValue X q 0 (barrierStrategy X 0 0)
    --   = barrierSupValue X 0 q.
    -- Step 2: by_cases on finite negative-jump activity. Finite case closed by
    --   Proved cd185c75; infinite case closes below via Open ff758fb4 (hJumps
    --   from hInfinite, count-free) + Proved 9228cae3 (hJumps + hder).
    have hDiv : dividendValue X q 0 (barrierStrategy X 0 0)
        = barrierSupValue X 0 q :=
      AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q 0
    have hSup : barrierSupValue X 0 q
        = ENNReal.ofReal (barrierValue W 0 0) := by
      by_cases hFinite : X.ν (Iio (0 : ℝ)) < ⊤
      · exact AvramDividend.Classical.zero_reflectedSupValue_bv_finite_activity
          X hX q hq W hW hbv hFinite
      · -- Infinite-activity sub-branch (Open 625fac59 shape, refined 2026-10-27):
        -- Single Proved closer 3d156c7e takes
        -- (X q W δ counts hTop hδpos hcofinal hsubset hzeroLaw hder) directly,
        -- replacing the 85823b83+9228cae3 two-layer route and its ae-jumps
        -- middle layer. Proved 0893ca6f supplies hder; Proved 92237d25
        -- pins barrierValue W 0 0 = 0 (hBarrierZero). Remaining gap: hCount.
        -- NOTE: by_cases binds the negated hypothesis as hFinite here;
        -- alias it to hInfinite to match the callee binder names.
        have hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤ := hFinite
        have hder : derivZeroPlus W = ⊤ :=
          AvramDividend.Classical.scale_derivZeroPlus_top_of_bv_infinite_negative_activity
            X hX q hq W hW hbv hInfinite
        -- Count-free route 2026-10-28: Open ff758fb4 supplies the a.e. early
        -- downward-jump property directly from hInfinite (no Poisson-count
        -- construction needed); Proved 9228cae3 closes barrierSupValue from
        -- (hJumps, hder). Conclusion shapes verified binder-identical against
        -- live show reads this turn. Remote decides SKETCH vs ACCEPTED.
        have hJumps : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
            ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
              ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
                (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l :=
          AvramDividend.Classical.ae_early_downward_jumps_of_infinite_negative_activity
            X hInfinite
        exact AvramDividend.Classical.zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
          X q W hJumps hder
    exact hDiv.trans hSup
  · -- ¬BV branch: exact Proved package application modulo one Open slope fact.
    have hnbv : ¬ X.BoundedVariation := hbv
    -- hRog discharged 2026-10-28 as an explicit Open reduction dependency:
    -- Open 4502f364 (ae_rogozin_negative_slopes_of_unbounded_variation)
    -- applied to hnbv. Its conclusion is binder-identical to the hRog shape
    -- (verified against the live 4502f364 show this turn). Remote decides
    -- SKETCH vs ACCEPTED; no sorry remains in this branch.
    -- Proved b2e617e8 turns hRog into hNear for Proved fd11e610 below.
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
    -- Bridge cross-check (comment only, no new import): Proved 6e269fcd
    -- (barrier_strategy_value_zero_all_capital_of_unbounded_ae_negative_near_zero)
    -- at x = 0 with hx : 0 ≤ 0 concludes this same goal from the identical
    -- (Standing, hnbv, hNear) hypotheses; fd11e610.2 and 6e269fcd-at-0 agree.
    -- Verified 2026-10-27 against fresh show: 6e269fcd binders are
    -- (X hX q hq W hW hnbv hNear x hx) with conclusion
    -- dividendValue X q x (barrierStrategy X x 0) = ofReal (barrierValue W 0 x);
    -- at x := 0 this is syntactically this goal, and the commented call passes
    -- all 10 explicit args in order with (le_refl 0 : 0 <= 0) for hx.
    -- have hcross :=
    --   AvramDividend.Classical.barrier_strategy_value_zero_all_capital_of_unbounded_ae_negative_near_zero
    --     X hX q hq W hW hnbv hNear 0 (le_refl 0)
    -- exact hcross
    exact hpack.2
