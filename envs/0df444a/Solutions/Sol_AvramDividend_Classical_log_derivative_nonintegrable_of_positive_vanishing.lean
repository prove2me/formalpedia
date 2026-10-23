-- Prove2me | solution 1 for AvramDividend.Classical.log_derivative_nonintegrable_of_positive_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:57:36.622995+00:00
-- url     : https://prove2.me/submissions/c8911f4a-bdef-4feb-802d-e6320d04dad5

import Mathlib.Analysis.SpecialFunctions.NonIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Asymptotics
open scoped Topology

theorem solution
    (V : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hdiff : ∀ x : ℝ, 0 < x → HasDerivAt V (deriv V x) x)
    (hzero : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    ¬ IntegrableOn (fun x : ℝ => deriv V x / V x) (Ioi (0 : ℝ)) := by
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hxpos : ∀ᶠ x : ℝ in l, 0 < x := by
    exact self_mem_nhdsWithin
  have hvpos : ∀ᶠ x : ℝ in l, V x ∈ Ioi (0 : ℝ) :=
    hxpos.mono (fun x hx => hpos x hx)
  have hzero_pos : Tendsto V l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hvpos⟩
  have hlog : Tendsto (fun x => Real.log (V x)) l atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hzero_pos
  have hnorm : Tendsto (fun x => ‖Real.log (V x)‖) l atTop := by
    simpa only [Real.norm_eq_abs, Function.comp_def] using
      Filter.tendsto_abs_atBot_atTop.comp hlog
  have hlog_deriv : ∀ᶠ x : ℝ in l,
      HasDerivAt (fun y => Real.log (V y)) (deriv V x / V x) x := by
    filter_upwards [hxpos] with x hx
    exact (hdiff x hx).log (ne_of_gt (hpos x hx))
  have hdiff_log : ∀ᶠ x : ℝ in l,
      DifferentiableAt ℝ (fun y => Real.log (V y)) x :=
    hlog_deriv.mono (fun x hx => hx.differentiableAt)
  have hbigO :
      (deriv (fun y => Real.log (V y))) =O[l]
        (fun x => deriv V x / V x) := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [hlog_deriv] with x hx
    simp only [hx.deriv, le_refl]
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
    l (show Ioi (0 : ℝ) ∈ l from self_mem_nhdsWithin)
    hdiff_log hnorm hbigO
