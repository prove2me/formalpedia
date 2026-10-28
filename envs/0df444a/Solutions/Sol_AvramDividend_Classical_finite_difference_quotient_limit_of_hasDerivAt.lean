-- Prove2me | solution 1 for AvramDividend.Classical.finite_difference_quotient_limit_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:42:51.793332+00:00
-- url     : https://prove2.me/submissions/4292e317-0aa8-4d4d-afc5-28f0b9e1e831

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

theorem solution
    (W : ℝ → ℝ) (a : ℝ)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a - ε) / (W a - W (a - ε)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) ∧
    Filter.Tendsto (fun ε : ℝ => ε * W (a + ε) / (W (a + ε) - W a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by
  constructor
  -- Lower quotient: use left slope (t -> 0-) composed with eps |-> -eps.
  have hSlopeL := hD.tendsto_slope_zero_left
  have hMapNeg : Filter.Tendsto (fun ε : ℝ => -ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin (0 : ℝ) (Set.Iio 0)) := by
    have hCont : ContinuousAt (fun ε : ℝ => -ε) (0 : ℝ) :=
      continuousAt_id.neg
    have hEv : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), -ε ∈ Set.Iio (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa [Set.mem_Ioi, Set.mem_Iio, neg_lt_zero] using hε
    have hT : Filter.Tendsto (fun ε : ℝ => -ε)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-(0 : ℝ))) :=
      tendsto_nhdsWithin_of_tendsto_nhds hCont.tendsto
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hT hEv)
  have hCompSub : Filter.Tendsto (fun ε : ℝ => a - ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin a (Set.Iio a)) := by
    have hCont : ContinuousAt (fun ε : ℝ => a - ε) (0 : ℝ) :=
      continuousAt_const.sub continuousAt_id
    have hEv : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), a - ε ∈ Set.Iio a := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa [Set.mem_Ioi, Set.mem_Iio, sub_lt_self_iff] using hε
    have hT : Filter.Tendsto (fun ε : ℝ => a - ε)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (a - (0 : ℝ))) :=
      tendsto_nhdsWithin_of_tendsto_nhds hCont.tendsto
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hT hEv)
  have hBase : Filter.Tendsto (fun ε : ℝ => (-ε)⁻¹ • (W (a + (-ε)) - W a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv W a)) :=
    hSlopeL.comp hMapNeg
  have hDenom : Filter.Tendsto (fun ε : ℝ => (W a - W (a - ε)) / ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv W a)) := by
    have hEq : (fun ε : ℝ => (W a - W (a - ε)) / ε)
        = (fun ε : ℝ => (-ε)⁻¹ • (W (a + (-ε)) - W a)) := by
      funext ε
      simp only [sub_eq_add_neg, smul_eq_mul, div_eq_mul_inv, inv_neg]
      ring
    rw [hEq]; exact hBase
  have hNum : Filter.Tendsto (fun ε : ℝ => W (a - ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a)) :=
    hD.continuousAt.tendsto.comp (hCompSub.mono_right nhdsWithin_le_nhds)
  have hLim := hNum.div hDenom hd
  have hEqF : (fun ε : ℝ => W (a - ε) / ((W a - W (a - ε)) / ε))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun ε : ℝ => ε * W (a - ε) / (W a - W (a - ε))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε
    have hne : ε ≠ 0 := ne_of_gt hε
    field_simp
  exact hLim.congr' hEqF
  -- Upper quotient: right slope already has the exact shape.
  have hSlopeR := hD.tendsto_slope_zero_right
  have hCompAdd : Filter.Tendsto (fun ε : ℝ => a + ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin a (Set.Ioi a)) := by
    have hCont : ContinuousAt (fun ε : ℝ => a + ε) (0 : ℝ) :=
      continuousAt_const.add continuousAt_id
    have hEv : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), a + ε ∈ Set.Ioi a := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa [Set.mem_Ioi, lt_add_iff_pos_right] using hε
    have hT : Filter.Tendsto (fun ε : ℝ => a + ε)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (a + (0 : ℝ))) :=
      tendsto_nhdsWithin_of_tendsto_nhds hCont.tendsto
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hT hEv)
  have hDenomU : Filter.Tendsto (fun ε : ℝ => (W (a + ε) - W a) / ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv W a)) := by
    have hEq : (fun ε : ℝ => (W (a + ε) - W a) / ε)
        = (fun t : ℝ => t⁻¹ • (W (a + t) - W a)) := by
      funext ε
      simp only [smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hEq]; exact hSlopeR
  have hNumU : Filter.Tendsto (fun ε : ℝ => W (a + ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a)) :=
    hD.continuousAt.tendsto.comp (hCompAdd.mono_right nhdsWithin_le_nhds)
  have hLimU := hNumU.div hDenomU hd
  have hEqFU : (fun ε : ℝ => W (a + ε) / ((W (a + ε) - W a) / ε))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun ε : ℝ => ε * W (a + ε) / (W (a + ε) - W a)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε
    have hne : ε ≠ 0 := ne_of_gt hε
    field_simp
  exact hLimU.congr' hEqFU
