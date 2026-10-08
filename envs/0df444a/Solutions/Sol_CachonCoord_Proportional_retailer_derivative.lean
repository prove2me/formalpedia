-- Prove2me | solution 1 for CachonCoord.Proportional.retailer_derivative
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:51:37.001992+00:00
-- url     : https://prove2.me/submissions/d68e21ea-43e7-49c7-a8a4-93eb6cbf8f18

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

open CachonCoord.Proportional MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
set_option maxHeartbeats 1000000

private lemma leftover_integrable (M : Model) (q : ℝ) :
    Integrable (fun d => max (q - d) 0) M.law := by
  letI := M.isProb
  exact ((integrable_const q).sub M.integrable).pos_part

private lemma leftover_lip (d : ℝ) : LipschitzWith 1 (fun y : ℝ => max (y - d) 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simpa [Real.dist_eq, sub_sub_sub_cancel_right] using
    lipschitzWith_max.dist_le_mul (y - d, 0) (z - d, 0)

private lemma leftover_continuous (M : Model) : Continuous M.I := by
  letI := M.isProb
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have hh := norm_integral_le_of_norm_le_const (μ := M.law) (C := dist y z)
    (f := fun d => max (y - d) 0 - max (z - d) 0)
    (Filter.Eventually.of_forall fun d => by
      simpa [← dist_eq_norm] using (leftover_lip d).dist_le_mul y z)
  simpa [Model.I, integral_sub (leftover_integrable M y) (leftover_integrable M z),
    dist_eq_norm] using hh

private lemma no_atom (M : Model) (q : ℝ) (hq : 0 < q) : M.law {q} = 0 := by
  letI := M.isProb
  have hc := (M.hasDerivAt_cdf q hq).continuousAt
  have hl : Function.leftLim (cdf M.law) q = cdf M.law q :=
    hc.continuousWithinAt.leftLim_eq
  rw [← measure_cdf M.law, StieltjesFunction.measure_singleton, hl, sub_self, ENNReal.ofReal_zero]

private lemma leftover_deriv (M : Model) (q : ℝ) (hq : 0 < q) :
    HasDerivAt M.I (M.F q) q := by
  letI := M.isProb
  let D : ℝ → ℝ := (Iio q).indicator (fun _ => 1)
  have hD : AEStronglyMeasurable D M.law :=
    (measurable_const.indicator measurableSet_Iio).aestronglyMeasurable
  have hdiff : ∀ᵐ d ∂M.law, HasDerivAt (fun y => max (y - d) 0) (D d) q := by
    have hne : ∀ᵐ d ∂M.law, d ≠ q := by
      simpa only [ae_iff, not_not, Set.setOf_eq_eq_singleton] using no_atom M q hq
    filter_upwards [hne] with d hd
    rcases lt_or_gt_of_ne hd with h | h
    · have he : (fun y : ℝ => max (y - d) 0) =ᶠ[𝓝 q] (fun y => y - d) := by
        filter_upwards [eventually_gt_nhds h] with y hy
        exact max_eq_left (sub_nonneg.mpr hy.le)
      simpa [D, h] using ((hasDerivAt_id q).sub_const d).congr_of_eventuallyEq he
    · have he : (fun y : ℝ => max (y - d) 0) =ᶠ[𝓝 q] (fun _ => 0) := by
        filter_upwards [eventually_lt_nhds h] with y hy
        exact max_eq_right (sub_nonpos.mpr hy.le)
      simpa [D, not_lt.mpr h.le] using (hasDerivAt_const q (0 : ℝ)).congr_of_eventuallyEq he
  have hh := hasDerivAt_integral_of_dominated_loc_of_lip (μ := M.law)
    (F := fun y d => max (y - d) 0) (F' := D) (bound := fun _ => (1 : ℝ))
    (s := Set.univ) (x₀ := q) (by simp)
    (Filter.Eventually.of_forall fun y =>
      ((measurable_const.sub measurable_id).max measurable_const).aestronglyMeasurable)
    (leftover_integrable M q) hD
    (Filter.Eventually.of_forall fun d => by simpa using (leftover_lip d))
    (integrable_const 1) hdiff
  have hi : (∫ d, D d ∂M.law) = M.F q := by
    have hm : M.law (Iio q) = M.law (Iic q) := by
      have hdis : Disjoint (Iio q) ({q} : Set ℝ) := by
        apply Set.disjoint_left.mpr
        intro a ha hb
        exact (Set.mem_Iio.mp ha).ne (Set.mem_singleton_iff.mp hb)
      rw [← Iio_union_right, measure_union hdis (measurableSet_singleton q),
        no_atom M q hq, add_zero]
    simp [D, integral_indicator measurableSet_Iio, Model.F, cdf_eq_real, measureReal_def, hm]
  simpa only [hi] using! hh.2

private lemma leftover_zero (M : Model) : M.I 0 = 0 := by
  apply integral_eq_zero_of_ae
  have hn : ∀ᵐ d ∂M.law, 0 ≤ d := by
    rw [ae_iff]
    have he : {a : ℝ | ¬0 ≤ a} = Iio 0 := by
      ext a
      simp
    rw [he]
    exact M.nonneg
  filter_upwards [hn] with d hd
  exact max_eq_right (by linarith)

private lemma leftover_cdf_integral (M : Model) (q : ℝ) (hq : 0 < q) :
    M.I q = ∫ x in (0 : ℝ)..q, M.F x := by
  have hint : IntervalIntegrable M.F volume 0 q :=
    (monotone_cdf M.law).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hq
    (fun y hy => leftover_deriv M y hy.1) hint
    ((leftover_continuous M).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((leftover_continuous M).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa [leftover_zero M] using he.symm

private lemma retailer_formula (M : Model) (w b y s : ℝ) (hy : 0 < y) (hs : 0 ≤ s) :
    M.retailerProfit w b y s = (M.p - w) * y - (M.p - b) * (y / (y + s)) * M.I (y + s) := by
  letI := M.isProb
  have hq : 0 < y + s := by linarith
  have hk : 0 ≤ y / (y + s) := div_nonneg hy.le hq.le
  have he (d : ℝ) :
      M.p * min y (y / (y + s) * d) + b * max (y - y / (y + s) * d) 0 - w * y =
        (M.p - w) * y - ((M.p - b) * (y / (y + s))) * max (y + s - d) 0 := by
    have hmul : y - y / (y + s) * d = (y / (y + s)) * (y + s - d) := by
      field_simp
      <;> ring
    have hmax : max (y - y / (y + s) * d) 0 = (y / (y + s)) * max (y + s - d) 0 := by
      rw [hmul, mul_max_of_nonneg (y + s - d) 0 hk, mul_zero]
    have hmin : min y (y / (y + s) * d) = y - max (y - y / (y + s) * d) 0 := by
      rcases le_total y (y / (y + s) * d) with h | h
      · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]; ring
    rw [hmin, hmax]
    ring
  unfold Model.retailerProfit
  simp_rw [he]
  rw [integral_sub (integrable_const _) ((leftover_integrable M (y + s)).const_mul _),
    integral_const, integral_const_mul]
  simp [Model.I]

theorem solution (M : Model) (w b x s : ℝ) (hx : 0 < x) (hs : 0 ≤ s) :
    HasDerivAt (fun y => M.retailerProfit w b y s)
      ((M.p - w) - (M.p - b) *
        (x / (x + s) * M.F (x + s) + s / (x + s) * M.avgF (x + s))) x := by
  have hq : 0 < x + s := by linarith
  have hd := (hasDerivAt_id x).div ((hasDerivAt_id x).add_const s) hq.ne'
  have hI := (leftover_deriv M (x + s) hq).comp x ((hasDerivAt_id x).add_const s)
  have hh := (((hasDerivAt_id x).const_mul (M.p - w)).sub
    ((hd.const_mul (M.p - b)).mul hI))
  have he : (M.p - w) * 1 -
      ((M.p - b) * ((1 * (x + s) - x * (1 + 0)) / (x + s)^2) * M.I (x + s) +
        (M.p - b) * (x / (x + s)) * (M.F (x + s) * (1 + 0))) =
      (M.p - w) - (M.p - b) *
        (x / (x + s) * M.F (x + s) + s / (x + s) * M.avgF (x + s)) := by
    rw [leftover_cdf_integral M (x + s) hq]
    unfold Model.avgF
    field_simp
    <;> ring
  simp only [id_eq, Pi.div_apply, Function.comp_apply] at hh
  simp only [one_mul, mul_one, add_zero] at hh
  simp only [one_mul, mul_one, add_zero] at he
  rw [he] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact retailer_formula M w b y s hy hs

#print axioms solution
