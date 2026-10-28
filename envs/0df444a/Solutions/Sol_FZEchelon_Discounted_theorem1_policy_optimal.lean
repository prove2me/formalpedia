-- Prove2me | solution 1 for FZEchelon.Discounted.theorem1_policy_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T08:08:50.072991+00:00
-- url     : https://prove2.me/submissions/d03272b7-2b17-42a4-95a0-99214b0a7a8e

import Mathlib
import Definitions.Def_FZEchelon_Discounted_Programs

open MeasureTheory Filter Topology

/- Inlined source: Generic convex integral helpers. -/

open MeasureTheory

namespace FZEchelon.AverageCost.Analysis

lemma convex_affine (a b : ℝ) : ConvexOn ℝ Set.univ (fun x : ℝ => a * x + b) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy c d hc hd hcd
  simp only [smul_eq_mul]
  have hb := congrArg (fun z : ℝ => z * b) hcd
  nlinarith

lemma convex_integral {ν : Measure ℝ} (f : ℝ → ℝ → ℝ)
    (hi : ∀ x, Integrable (f x) ν) (hc : ∀ t, ConvexOn ℝ Set.univ (fun x => f x t)) :
    ConvexOn ℝ Set.univ (fun x => ∫ t, f x t ∂ν) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have h := integral_mono (hi (a * x + b * y))
    (((hi x).const_mul a).add ((hi y).const_mul b))
    (fun t => (hc t).2 hx hy ha hb hab)
  simpa only [Pi.add_apply, integral_add ((hi x).const_mul a) ((hi y).const_mul b),
    integral_const_mul, smul_eq_mul] using h

lemma hinge_integrable {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable id ν) (x : ℝ) :
    Integrable (fun t => max (t - x) 0) ν ∧
      Integrable (fun t => max (x - t) 0) ν := by
  exact ⟨(hν.sub (integrable_const x)).sup (integrable_const 0),
    ((integrable_const x).sub hν).sup (integrable_const 0)⟩

lemma hinge_integral_convex {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable id ν) :
    ConvexOn ℝ Set.univ (fun x => ∫ t, max (t - x) 0 ∂ν) ∧
      ConvexOn ℝ Set.univ (fun x => ∫ t, max (x - t) 0 ∂ν) := by
  constructor
  · apply convex_integral _ (fun x => (hinge_integrable hν x).1)
    intro t
    have heq : (fun x : ℝ => max (t - x) 0) =
        (fun x => (-1 : ℝ) * x + t) ⊔ (fun _ => 0) := by
      funext x
      change max (t - x) 0 = max (-1 * x + t) 0
      congr 1
      ring
    rw [heq]
    exact (convex_affine (-1) t).sup (convexOn_const 0 convex_univ)
  · apply convex_integral _ (fun x => (hinge_integrable hν x).2)
    intro t
    have heq : (fun x : ℝ => max (x - t) 0) =
        (fun x => (1 : ℝ) * x + (-t)) ⊔ (fun _ => 0) := by
      funext x
      change max (x - t) 0 = max (1 * x + (-t)) 0
      congr 1
      ring
    rw [heq]
    exact (convex_affine 1 (-t)).sup (convexOn_const 0 convex_univ)

lemma hinge_integral_lipschitz {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Integrable id ν) (x y : ℝ) :
    |(∫ t, max (t - x) 0 ∂ν) - ∫ t, max (t - y) 0 ∂ν| ≤ |x - y| ∧
      |(∫ t, max (x - t) 0 ∂ν) - ∫ t, max (y - t) 0 ∂ν| ≤ |x - y| := by
  constructor
  · rw [← integral_sub (hinge_integrable hν x).1 (hinge_integrable hν y).1]
    have h := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun t => max (t - x) 0 - max (t - y) 0)
      (C := |x - y|) (Filter.Eventually.of_forall (fun t => by
        simpa only [Real.norm_eq_abs, sub_sub_sub_cancel_left, abs_sub_comm] using
          abs_max_sub_max_le_abs (t - x) (t - y) 0))
    simpa using h
  · rw [← integral_sub (hinge_integrable hν x).2 (hinge_integrable hν y).2]
    have h := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun t => max (x - t) 0 - max (y - t) 0)
      (C := |x - y|) (Filter.Eventually.of_forall (fun t => by
        simpa only [Real.norm_eq_abs, sub_sub_sub_cancel_right] using
          abs_max_sub_max_le_abs (x - t) (y - t) 0))
    simpa using h

end FZEchelon.AverageCost.Analysis

/- Inlined source: ConvexGap. -/

namespace FZEchelon.Discounted

noncomputable def convexGapPenalty (F : ℝ → ℝ) (xstar w : ℝ) : ℝ :=
  if xstar ≤ w then 0 else F w - F xstar

noncomputable def convexGapExcess (F : ℝ → ℝ) (xstar x : ℝ) : ℝ :=
  if xstar ≤ x then F x - F xstar else 0

lemma convexGap_lower (F : ℝ → ℝ) (xstar x u w : ℝ)
    (hF : ConvexOn ℝ Set.univ F) (hmin : ∀ z, F xstar ≤ F z)
    (hxu : x ≤ u) (huw : u ≤ w) :
    convexGapExcess F xstar x ≤ F u - F xstar - convexGapPenalty F xstar w := by
  unfold convexGapExcess convexGapPenalty
  by_cases hx : xstar ≤ x
  · have hw : xstar ≤ w := hx.trans (hxu.trans huw)
    simp only [if_pos hx, if_pos hw, sub_zero]
    have h := hF.le_max_of_mem_Icc (show xstar ∈ Set.univ from trivial)
      (show u ∈ Set.univ from trivial) (show x ∈ Set.Icc xstar u from ⟨hx, hxu⟩)
    rw [max_eq_right (hmin u)] at h
    linarith
  · simp only [if_neg hx]
    by_cases hw : xstar ≤ w
    · simp only [if_pos hw, sub_zero]
      linarith [hmin u]
    · simp only [if_neg hw]
      have hws : w ≤ xstar := le_of_not_ge hw
      have h := hF.le_max_of_mem_Icc (show u ∈ Set.univ from trivial)
        (show xstar ∈ Set.univ from trivial) (show w ∈ Set.Icc u xstar from ⟨huw, hws⟩)
      rw [max_eq_left (hmin u)] at h
      linarith

lemma convexGap_candidate (F : ℝ → ℝ) (xstar x w : ℝ) (hxw : x ≤ w) :
    F (x + max 0 (min xstar w - x)) - F xstar - convexGapPenalty F xstar w =
      convexGapExcess F xstar x := by
  unfold convexGapPenalty convexGapExcess
  by_cases hx : xstar ≤ x
  · have hw : xstar ≤ w := hx.trans hxw
    have hm : min xstar w - x ≤ 0 := by linarith [min_le_left xstar w]
    simp only [if_pos hx, if_pos hw, max_eq_left hm, add_zero, sub_zero]
  · have hm : 0 ≤ min xstar w - x := by
      have hxs : x ≤ xstar := le_of_not_ge hx
      exact sub_nonneg.mpr (le_min hxs hxw)
    rw [max_eq_right hm]
    have heq : x + (min xstar w - x) = min xstar w := by ring
    rw [heq]
    simp only [if_neg hx]
    by_cases hw : xstar ≤ w
    · simp [hw, min_eq_left hw]
    · have hw' : w ≤ xstar := le_of_not_ge hw
      simp [hw, min_eq_right hw']


lemma convexGapExcess_nonneg (F : ℝ → ℝ) (xstar x : ℝ)
    (hmin : ∀ z, F xstar ≤ F z) : 0 ≤ convexGapExcess F xstar x := by
  unfold convexGapExcess
  split_ifs
  · exact sub_nonneg.mpr (hmin x)
  · exact le_rfl

lemma convexGapExcess_monotone (F : ℝ → ℝ) (xstar : ℝ)
    (hF : ConvexOn ℝ Set.univ F) (hmin : ∀ z, F xstar ≤ F z) :
    Monotone (convexGapExcess F xstar) := by
  intro x y hxy
  by_cases hx : xstar ≤ x
  · have hy : xstar ≤ y := hx.trans hxy
    have h := hF.le_max_of_mem_Icc (show xstar ∈ Set.univ from trivial)
      (show y ∈ Set.univ from trivial) (show x ∈ Set.Icc xstar y from ⟨hx, hxy⟩)
    rw [max_eq_right (hmin y)] at h
    simp only [convexGapExcess, if_pos hx, if_pos hy]
    linarith
  · simp only [convexGapExcess, if_neg hx]
    exact convexGapExcess_nonneg F xstar y hmin

end FZEchelon.Discounted

/- Inlined source: Analytic. -/

open MeasureTheory
open FZEchelon.AverageCost.Analysis

namespace FZEchelon.Discounted

variable (M : Model)

lemma demandLaw_probability (n : ℕ) : IsProbabilityMeasure (M.demandLaw n) := by
  apply Measure.isProbabilityMeasure_map
  exact (show Measurable (fun t : Fin n → ℝ => ∑ j, t j) from by fun_prop).aemeasurable

lemma demandLaw_integrable (hν : Integrable id M.ν) (n : ℕ) :
    Integrable id (M.demandLaw n) := by
  have hm : Measurable (fun t : Fin n → ℝ => ∑ j, t j) := by fun_prop
  apply (integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).2
  exact integrable_finsetSum Finset.univ (fun j _ =>
    integrable_eval (i := j) (μ := fun _ : Fin n => M.ν) hν)

lemma outletCost_convex (hα : 0 ≤ M.α) (hpr : 0 ≤ M.pr) (hhold : 0 ≤ M.hd + M.hr)
    (hν : Integrable id M.ν) : ConvexOn ℝ Set.univ M.R := by
  letI := demandLaw_probability M (M.l + 1)
  have h := hinge_integral_convex (demandLaw_integrable M hν (M.l + 1))
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hm := h.1.2 hx hy ha hb hab
  have hp := h.2.2 hx hy ha hb hab
  have hl := (convex_affine (-M.hd) (M.hd * (M.l : ℝ) * M.mu)).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hm hp hl
  have ht := add_le_add (add_le_add hl (mul_le_mul_of_nonneg_left hm hpr))
    (mul_le_mul_of_nonneg_left hp hhold)
  have ht' := mul_le_mul_of_nonneg_left ht (pow_nonneg hα M.l)
  convert ht' using 1 <;> simp only [Model.R, smul_eq_mul] <;> ring

noncomputable def stationaryObjective (x : ℝ) : ℝ := (1 - M.α) * M.cr * x + M.R x

lemma stationaryObjective_convex (hM : M.StandingAssumptions) :
    ConvexOn ℝ Set.univ (stationaryObjective M) := by
  have hR := outletCost_convex M hM.α_nonneg hM.pr_pos.le
    (add_nonneg hM.hd_pos.le hM.hr_pos.le) hM.demand_integrable
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hr := hR.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hr
  convert add_le_add (le_refl ((1 - M.α) * M.cr * (a * x + b * y))) hr using 1 <;>
    simp only [stationaryObjective, smul_eq_mul] <;> ring

lemma stationaryObjective_min (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar) :
    ∀ x, stationaryObjective M xstar ≤ stationaryObjective M x := hx

lemma penalty_gap (xstar w : ℝ) :
    convexGapPenalty (stationaryObjective M) xstar w = M.P xstar w := by
  unfold convexGapPenalty stationaryObjective Model.P
  split_ifs <;> ring

lemma feasible_stage_gap (hM : M.StandingAssumptions) (xstar : ℝ)
    (hx : M.IsStationaryCriticalNumber xstar) (x u w : ℝ) (hxu : x ≤ u) (huw : u ≤ w) :
    convexGapExcess (stationaryObjective M) xstar x ≤
      stationaryObjective M u - stationaryObjective M xstar - M.P xstar w := by
  rw [← penalty_gap M xstar w]
  exact convexGap_lower _ _ _ _ _ (stationaryObjective_convex M hM)
    (stationaryObjective_min M xstar hx) hxu huw

lemma candidate_stage_gap (xstar x w : ℝ) (hxw : x ≤ w) :
    stationaryObjective M (x + max 0 (min xstar w - x)) - stationaryObjective M xstar -
      M.P xstar w = convexGapExcess (stationaryObjective M) xstar x := by
  rw [← penalty_gap M xstar w]
  exact convexGap_candidate _ _ _ _ hxw


/-- Exact one-period accounting, before taking expectations or infinite sums. -/
lemma one_step_decomposition (xstar : ℝ) (s : M.State) (a : ℝ × ℝ) :
    M.system.cost s a =
      (M.depotSystem xstar).cost (s.1, s.2.1) a.1 + stationaryObjective M xstar +
        M.cr * (M.α * (s.2.2 + a.2) - s.2.2) +
        (stationaryObjective M (s.2.2 + a.2) - stationaryObjective M xstar -
          M.P xstar (s.2.1 + M.arrival s.1 a.1)) := by
  simp only [Model.system, Model.depotSystem, stationaryObjective]
  ring

lemma feasible_one_step_lower (hM : M.StandingAssumptions) (xstar : ℝ)
    (hx : M.IsStationaryCriticalNumber xstar) (s : M.State) (a : ℝ × ℝ)
    (ha : M.system.feasible s a) :
    (M.depotSystem xstar).cost (s.1, s.2.1) a.1 + stationaryObjective M xstar +
      M.cr * (M.α * (s.2.2 + a.2) - s.2.2) +
      convexGapExcess (stationaryObjective M) xstar s.2.2 ≤ M.system.cost s a := by
  have h := feasible_stage_gap M hM xstar hx s.2.2 (s.2.2 + a.2)
    (s.2.1 + M.arrival s.1 a.1) (by linarith [ha.2.1]) ha.2.2
  rw [one_step_decomposition M xstar s a]
  linarith

lemma candidate_one_step_eq (σ : M.DepotState → ℝ) (xstar : ℝ) (s : M.State)
    (hs : M.InDomain s) (hσ : ∀ p, 0 ≤ σ p) :
    M.system.cost s (M.piStar σ xstar s) =
      (M.depotSystem xstar).cost (s.1, s.2.1) (σ (s.1, s.2.1)) +
        stationaryObjective M xstar +
        M.cr * (M.α * (s.2.2 + (M.piStar σ xstar s).2) - s.2.2) +
        convexGapExcess (stationaryObjective M) xstar s.2.2 := by
  have ha : 0 ≤ M.arrival s.1 (σ (s.1, s.2.1)) := by
    unfold Model.arrival
    split
    · exact hs.1 _
    · exact hσ _
  have hxw : s.2.2 ≤ s.2.1 + M.arrival s.1 (σ (s.1, s.2.1)) := by linarith [hs.2]
  have h := candidate_stage_gap M xstar s.2.2 (s.2.1 + M.arrival s.1 (σ (s.1, s.2.1))) hxw
  rw [one_step_decomposition M xstar s (M.piStar σ xstar s)]
  change _ = _
  simp only [Model.piStar] at h ⊢
  linarith

end FZEchelon.Discounted

/- Inlined source: CostBounds. -/

open MeasureTheory
open FZEchelon.AverageCost.Analysis

namespace FZEchelon.Discounted.CostBounds

variable (M : Model)

lemma demandLaw_probability (n : ℕ) : IsProbabilityMeasure (M.demandLaw n) := by
  apply Measure.isProbabilityMeasure_map
  exact (show Measurable (fun t : Fin n → ℝ => ∑ j, t j) from by fun_prop).aemeasurable

lemma demandLaw_integrable (hν : Integrable id M.ν) (n : ℕ) :
    Integrable id (M.demandLaw n) := by
  have hm : Measurable (fun t : Fin n → ℝ => ∑ j, t j) := by fun_prop
  apply (integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).2
  exact integrable_finsetSum Finset.univ (fun j _ =>
    integrable_eval (i := j) (μ := fun _ : Fin n => M.ν) hν)

lemma demandLaw_nonneg (hν0 : M.ν (Set.Iio 0) = 0) (n : ℕ) :
    ∀ᵐ t ∂M.demandLaw n, 0 ≤ t := by
  have hν : ∀ᵐ t ∂M.ν, 0 ≤ t := by simpa only [ae_iff, not_le, Set.Iio] using hν0
  have hcoords : ∀ᵐ t ∂Measure.pi (fun _ : Fin n => M.ν), ∀ j, 0 ≤ t j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval (fun _ : Fin n => M.ν) j).quasiMeasurePreserving.tendsto_ae hν
  apply (ae_map_iff (show AEMeasurable (fun t : Fin n → ℝ => ∑ j, t j)
    (Measure.pi (fun _ : Fin n => M.ν)) from (by fun_prop)) measurableSet_Ici).2
  filter_upwards [hcoords] with t ht
  exact Finset.sum_nonneg (fun j _ => ht j)

lemma mean_nonneg (hν0 : M.ν (Set.Iio 0) = 0) : 0 ≤ M.mu := by
  apply integral_nonneg_of_ae
  have hν : ∀ᵐ t ∂M.ν, 0 ≤ t := by simpa only [ae_iff, not_le, Set.Iio] using hν0
  exact hν

lemma R_abs_sub_le (hM : M.StandingAssumptions) (x y : ℝ) :
    |M.R x - M.R y| ≤
      M.α ^ M.l * (M.hd + M.pr + (M.hd + M.hr)) * |x - y| := by
  letI := demandLaw_probability M (M.l + 1)
  have h := hinge_integral_lipschitz (demandLaw_integrable M hM.demand_integrable (M.l + 1)) x y
  let A := (∫ t, max (t - x) 0 ∂M.demandLaw (M.l + 1)) -
    ∫ t, max (t - y) 0 ∂M.demandLaw (M.l + 1)
  let B := (∫ t, max (x - t) 0 ∂M.demandLaw (M.l + 1)) -
    ∫ t, max (y - t) 0 ∂M.demandLaw (M.l + 1)
  have hβ : 0 ≤ M.α ^ M.l := pow_nonneg hM.α_nonneg _
  have hh : 0 ≤ M.hd + M.hr := add_nonneg hM.hd_pos.le hM.hr_pos.le
  have heq : M.R x - M.R y = M.α ^ M.l *
      (-M.hd * (x - y) + M.pr * A + (M.hd + M.hr) * B) := by
    simp only [Model.R, A, B]
    ring
  have hcore : |(-M.hd * (x - y) + M.pr * A) + (M.hd + M.hr) * B| ≤
      (M.hd + M.pr + (M.hd + M.hr)) * |x - y| := by
    calc
      |(-M.hd * (x - y) + M.pr * A) + (M.hd + M.hr) * B| ≤
          |-M.hd * (x - y)| + |M.pr * A| + |(M.hd + M.hr) * B| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = M.hd * |x - y| + M.pr * |A| + (M.hd + M.hr) * |B| := by
        rw [abs_mul, abs_neg, abs_of_nonneg hM.hd_pos.le, abs_mul,
          abs_of_nonneg hM.pr_pos.le, abs_mul, abs_of_nonneg hh]
      _ ≤ M.hd * |x - y| + M.pr * |x - y| + (M.hd + M.hr) * |x - y| :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left h.1 hM.pr_pos.le))
          (mul_le_mul_of_nonneg_left h.2 hh)
      _ = (M.hd + M.pr + (M.hd + M.hr)) * |x - y| := by ring
  rw [heq, abs_mul, abs_of_nonneg hβ]
  calc
    _ ≤ M.α ^ M.l * ((M.hd + M.pr + (M.hd + M.hr)) * |x - y|) :=
      mul_le_mul_of_nonneg_left hcore hβ
    _ = _ := by ring

lemma R_continuous (hM : M.StandingAssumptions) : Continuous M.R := by
  have hC : 0 ≤ M.α ^ M.l * (M.hd + M.pr + (M.hd + M.hr)) :=
    mul_nonneg (pow_nonneg hM.α_nonneg _)
      (add_nonneg (add_nonneg hM.hd_pos.le hM.pr_pos.le)
        (add_nonneg hM.hd_pos.le hM.hr_pos.le))
  have h : LipschitzWith ⟨M.α ^ M.l * (M.hd + M.pr + (M.hd + M.hr)), hC⟩ M.R := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |M.R x - M.R y| ≤
      M.α ^ M.l * (M.hd + M.pr + (M.hd + M.hr)) * |x - y|
    exact R_abs_sub_le M hM x y
  exact h.continuous

lemma core_nonneg (hM : M.StandingAssumptions)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (w u : ℝ) (huw : u ≤ w) : 0 ≤ M.D w + M.R u := by
  letI := demandLaw_probability M (M.l + 1)
  have hi := demandLaw_integrable M hM.demand_integrable (M.l + 1)
  have hn := demandLaw_nonneg M hM.demand_nonneg (M.l + 1)
  have hβ0 : 0 ≤ M.α ^ M.l := pow_nonneg hM.α_nonneg _
  have hβ1 : M.α ^ M.l ≤ 1 := pow_le_one₀ hM.α_nonneg hM.α_le_one
  have hμ := mean_nonneg M hM.demand_nonneg
  have hH : 0 ≤ ∫ t, max (t - u) 0 ∂M.demandLaw (M.l + 1) :=
    integral_nonneg (fun _ => le_max_right _ _)
  have hJ : 0 ≤ ∫ t, max (u - t) 0 ∂M.demandLaw (M.l + 1) :=
    integral_nonneg (fun _ => le_max_right _ _)
  have hh : 0 ≤ M.hd + M.hr := add_nonneg hM.hd_pos.le hM.hr_pos.le
  have hmu : 0 ≤ M.α ^ M.l * M.hd * (M.l : ℝ) * M.mu :=
    mul_nonneg (mul_nonneg (mul_nonneg hβ0 hM.hd_pos.le) (Nat.cast_nonneg _)) hμ
  have hhold : 0 ≤ M.α ^ M.l * (M.hd + M.hr) *
      (∫ t, max (u - t) 0 ∂M.demandLaw (M.l + 1)) :=
    mul_nonneg (mul_nonneg hβ0 hh) hJ
  by_cases hu : 0 ≤ u
  · have hwu : 0 ≤ M.hd * (w - M.α ^ M.l * u) := by
      apply mul_nonneg hM.hd_pos.le
      nlinarith [mul_nonneg (sub_nonneg.mpr hβ1) hu]
    have hp : 0 ≤ M.α ^ M.l * M.pr *
        (∫ t, max (t - u) 0 ∂M.demandLaw (M.l + 1)) :=
      mul_nonneg (mul_nonneg hβ0 hM.pr_pos.le) hH
    simp only [Model.D, Model.R]
    nlinarith
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have hshort : -u ≤ ∫ t, max (t - u) 0 ∂M.demandLaw (M.l + 1) := by
      calc
        -u = ∫ _t, -u ∂M.demandLaw (M.l + 1) := by simp
        _ ≤ _ := by
          apply integral_mono_ae (integrable_const _) (hinge_integrable hi u).1
          filter_upwards [hn] with t ht
          exact le_trans (by linarith) (le_max_left _ _)
    have h1 : 0 ≤ M.hd * (w-u) := mul_nonneg hM.hd_pos.le (sub_nonneg.mpr huw)
    have h2 : 0 ≤ ((1 - M.α ^ M.l) * M.hd - M.α ^ M.l * M.pr) * u :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hcost) hu'
    have hsum : 0 ≤ (∫ t, max (t-u) 0 ∂M.demandLaw (M.l + 1)) + u := by linarith
    have h3 : 0 ≤ M.α ^ M.l * M.pr *
        ((∫ t, max (t-u) 0 ∂M.demandLaw (M.l + 1)) + u) :=
      mul_nonneg (mul_nonneg hβ0 hM.pr_pos.le) hsum
    simp only [Model.D, Model.R]
    nlinarith

lemma system_stage_lower (hM : M.StandingAssumptions)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (s : M.State) (a : ℝ × ℝ) (ha : M.system.feasible s a) :
    M.orderCost a.1 + M.cr * a.2 ≤ M.system.cost s a := by
  have h := core_nonneg M hM hcost _ _ ha.2.2
  simp only [Model.system]
  linarith


lemma orderCost_nonneg (hM : M.StandingAssumptions) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ M.orderCost y := by
  unfold Model.orderCost
  split_ifs
  · exact le_rfl
  · exact add_nonneg hM.K_pos.le (mul_nonneg hM.cd_pos.le hy)

lemma system_stage_nonneg (hM : M.StandingAssumptions)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (s : M.State) (a : ℝ × ℝ) (ha : M.system.feasible s a) :
    0 ≤ M.system.cost s a := by
  have h := system_stage_lower M hM hcost s a ha
  have ho := orderCost_nonneg M hM ha.1
  have hz : 0 ≤ M.cr * a.2 := mul_nonneg hM.cr_pos.le ha.2.1
  linarith

end FZEchelon.Discounted.CostBounds

/- Inlined source: PolicyHelpers. -/

open MeasureTheory

namespace FZEchelon.Discounted

variable (M : Model)

lemma arrival_nonneg (p : M.DepotState) (y : ℝ) (hp : ∀ k, 0 ≤ p.1 k)
    (hy : 0 ≤ y) : 0 ≤ M.arrival p.1 y := by
  unfold Model.arrival
  split
  · exact hp _
  · exact hy

lemma shift_nonneg (p : Fin M.L → ℝ) (y : ℝ) (hp : ∀ k, 0 ≤ p k)
    (hy : 0 ≤ y) : ∀ k, 0 ≤ M.shift p y k := by
  intro k
  unfold Model.shift
  split
  · exact hy
  · exact hp _

lemma piStar_feasible (σ : M.DepotState → ℝ) (xstar : ℝ)
    (hσ : ∀ p, 0 ≤ σ p) (s : M.State) (hs : M.InDomain s) :
    M.system.feasible s (M.piStar σ xstar s) := by
  have ha := arrival_nonneg M (s.1, s.2.1) (σ (s.1, s.2.1)) hs.1 (hσ _)
  change 0 ≤ σ (s.1, s.2.1) ∧
    0 ≤ max 0 (min xstar (s.2.1 + M.arrival s.1 (σ (s.1, s.2.1))) - s.2.2) ∧
    s.2.2 + max 0 (min xstar (s.2.1 + M.arrival s.1 (σ (s.1, s.2.1))) - s.2.2) ≤
      s.2.1 + M.arrival s.1 (σ (s.1, s.2.1))
  refine ⟨hσ _, le_max_left _ _, ?_⟩
  rw [add_max]
  apply max_le
  · linarith [hs.2]
  · linarith [min_le_right xstar (s.2.1 + M.arrival s.1 (σ (s.1, s.2.1)))]

lemma domain_next (s : M.State) (a : ℝ × ℝ) (u : ℝ) (hs : M.InDomain s)
    (ha : M.system.feasible s a) : M.InDomain (M.system.next s a u) := by
  change (∀ k, 0 ≤ M.shift s.1 a.1 k) ∧
    s.2.2 + a.2 - u ≤ s.2.1 + M.arrival s.1 a.1 - u
  exact ⟨shift_nonneg M s.1 a.1 hs.1 ha.1, sub_le_sub_right ha.2.2 u⟩

lemma arrival_measurable : Measurable (fun p : M.DepotState => M.arrival p.1 p.2) := by
  unfold Model.arrival
  split
  · exact (measurable_pi_apply _).comp measurable_fst
  · exact measurable_snd

lemma shift_measurable : Measurable (fun p : M.DepotState => M.shift p.1 p.2) := by
  apply measurable_pi_lambda
  intro k
  unfold Model.shift
  split
  · exact measurable_snd
  · exact (measurable_pi_apply _).comp measurable_fst

lemma piStar_measurable (σ : M.DepotState → ℝ) (xstar : ℝ) (hσ : Measurable σ) :
    Measurable (M.piStar σ xstar) := by
  have hp : Measurable (fun s : M.State => (s.1, s.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hy : Measurable (fun s : M.State => σ (s.1, s.2.1)) := hσ.comp hp
  have ha : Measurable (fun s : M.State => M.arrival s.1 (σ (s.1, s.2.1))) :=
    (arrival_measurable M).comp (measurable_fst.prodMk hy)
  change Measurable (fun s : M.State =>
    (σ (s.1, s.2.1), max 0 (min xstar (s.2.1 + M.arrival s.1 (σ (s.1, s.2.1))) - s.2.2)))
  exact hy.prodMk (measurable_const.max ((measurable_const.min (measurable_snd.fst.add ha)).sub measurable_snd.snd))

lemma system_next_measurable : Measurable (fun q : M.State × (ℝ × ℝ) × ℝ =>
    M.system.next q.1 q.2.1 q.2.2) := by
  have hshift : Measurable (fun q : M.State × (ℝ × ℝ) × ℝ => M.shift q.1.1 q.2.1.1) :=
    (shift_measurable M).comp (measurable_fst.fst.prodMk measurable_snd.fst.fst)
  have harrival : Measurable (fun q : M.State × (ℝ × ℝ) × ℝ => M.arrival q.1.1 q.2.1.1) :=
    (arrival_measurable M).comp (measurable_fst.fst.prodMk measurable_snd.fst.fst)
  change Measurable (fun q : M.State × (ℝ × ℝ) × ℝ =>
    (M.shift q.1.1 q.2.1.1, q.1.2.1 + M.arrival q.1.1 q.2.1.1 - q.2.2,
      q.1.2.2 + q.2.1.2 - q.2.2))
  exact hshift.prodMk (((measurable_fst.snd.fst.add harrival).sub measurable_snd.snd).prodMk
    ((measurable_fst.snd.snd.add measurable_snd.fst.snd).sub measurable_snd.snd))

lemma statTraj_measurable (σ : M.State → ℝ × ℝ) (hσ : Measurable σ)
    (s : M.State) (n : ℕ) : Measurable (fun ω => M.system.statTraj σ s ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun ω => M.system.next (M.system.statTraj σ s ω n)
      (σ (M.system.statTraj σ s ω n)) (ω n))
    exact (system_next_measurable M).comp
      (ih.prodMk ((hσ.comp ih).prodMk (measurable_pi_apply n)))

lemma statTraj_prefix (σ : M.State → ℝ × ℝ) (s : M.State) (ω ω' : ℕ → ℝ)
    (n : ℕ) (h : ∀ j < n, ω j = ω' j) :
    M.system.statTraj σ s ω n = M.system.statTraj σ s ω' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ControlSystem.statTraj]
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

lemma piStar_admissible (σ : M.DepotState → ℝ) (xstar : ℝ)
    (hσm : Measurable σ) (hσ : ∀ p, 0 ≤ σ p) (s : M.State) (hs : M.InDomain s) :
    M.system.Admissible (M.system.stationary (M.piStar σ xstar) s) s := by
  have hpol := piStar_measurable M σ xstar hσm
  constructor
  · intro k
    exact hpol.comp (statTraj_measurable M _ hpol s k)
  constructor
  · intro k ω ω' h
    change M.piStar σ xstar (M.system.statTraj (M.piStar σ xstar) s ω k) =
      M.piStar σ xstar (M.system.statTraj (M.piStar σ xstar) s ω' k)
    rw [statTraj_prefix M _ s ω ω' k h]
  · intro ω k
    have heq : ∀ n, M.system.traj (M.system.stationary (M.piStar σ xstar) s) s ω n =
        M.system.statTraj (M.piStar σ xstar) s ω n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        simp only [ControlSystem.traj, ControlSystem.statTraj, ControlSystem.stationary, ih]
    have hd : ∀ n, M.InDomain (M.system.statTraj (M.piStar σ xstar) s ω n) := by
      intro n
      induction n with
      | zero => exact hs
      | succ n ih =>
        exact domain_next M _ _ _ ih (piStar_feasible M σ xstar hσ _ ih)
    rw [heq k]
    exact piStar_feasible M σ xstar hσ _ (hd k)

end FZEchelon.Discounted

/- Inlined source: Pathwise. -/

open MeasureTheory

namespace FZEchelon.Discounted

variable (M : Model)

/-- Keep only the order component of a history-dependent system policy. -/
def projectOrders (π : Policy (ℝ × ℝ)) : Policy ℝ := fun n ω => (π n ω).1

lemma projectOrders_traj (xstar : ℝ) (π : Policy (ℝ × ℝ)) (s : M.State)
    (ω : ℕ → ℝ) (n : ℕ) :
    (M.depotSystem xstar).traj (projectOrders π) (s.1, s.2.1) ω n =
      ((M.system.traj π s ω n).1, (M.system.traj π s ω n).2.1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ControlSystem.traj]
    rw [ih]
    rfl

lemma projectOrders_admissible (xstar : ℝ) (π : Policy (ℝ × ℝ)) (s : M.State)
    (hπ : M.system.Admissible π s) :
    (M.depotSystem xstar).Admissible (projectOrders π) (s.1, s.2.1) := by
  refine ⟨fun n => (hπ.1 n).fst, ?_, ?_⟩
  · intro n ω ω' h
    exact congrArg Prod.fst (hπ.2.1 n ω ω' h)
  · intro ω n
    exact (hπ.2.2 ω n).1

lemma admissible_traj_domain (π : Policy (ℝ × ℝ)) (s : M.State)
    (hπ : M.system.Admissible π s) (hs : M.InDomain s) (ω : ℕ → ℝ) (n : ℕ) :
    M.InDomain (M.system.traj π s ω n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact domain_next M _ _ _ ih (hπ.2.2 ω n)

/-- Capped critical shipments following a prescribed history-dependent order stream. -/
noncomputable def followTraj (πd : Policy ℝ) (xstar : ℝ) (s : M.State) (ω : ℕ → ℝ) :
    ℕ → M.State
  | 0 => s
  | n + 1 => M.system.next (followTraj πd xstar s ω n)
      (M.piStar (fun _ => πd n ω) xstar (followTraj πd xstar s ω n)) (ω n)

noncomputable def followOrders (πd : Policy ℝ) (xstar : ℝ) (s : M.State) : Policy (ℝ × ℝ) :=
  fun n ω => M.piStar (fun _ => πd n ω) xstar (followTraj M πd xstar s ω n)

lemma followOrders_traj (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (ω : ℕ → ℝ) (n : ℕ) :
    M.system.traj (followOrders M πd xstar s) s ω n = followTraj M πd xstar s ω n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ControlSystem.traj, followTraj, followOrders, ih]

lemma projectOrders_follow (πd : Policy ℝ) (xstar : ℝ) (s : M.State) :
    projectOrders (followOrders M πd xstar s) = πd := rfl

lemma followTraj_domain (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (hnn : ∀ n ω, 0 ≤ πd n ω) (hs : M.InDomain s) (ω : ℕ → ℝ) (n : ℕ) :
    M.InDomain (followTraj M πd xstar s ω n) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    exact domain_next M _ _ _ ih (piStar_feasible M (fun _ => πd n ω) xstar
      (fun _ => hnn n ω) _ ih)

lemma follow_action_measurable {Ω : Type*} [MeasurableSpace Ω]
    (xstar : ℝ) (f : Ω → M.State) (g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => M.piStar (fun _ => g ω) xstar (f ω)) := by
  have ha : Measurable (fun ω => M.arrival (f ω).1 (g ω)) :=
    (arrival_measurable M).comp (hf.fst.prodMk hg)
  change Measurable (fun ω => (g ω,
    max 0 (min xstar ((f ω).2.1 + M.arrival (f ω).1 (g ω)) - (f ω).2.2)))
  exact hg.prodMk (measurable_const.max
    ((measurable_const.min (hf.snd.fst.add ha)).sub hf.snd.snd))

lemma followTraj_measurable (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (hm : ∀ n, Measurable (πd n)) (n : ℕ) :
    Measurable (fun ω => followTraj M πd xstar s ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (system_next_measurable M).comp
      (ih.prodMk ((follow_action_measurable M xstar _ _ ih (hm n)).prodMk (measurable_pi_apply n)))

lemma followTraj_prefix (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (hπ : ControlSystem.NonAnticipative πd) (ω ω' : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < n, ω j = ω' j) :
    followTraj M πd xstar s ω n = followTraj M πd xstar s ω' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : ∀ j < n, ω j = ω' j := fun j hj => h j (Nat.lt_succ_of_lt hj)
    simp only [followTraj, ih hp, hπ n ω ω' hp, h n (Nat.lt_succ_self n)]

lemma followOrders_admissible (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (hm : ∀ n, Measurable (πd n)) (hp : ControlSystem.NonAnticipative πd)
    (hnn : ∀ n ω, 0 ≤ πd n ω) (hs : M.InDomain s) :
    M.system.Admissible (followOrders M πd xstar s) s := by
  refine ⟨fun n => follow_action_measurable M xstar _ _
    (followTraj_measurable M πd xstar s hm n) (hm n), ?_, ?_⟩
  · intro n ω ω' h
    simp only [followOrders, followTraj_prefix M πd xstar s hp ω ω' n h, hp n ω ω' h]
  · intro ω n
    rw [followOrders_traj]
    exact piStar_feasible M (fun _ => πd n ω) xstar (fun _ => hnn n ω) _
      (followTraj_domain M πd xstar s hnn hs ω n)

noncomputable def unservedStock (x : ℝ) (ω : ℕ → ℝ) (n : ℕ) : ℝ :=
  x - ∑ j ∈ Finset.range n, ω j

lemma unservedStock_succ (x : ℝ) (ω : ℕ → ℝ) (n : ℕ) :
    unservedStock x ω (n + 1) = unservedStock x ω n - ω n := by
  simp only [unservedStock, Finset.sum_range_succ]
  ring

lemma traj_stock_lower (π : Policy (ℝ × ℝ)) (s : M.State)
    (hπ : M.system.Admissible π s) (ω : ℕ → ℝ) (n : ℕ) :
    unservedStock s.2.2 ω n ≤ (M.system.traj π s ω n).2.2 := by
  induction n with
  | zero => simp [unservedStock, ControlSystem.traj]
  | succ n ih =>
    rw [unservedStock_succ]
    change _ ≤ (M.system.traj π s ω n).2.2 + (π n ω).2 - ω n
    linarith [(hπ.2.2 ω n).2.1]

lemma follow_stock_lower (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (ω : ℕ → ℝ) (n : ℕ) :
    unservedStock s.2.2 ω n ≤ (followTraj M πd xstar s ω n).2.2 := by
  induction n with
  | zero => simp [unservedStock, followTraj]
  | succ n ih =>
    rw [unservedStock_succ]
    change _ ≤ (followTraj M πd xstar s ω n).2.2 +
      max 0 (min xstar ((followTraj M πd xstar s ω n).2.1 +
        M.arrival (followTraj M πd xstar s ω n).1 (πd n ω)) -
          (followTraj M πd xstar s ω n).2.2) - ω n
    linarith [le_max_left (0 : ℝ) (min xstar
      ((followTraj M πd xstar s ω n).2.1 + M.arrival (followTraj M πd xstar s ω n).1 (πd n ω)) -
        (followTraj M πd xstar s ω n).2.2)]

lemma capped_post_le (xstar x w : ℝ) : x + max 0 (min xstar w - x) ≤ max xstar x := by
  rw [add_max]
  apply max_le
  · simpa using le_max_right xstar x
  · linarith [min_le_left xstar w, le_max_left xstar x]

lemma follow_stock_upper (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    (followTraj M πd xstar s ω n).2.2 ≤ max xstar (unservedStock s.2.2 ω n) := by
  induction n with
  | zero => simpa [followTraj, unservedStock] using le_max_right xstar s.2.2
  | succ n ih =>
    rw [unservedStock_succ]
    have hu := capped_post_le xstar (followTraj M πd xstar s ω n).2.2
      ((followTraj M πd xstar s ω n).2.1 + M.arrival (followTraj M πd xstar s ω n).1 (πd n ω))
    have hm : max xstar (followTraj M πd xstar s ω n).2.2 ≤
        max xstar (unservedStock s.2.2 ω n) := max_le (le_max_left _ _) ih
    change (followTraj M πd xstar s ω n).2.2 +
      max 0 (min xstar ((followTraj M πd xstar s ω n).2.1 +
        M.arrival (followTraj M πd xstar s ω n).1 (πd n ω)) -
          (followTraj M πd xstar s ω n).2.2) - ω n ≤ _
    calc
      _ ≤ max xstar (unservedStock s.2.2 ω n) - ω n := sub_le_sub_right (hu.trans hm) _
      _ ≤ _ := by
        rw [sub_eq_add_neg, ← max_add_add_right]
        exact max_le_max (by linarith [hω n]) le_rfl

lemma convexGapExcess_eq_of_interval (F : ℝ → ℝ) (a b x : ℝ)
    (hbx : b ≤ x) (hxb : x ≤ max a b) :
    convexGapExcess F a x = convexGapExcess F a b := by
  by_cases hb : a ≤ b
  · have h : x = b := by rw [max_eq_right hb] at hxb; linarith
    rw [h]
  · have hxa : x ≤ a := by rw [max_eq_left (le_of_not_ge hb)] at hxb; exact hxb
    unfold convexGapExcess
    by_cases hx : a ≤ x
    · have h : x = a := le_antisymm hxa hx
      simp [h, hb]
    · simp [hx, hb]

lemma follow_gap_eq (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    convexGapExcess (stationaryObjective M) xstar (followTraj M πd xstar s ω n).2.2 =
      convexGapExcess (stationaryObjective M) xstar (unservedStock s.2.2 ω n) :=
  convexGapExcess_eq_of_interval _ _ _ _ (follow_stock_lower M πd xstar s ω n)
    (follow_stock_upper M πd xstar s ω hω n)

end FZEchelon.Discounted

/- Inlined source: Stationary. -/

open MeasureTheory

namespace FZEchelon.Discounted

variable (M : Model)

lemma depot_statTraj_projection (σ : M.DepotState → ℝ) (xstar : ℝ) (s : M.State)
    (ω : ℕ → ℝ) (n : ℕ) :
    (M.depotSystem xstar).statTraj σ (s.1, s.2.1) ω n =
      ((M.system.statTraj (M.piStar σ xstar) s ω n).1,
        (M.system.statTraj (M.piStar σ xstar) s ω n).2.1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ControlSystem.statTraj, Model.depotSystem, Model.system, Model.piStar] at ih ⊢
    rw [ih]

lemma projectOrders_stationary (σ : M.DepotState → ℝ) (xstar : ℝ) (s : M.State) :
    projectOrders (M.system.stationary (M.piStar σ xstar) s) =
      (M.depotSystem xstar).stationary σ (s.1, s.2.1) := by
  funext n ω
  change σ ((M.system.statTraj (M.piStar σ xstar) s ω n).1,
      (M.system.statTraj (M.piStar σ xstar) s ω n).2.1) =
    σ ((M.depotSystem xstar).statTraj σ (s.1, s.2.1) ω n)
  rw [depot_statTraj_projection M σ xstar s ω n]

lemma followTraj_stationary (σ : M.DepotState → ℝ) (xstar : ℝ) (s : M.State)
    (ω : ℕ → ℝ) (n : ℕ) :
    followTraj M ((M.depotSystem xstar).stationary σ (s.1, s.2.1)) xstar s ω n =
      M.system.statTraj (M.piStar σ xstar) s ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [followTraj, ControlSystem.statTraj, ControlSystem.stationary, ih]
    rw [depot_statTraj_projection M σ xstar s ω n]
    rfl

lemma followOrders_stationary (σ : M.DepotState → ℝ) (xstar : ℝ) (s : M.State) :
    followOrders M ((M.depotSystem xstar).stationary σ (s.1, s.2.1)) xstar s =
      M.system.stationary (M.piStar σ xstar) s := by
  funext n ω
  simp only [followOrders, ControlSystem.stationary, followTraj_stationary M σ xstar s ω n]
  rw [depot_statTraj_projection M σ xstar s ω n]
  rfl

lemma depot_next_measurable (xstar : ℝ) :
    Measurable (fun q : M.DepotState × ℝ × ℝ =>
      (M.depotSystem xstar).next q.1 q.2.1 q.2.2) := by
  have hshift : Measurable (fun q : M.DepotState × ℝ × ℝ => M.shift q.1.1 q.2.1) :=
    (shift_measurable M).comp (measurable_fst.fst.prodMk measurable_snd.fst)
  have harr : Measurable (fun q : M.DepotState × ℝ × ℝ => M.arrival q.1.1 q.2.1) :=
    (arrival_measurable M).comp (measurable_fst.fst.prodMk measurable_snd.fst)
  change Measurable (fun q : M.DepotState × ℝ × ℝ =>
    (M.shift q.1.1 q.2.1, q.1.2 + M.arrival q.1.1 q.2.1 - q.2.2))
  exact hshift.prodMk ((measurable_fst.snd.add harr).sub measurable_snd.snd)

lemma depot_statTraj_measurable (σ : M.DepotState → ℝ) (hσ : Measurable σ)
    (xstar : ℝ) (p : M.DepotState) (n : ℕ) :
    Measurable (fun ω => (M.depotSystem xstar).statTraj σ p ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun ω => (M.depotSystem xstar).next
      ((M.depotSystem xstar).statTraj σ p ω n)
      (σ ((M.depotSystem xstar).statTraj σ p ω n)) (ω n))
    exact (depot_next_measurable M xstar).comp
      (ih.prodMk ((hσ.comp ih).prodMk (measurable_pi_apply n)))

lemma depot_statTraj_prefix (σ : M.DepotState → ℝ) (xstar : ℝ) (p : M.DepotState)
    (ω ω' : ℕ → ℝ) (n : ℕ) (h : ∀ j < n, ω j = ω' j) :
    (M.depotSystem xstar).statTraj σ p ω n = (M.depotSystem xstar).statTraj σ p ω' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ControlSystem.statTraj]
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

lemma depot_stationary_admissible (σ : M.DepotState → ℝ) (hσm : Measurable σ)
    (hσnn : ∀ p, 0 ≤ σ p) (xstar : ℝ) (p : M.DepotState) :
    (M.depotSystem xstar).Admissible ((M.depotSystem xstar).stationary σ p) p := by
  constructor
  · intro n
    exact hσm.comp (depot_statTraj_measurable M σ hσm xstar p n)
  constructor
  · intro n ω ω' h
    change σ ((M.depotSystem xstar).statTraj σ p ω n) =
      σ ((M.depotSystem xstar).statTraj σ p ω' n)
    rw [depot_statTraj_prefix M σ xstar p ω ω' n h]
  · intro ω n
    exact hσnn _

end FZEchelon.Discounted

/- Inlined source: FiniteComparison. -/

namespace FZEchelon.Discounted

lemma discounted_decomposition (α c r : ℝ) (f g e x z d : ℕ → ℝ)
    (hs : ∀ k, f k = g k + c + r * (α * (x k + z k) - x k) + e k)
    (hx : ∀ k, x (k + 1) = x k + z k - d k) (n : ℕ) :
    (∑ k ∈ Finset.range n, α ^ k * f k) =
      (∑ k ∈ Finset.range n, α ^ k * g k) + c * (∑ k ∈ Finset.range n, α ^ k) +
        r * (α ^ n * x n - x 0 + ∑ k ∈ Finset.range n, α ^ (k + 1) * d k) +
        ∑ k ∈ Finset.range n, α ^ k * e k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [ih, hs n, hx n]
    simp only [pow_succ]
    ring

variable (M : Model)

noncomputable def stageGap (xstar : ℝ) (s : M.State) (a : ℝ × ℝ) : ℝ :=
  stationaryObjective M (s.2.2 + a.2) - stationaryObjective M xstar -
    M.P xstar (s.2.1 + M.arrival s.1 a.1)

noncomputable def systemPartial (π : Policy (ℝ × ℝ)) (s : M.State) (ω : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, M.α ^ k * M.system.cost (M.system.traj π s ω k) (π k ω)

noncomputable def depotPartial (xstar : ℝ) (πd : Policy ℝ) (p : M.DepotState)
    (ω : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, M.α ^ k * (M.depotSystem xstar).cost
    ((M.depotSystem xstar).traj πd p ω k) (πd k ω)

noncomputable def baselineGap (xstar x : ℝ) (ω : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, M.α ^ k *
    convexGapExcess (stationaryObjective M) xstar (unservedStock x ω k)

noncomputable def commonPartial (xstar x : ℝ) (ω : ℕ → ℝ) (n : ℕ) : ℝ :=
  stationaryObjective M xstar * (∑ k ∈ Finset.range n, M.α ^ k) +
    M.cr * (-x + ∑ k ∈ Finset.range n, M.α ^ (k + 1) * ω k) +
    baselineGap M xstar x ω n

lemma systemPartial_decomposition (xstar : ℝ) (π : Policy (ℝ × ℝ)) (s : M.State)
    (ω : ℕ → ℝ) (n : ℕ) :
    systemPartial M π s ω n = depotPartial M xstar (projectOrders π) (s.1, s.2.1) ω n +
      stationaryObjective M xstar * (∑ k ∈ Finset.range n, M.α ^ k) +
      M.cr * (M.α ^ n * (M.system.traj π s ω n).2.2 - s.2.2 +
        ∑ k ∈ Finset.range n, M.α ^ (k + 1) * ω k) +
      ∑ k ∈ Finset.range n, M.α ^ k * stageGap M xstar (M.system.traj π s ω k) (π k ω) := by
  apply discounted_decomposition M.α (stationaryObjective M xstar) M.cr
    (fun k => M.system.cost (M.system.traj π s ω k) (π k ω))
    (fun k => (M.depotSystem xstar).cost
      ((M.depotSystem xstar).traj (projectOrders π) (s.1, s.2.1) ω k) (projectOrders π k ω))
    (fun k => stageGap M xstar (M.system.traj π s ω k) (π k ω))
    (fun k => (M.system.traj π s ω k).2.2) (fun k => (π k ω).2) ω
  · intro k
    rw [projectOrders_traj]
    exact one_step_decomposition M xstar _ _
  · intro k
    rfl

lemma pathGap_lower (hM : M.StandingAssumptions) (xstar : ℝ)
    (hx : M.IsStationaryCriticalNumber xstar) (π : Policy (ℝ × ℝ)) (s : M.State)
    (hπ : M.system.Admissible π s) (ω : ℕ → ℝ) (n : ℕ) :
    baselineGap M xstar s.2.2 ω n ≤
      ∑ k ∈ Finset.range n, M.α ^ k * stageGap M xstar (M.system.traj π s ω k) (π k ω) := by
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hM.α_nonneg k)
  apply (convexGapExcess_monotone _ _ (stationaryObjective_convex M hM)
    (stationaryObjective_min M xstar hx) (traj_stock_lower M π s hπ ω k)).trans
  exact feasible_stage_gap M hM xstar hx _ _ _ (by linarith [(hπ.2.2 ω k).2.1])
    (hπ.2.2 ω k).2.2

lemma follow_pathGap (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (hnn : ∀ n ω, 0 ≤ πd n ω) (hs : M.InDomain s)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    stageGap M xstar (M.system.traj (followOrders M πd xstar s) s ω n)
      (followOrders M πd xstar s n ω) =
        convexGapExcess (stationaryObjective M) xstar (unservedStock s.2.2 ω n) := by
  rw [followOrders_traj]
  have hd := followTraj_domain M πd xstar s hnn hs ω n
  have ha := arrival_nonneg M
    ((followTraj M πd xstar s ω n).1, (followTraj M πd xstar s ω n).2.1)
    (πd n ω) hd.1 (hnn n ω)
  have hb : (followTraj M πd xstar s ω n).2.2 ≤
      (followTraj M πd xstar s ω n).2.1 +
        M.arrival (followTraj M πd xstar s ω n).1 (πd n ω) := by linarith [hd.2]
  change stationaryObjective M ((followTraj M πd xstar s ω n).2.2 +
    max 0 (min xstar ((followTraj M πd xstar s ω n).2.1 +
      M.arrival (followTraj M πd xstar s ω n).1 (πd n ω)) -
        (followTraj M πd xstar s ω n).2.2)) - stationaryObjective M xstar -
      M.P xstar ((followTraj M πd xstar s ω n).2.1 +
        M.arrival (followTraj M πd xstar s ω n).1 (πd n ω)) = _
  rw [candidate_stage_gap M xstar _ _ hb, follow_gap_eq M πd xstar s ω hω n]

lemma followPartial_decomposition (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (hnn : ∀ n ω, 0 ≤ πd n ω) (hs : M.InDomain s)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    systemPartial M (followOrders M πd xstar s) s ω n =
      depotPartial M xstar πd (s.1, s.2.1) ω n + commonPartial M xstar s.2.2 ω n +
        M.cr * M.α ^ n * (followTraj M πd xstar s ω n).2.2 := by
  rw [systemPartial_decomposition M xstar, projectOrders_follow, followOrders_traj]
  simp only [follow_pathGap M πd xstar s hnn hs ω hω]
  unfold commonPartial baselineGap
  ring

lemma systemPartial_lower (hM : M.StandingAssumptions) (xstar : ℝ)
    (hx : M.IsStationaryCriticalNumber xstar) (π : Policy (ℝ × ℝ)) (s : M.State)
    (hπ : M.system.Admissible π s) (ω : ℕ → ℝ) (n : ℕ) :
    depotPartial M xstar (projectOrders π) (s.1, s.2.1) ω n +
      commonPartial M xstar s.2.2 ω n +
        M.cr * M.α ^ n * (M.system.traj π s ω n).2.2 ≤ systemPartial M π s ω n := by
  have hg := pathGap_lower M hM xstar hx π s hπ ω n
  rw [systemPartial_decomposition M xstar]
  dsimp only [commonPartial, baselineGap] at hg ⊢
  linarith

lemma follow_stock_uniform_upper (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    (followTraj M πd xstar s ω n).2.2 ≤ max xstar s.2.2 := by
  apply (follow_stock_upper M πd xstar s ω hω n).trans
  apply max_le_max le_rfl
  unfold unservedStock
  have hsum : 0 ≤ ∑ k ∈ Finset.range n, ω k := Finset.sum_nonneg (fun k _ => hω k)
  linarith

/-- Keeping orders fixed and using capped critical shipments cannot increase
finite-horizon cost by more than a demand-only discounted terminal bound. -/
lemma followPartial_le (hM : M.StandingAssumptions) (xstar : ℝ)
    (hx : M.IsStationaryCriticalNumber xstar) (π : Policy (ℝ × ℝ)) (s : M.State)
    (hπ : M.system.Admissible π s) (hs : M.InDomain s)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    systemPartial M (followOrders M (projectOrders π) xstar s) s ω n ≤
      systemPartial M π s ω n + M.cr * M.α ^ n *
        (max xstar s.2.2 - s.2.2 + ∑ k ∈ Finset.range n, ω k) := by
  have hnn : ∀ n ω, 0 ≤ projectOrders π n ω := fun n ω => (hπ.2.2 ω n).1
  rw [followPartial_decomposition M (projectOrders π) xstar s hnn hs ω hω n]
  have hl := systemPartial_lower M hM xstar hx π s hπ ω n
  have hu := follow_stock_uniform_upper M (projectOrders π) xstar s ω hω n
  have hxlow := traj_stock_lower M π s hπ ω n
  have hd : (followTraj M (projectOrders π) xstar s ω n).2.2 -
      (M.system.traj π s ω n).2.2 ≤ max xstar s.2.2 - s.2.2 +
        ∑ k ∈ Finset.range n, ω k := by
    unfold unservedStock at hxlow
    linarith
  have hmul := mul_le_mul_of_nonneg_left hd
    (mul_nonneg hM.cr_pos.le (pow_nonneg hM.α_nonneg n))
  linarith

end FZEchelon.Discounted

/- Inlined source: SeriesComparison. -/

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

/-- Finite comparisons with an integrable error tending to zero compare the
expected nonnegative infinite series, without integrability of either series. -/
lemma lintegral_series_le_of_partial_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : ℕ → Ω → ℝ) (e : ℕ → Ω → ℝ)
    (hf : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ f k ω) (hg : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ g k ω)
    (hgm : ∀ k, AEMeasurable (g k) μ)
    (he : ∀ n, Integrable (e n) μ) (hen : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ e n ω)
    (helim : Tendsto (fun n => ∫ ω, e n ω ∂μ) atTop (𝓝 0))
    (hle : ∀ n, ∀ᵐ ω ∂μ,
      (∑ k ∈ Finset.range n, g k ω) ≤ (∑ k ∈ Finset.range n, f k ω) + e n ω) :
    (∫⁻ ω, ∑' k, ENNReal.ofReal (g k ω) ∂μ) ≤
      ∫⁻ ω, ∑' k, ENNReal.ofReal (f k ω) ∂μ := by
  have hfa : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ f k ω := ae_all_iff.2 hf
  have hga : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ g k ω := ae_all_iff.2 hg
  have hb (n : ℕ) :
      (∑ k ∈ Finset.range n, ∫⁻ ω, ENNReal.ofReal (g k ω) ∂μ) ≤
        (∫⁻ ω, ∑' k, ENNReal.ofReal (f k ω) ∂μ) +
          ENNReal.ofReal (∫ ω, e n ω ∂μ) := by
    rw [← lintegral_finsetSum' _ (fun k _ => (hgm k).ennreal_ofReal),
      ofReal_integral_eq_lintegral_ofReal (he n) (hen n),
      ← lintegral_add_right' _ (he n).aestronglyMeasurable.aemeasurable.ennreal_ofReal]
    apply lintegral_mono_ae
    filter_upwards [hfa, hga, hen n, hle n] with ω hfω hgω heω hleω
    calc
      (∑ k ∈ Finset.range n, ENNReal.ofReal (g k ω)) =
          ENNReal.ofReal (∑ k ∈ Finset.range n, g k ω) :=
        (ENNReal.ofReal_sum_of_nonneg (fun k _ => hgω k)).symm
      _ ≤ ENNReal.ofReal ((∑ k ∈ Finset.range n, f k ω) + e n ω) :=
        ENNReal.ofReal_le_ofReal hleω
      _ = (∑ k ∈ Finset.range n, ENNReal.ofReal (f k ω)) + ENNReal.ofReal (e n ω) := by
        rw [ENNReal.ofReal_add (Finset.sum_nonneg (fun k _ => hfω k)) heω,
          ENNReal.ofReal_sum_of_nonneg (fun k _ => hfω k)]
      _ ≤ (∑' k, ENNReal.ofReal (f k ω)) + ENNReal.ofReal (e n ω) :=
        add_le_add (ENNReal.sum_le_tsum _) le_rfl
  have hl := (tendsto_const_nhds : Tendsto
    (fun _ : ℕ => ∫⁻ ω, ∑' k, ENNReal.ofReal (f k ω) ∂μ) atTop
    (𝓝 (∫⁻ ω, ∑' k, ENNReal.ofReal (f k ω) ∂μ))).add
      (ENNReal.tendsto_ofReal helim)
  simp only [ENNReal.ofReal_zero, add_zero] at hl
  rw [lintegral_tsum (fun k => (hgm k).ennreal_ofReal)]
  exact le_of_tendsto_of_tendsto' (ENNReal.tendsto_nat_tsum _) hl hb

end FZEchelon.Discounted

/- Inlined source: DemandBounds. -/

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

variable (M : Model)

noncomputable abbrev pathMeasure := Measure.infinitePi (fun _ : ℕ => M.ν)

noncomputable def demandPrefix (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, ω k

lemma path_nonneg (hM : M.StandingAssumptions) :
    ∀ᵐ ω ∂pathMeasure M, ∀ n, 0 ≤ ω n := by
  have hν : ∀ᵐ t ∂M.ν, 0 ≤ t := by
    simpa only [ae_iff, not_le, Set.Iio] using hM.demand_nonneg
  rw [ae_all_iff]
  intro n
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => M.ν) n).quasiMeasurePreserving.tendsto_ae hν

lemma demand_coordinate_integrable (hM : M.StandingAssumptions) (n : ℕ) :
    Integrable (fun ω : ℕ → ℝ => ω n) (pathMeasure M) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => M.ν) n).integrable_comp_of_integrable
    hM.demand_integrable

lemma demand_coordinate_integral (n : ℕ) :
    (∫ ω : ℕ → ℝ, ω n ∂pathMeasure M) = M.mu := by
  have hi := integral_map (μ := pathMeasure M) (φ := fun ω : ℕ → ℝ => ω n)
    (f := fun t : ℝ => t) (measurable_pi_apply n).aemeasurable aestronglyMeasurable_id
  rw [Measure.infinitePi_map_eval] at hi
  exact hi.symm

lemma demandPrefix_measurable (n : ℕ) : Measurable (demandPrefix n) := by
  unfold demandPrefix
  fun_prop

lemma demandPrefix_nonneg (n : ℕ) (ω : ℕ → ℝ) (hω : ∀ k, 0 ≤ ω k) :
    0 ≤ demandPrefix n ω := Finset.sum_nonneg (fun k _ => hω k)

lemma demandPrefix_integrable (hM : M.StandingAssumptions) (n : ℕ) :
    Integrable (demandPrefix n) (pathMeasure M) :=
  integrable_finsetSum _ (fun k _ => demand_coordinate_integrable M hM k)

lemma demandPrefix_integral (hM : M.StandingAssumptions) (n : ℕ) :
    (∫ ω, demandPrefix n ω ∂pathMeasure M) = (n : ℝ) * M.mu := by
  simp only [demandPrefix]
  rw [integral_finsetSum _ (fun k _ => demand_coordinate_integrable M hM k)]
  simp only [demand_coordinate_integral, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Geometric discount dominates the linear growth of the expected cumulative demand. -/
lemma geometric_linear_tendsto_zero {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (A B : ℝ) :
    Tendsto (fun n : ℕ => α ^ n * (A + B * n)) atTop (𝓝 0) := by
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).mul_const A
  have h2 := (tendsto_self_mul_const_pow_of_lt_one hα0 hα1).mul_const B
  convert h1.add h2 using 1 <;> ring

lemma geometric_linear_summable {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (A B : ℝ) :
    Summable (fun n : ℕ => α ^ n * (A + B * n)) := by
  have hn : ‖α‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hα0] using hα1
  have h1 := (summable_geometric_of_norm_lt_one hn).mul_right A
  have h2 := (summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_right B
  apply (h1.add h2).congr
  intro n
  simp only [pow_one]
  ring

noncomputable def terminalError (α c A : ℝ) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  c * α ^ n * (A + demandPrefix n ω)

lemma terminalError_integrable (hM : M.StandingAssumptions) (α c A : ℝ) (n : ℕ) :
    Integrable (terminalError α c A n) (pathMeasure M) :=
  ((integrable_const A).add (demandPrefix_integrable M hM n)).const_mul _

lemma terminalError_integral (hM : M.StandingAssumptions) (α c A : ℝ) (n : ℕ) :
    (∫ ω, terminalError α c A n ω ∂pathMeasure M) = c * α ^ n * (A + n * M.mu) := by
  simp only [terminalError]
  rw [integral_const_mul,
    integral_add (integrable_const A) (demandPrefix_integrable M hM n),
    integral_const, demandPrefix_integral M hM]
  simp

lemma terminalError_integral_tendsto_zero (hM : M.StandingAssumptions) (hα : M.α < 1)
    (c A : ℝ) :
    Tendsto (fun n => ∫ ω, terminalError M.α c A n ω ∂pathMeasure M) atTop (𝓝 0) := by
  simp only [terminalError_integral M hM]
  have h := (geometric_linear_tendsto_zero hM.α_nonneg hα A M.mu).const_mul c
  simp only [mul_zero] at h
  apply h.congr
  intro n
  ring

lemma terminalError_integral_summable (hM : M.StandingAssumptions) (hα : M.α < 1)
    (c A : ℝ) :
    Summable (fun n => ∫ ω, terminalError M.α c A n ω ∂pathMeasure M) := by
  simp only [terminalError_integral M hM]
  apply ((geometric_linear_summable hM.α_nonneg hα A M.mu).mul_left c).congr
  intro n
  ring

noncomputable def demandEnvelope (α A B : ℝ) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  α ^ n * (A + B * demandPrefix n ω)

lemma demandEnvelope_integrable (hM : M.StandingAssumptions) (α A B : ℝ) (n : ℕ) :
    Integrable (demandEnvelope α A B n) (pathMeasure M) :=
  ((integrable_const A).add ((demandPrefix_integrable M hM n).const_mul B)).const_mul _

lemma demandEnvelope_integral (hM : M.StandingAssumptions) (α A B : ℝ) (n : ℕ) :
    (∫ ω, demandEnvelope α A B n ω ∂pathMeasure M) = α ^ n * (A + B * (n * M.mu)) := by
  simp only [demandEnvelope]
  rw [integral_const_mul,
    integral_add (integrable_const A) ((demandPrefix_integrable M hM n).const_mul B),
    integral_const_mul, integral_const, demandPrefix_integral M hM]
  simp

lemma demandEnvelope_integral_summable (hM : M.StandingAssumptions) (hα : M.α < 1)
    (A B : ℝ) :
    Summable (fun n => ∫ ω, demandEnvelope M.α A B n ω ∂pathMeasure M) := by
  simp only [demandEnvelope_integral M hM]
  apply (geometric_linear_summable hM.α_nonneg hα A (B * M.mu)).congr
  intro n
  ring

end FZEchelon.Discounted

/- Inlined source: StageMeasurable. -/

open MeasureTheory

namespace FZEchelon.Discounted

variable (M : Model)

lemma system_traj_measurable (π : Policy (ℝ × ℝ)) (s : M.State)
    (hm : ∀ n, Measurable (π n)) (n : ℕ) :
    Measurable (fun ω => M.system.traj π s ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (system_next_measurable M).comp
      (ih.prodMk ((hm n).prodMk (measurable_pi_apply n)))

lemma depot_traj_measurable (xstar : ℝ) (πd : Policy ℝ) (p : M.DepotState)
    (hm : ∀ n, Measurable (πd n)) (n : ℕ) :
    Measurable (fun ω => (M.depotSystem xstar).traj πd p ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (depot_next_measurable M xstar).comp
      (ih.prodMk ((hm n).prodMk (measurable_pi_apply n)))

lemma orderCost_measurable : Measurable M.orderCost := by
  unfold Model.orderCost
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
  · exact measurable_const
  · fun_prop

lemma penalty_measurable (hM : M.StandingAssumptions) (xstar : ℝ) :
    Measurable (M.P xstar) := by
  have hR := (CostBounds.R_continuous M hM).measurable
  unfold Model.P
  apply Measurable.ite measurableSet_Ici
  · exact measurable_const
  · exact (measurable_const.mul (measurable_id.sub measurable_const)).add
      (hR.sub measurable_const)

lemma objective_measurable (hM : M.StandingAssumptions) :
    Measurable (stationaryObjective M) :=
  (measurable_const.mul measurable_id).add (CostBounds.R_continuous M hM).measurable

lemma excess_measurable (hM : M.StandingAssumptions) (xstar : ℝ) :
    Measurable (convexGapExcess (stationaryObjective M) xstar) := by
  unfold convexGapExcess
  exact Measurable.ite measurableSet_Ici ((objective_measurable M hM).sub measurable_const)
    measurable_const

lemma system_cost_measurable (hM : M.StandingAssumptions) :
    Measurable (fun q : M.State × (ℝ × ℝ) => M.system.cost q.1 q.2) := by
  have ha : Measurable (fun q : M.State × (ℝ × ℝ) => M.arrival q.1.1 q.2.1) :=
    (arrival_measurable M).comp (measurable_fst.fst.prodMk measurable_snd.fst)
  exact (((orderCost_measurable M).comp measurable_snd.fst).add
    (measurable_const.mul (measurable_fst.snd.fst.add ha))).add
      (measurable_const.mul measurable_snd.snd) |>.add
        ((CostBounds.R_continuous M hM).measurable.comp
          (measurable_fst.snd.snd.add measurable_snd.snd))

lemma depot_cost_measurable (hM : M.StandingAssumptions) (xstar : ℝ) :
    Measurable (fun q : M.DepotState × ℝ => (M.depotSystem xstar).cost q.1 q.2) := by
  have ha : Measurable (fun q : M.DepotState × ℝ => M.arrival q.1.1 q.2) :=
    (arrival_measurable M).comp (measurable_fst.fst.prodMk measurable_snd)
  exact (((orderCost_measurable M).comp measurable_snd).add
    (measurable_const.mul (measurable_fst.snd.add ha))).add
      ((penalty_measurable M hM xstar).comp (measurable_fst.snd.add ha))

noncomputable def systemStage (π : Policy (ℝ × ℝ)) (s : M.State) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  M.α ^ n * M.system.cost (M.system.traj π s ω n) (π n ω)

noncomputable def depotStage (xstar : ℝ) (πd : Policy ℝ) (p : M.DepotState)
    (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  M.α ^ n * (M.depotSystem xstar).cost ((M.depotSystem xstar).traj πd p ω n) (πd n ω)

lemma systemStage_measurable (hM : M.StandingAssumptions) (π : Policy (ℝ × ℝ)) (s : M.State)
    (hm : ∀ n, Measurable (π n)) (n : ℕ) : Measurable (systemStage M π s n) :=
  measurable_const.mul ((system_cost_measurable M hM).comp
    ((system_traj_measurable M π s hm n).prodMk (hm n)))

lemma depotStage_measurable (hM : M.StandingAssumptions) (xstar : ℝ) (πd : Policy ℝ)
    (p : M.DepotState) (hm : ∀ n, Measurable (πd n)) (n : ℕ) :
    Measurable (depotStage M xstar πd p n) :=
  measurable_const.mul ((depot_cost_measurable M hM xstar).comp
    ((depot_traj_measurable M xstar πd p hm n).prodMk (hm n)))

lemma systemStage_nonneg (hM : M.StandingAssumptions)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (π : Policy (ℝ × ℝ)) (s : M.State) (hπ : M.system.Admissible π s)
    (n : ℕ) (ω : ℕ → ℝ) : 0 ≤ systemStage M π s n ω :=
  mul_nonneg (pow_nonneg hM.α_nonneg n)
    (CostBounds.system_stage_nonneg M hM hcost _ _ (hπ.2.2 ω n))

end FZEchelon.Discounted

/- Inlined source: ExtendedAccounting. -/

open MeasureTheory

namespace FZEchelon.Discounted.Accounting

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The expected sum of the positive parts of a sequence of real stage costs.
Discount factors, if present, are already included in the stage costs. -/
noncomputable def positiveSeries (μ : Measure Ω) (f : ℕ → Ω → ℝ) : ENNReal :=
  ∫⁻ ω, ∑' k, ENNReal.ofReal (f k ω) ∂μ

/-- The signed extended expectation used by `ControlSystem.discCost`. -/
noncomputable def signedSeries (μ : Measure Ω) (f : ℕ → Ω → ℝ) : EReal :=
  (positiveSeries μ f : EReal) -
    (positiveSeries μ (fun k ω => -f k ω) : EReal)

lemma positiveSeries_eq_tsum (μ : Measure Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ k, AEMeasurable (f k) μ) :
    positiveSeries μ f = ∑' k, ∫⁻ ω, ENNReal.ofReal (f k ω) ∂μ :=
  lintegral_tsum (fun k => (hf k).ennreal_ofReal)

lemma positiveSeries_mono (μ : Measure Ω) (f g : ℕ → Ω → ℝ)
    (hfg : ∀ k, ∀ᵐ ω ∂μ, f k ω ≤ g k ω) :
    positiveSeries μ f ≤ positiveSeries μ g := by
  apply lintegral_mono_ae
  filter_upwards [ae_all_iff.2 hfg] with ω hω
  exact ENNReal.tsum_le_tsum (fun k => ENNReal.ofReal_le_ofReal (hω k))

lemma positiveSeries_neg_eq_zero (μ : Measure Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ f k ω) :
    positiveSeries μ (fun k ω => -f k ω) = 0 := by
  have heq : (fun ω => ∑' k, ENNReal.ofReal (-f k ω)) =ᵐ[μ] (fun _ => 0) := by
    filter_upwards [ae_all_iff.2 hf] with ω hω
    calc
      (∑' k, ENNReal.ofReal (-f k ω)) = ∑' _ : ℕ, (0 : ENNReal) :=
        tsum_congr (fun k => ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (hω k)))
      _ = 0 := tsum_zero
  exact (lintegral_congr_ae heq).trans (lintegral_zero)

lemma signedSeries_of_nonneg (μ : Measure Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ f k ω) :
    signedSeries μ f = (positiveSeries μ f : EReal) := by
  rw [signedSeries, positiveSeries_neg_eq_zero μ f hf,
    EReal.coe_ennreal_zero, sub_zero]

lemma signedSeries_ne_bot (μ : Measure Ω) (f : ℕ → Ω → ℝ)
    (hneg : positiveSeries μ (fun k ω => -f k ω) ≠ ⊤) :
    signedSeries μ f ≠ ⊥ := by
  rw [signedSeries, ← EReal.coe_ennreal_toReal hneg,
    sub_eq_add_neg, ← EReal.coe_neg]
  exact EReal.add_ne_bot_iff.2 ⟨EReal.coe_ennreal_ne_bot _, EReal.coe_ne_bot _⟩

lemma positiveSeries_eq_ofReal_tsum (μ : Measure Ω) (f : ℕ → Ω → ℝ)
    (hfi : ∀ k, Integrable (f k) μ)
    (hf : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ f k ω)
    (hs : Summable (fun k => ∫ ω, f k ω ∂μ)) :
    positiveSeries μ f = ENNReal.ofReal (∑' k, ∫ ω, f k ω ∂μ) := by
  rw [positiveSeries_eq_tsum μ f (fun k => (hfi k).aestronglyMeasurable.aemeasurable)]
  have hk (k : ℕ) : (∫⁻ ω, ENNReal.ofReal (f k ω) ∂μ) =
      ENNReal.ofReal (∫ ω, f k ω ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hfi k) (hf k)).symm
  simp_rw [hk]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun k => integral_nonneg_of_ae (hf k)) hs).symm

lemma positiveSeries_posPart (μ : Measure Ω) (f : ℕ → Ω → ℝ) :
    positiveSeries μ (fun k ω => max (f k ω) 0) = positiveSeries μ f := by
  simp only [positiveSeries, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero]

private lemma ofReal_balance (f g r : ℝ) (hf : 0 ≤ f) (hrel : g = f + r) :
    ENNReal.ofReal g + ENNReal.ofReal (-r) =
      ENNReal.ofReal f + ENNReal.ofReal r + ENNReal.ofReal (-g) := by
  have heq : max g 0 + max (-r) 0 = f + max r 0 + max (-g) 0 := by
    have hg := max_zero_sub_max_neg_zero_eq_self g
    have hr := max_zero_sub_max_neg_zero_eq_self r
    linarith only [hg, hr, hrel]
  have h := congrArg ENNReal.ofReal heq
  rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ENNReal.ofReal_add (add_nonneg hf (le_max_right _ _)) (le_max_right _ _),
    ENNReal.ofReal_add hf (le_max_right _ _)] at h
  simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero] using h

private lemma positiveSeries_balance (μ : Measure Ω) (f g r : ℕ → Ω → ℝ)
    (hf : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ f k ω)
    (hfm : ∀ k, AEMeasurable (f k) μ)
    (hgm : ∀ k, AEMeasurable (g k) μ)
    (hrm : ∀ k, AEMeasurable (r k) μ)
    (hrel : ∀ k, ∀ᵐ ω ∂μ, g k ω = f k ω + r k ω) :
    positiveSeries μ g + positiveSeries μ (fun k ω => -r k ω) =
      positiveSeries μ f + positiveSeries μ r +
        positiveSeries μ (fun k ω => -g k ω) := by
  have hk (k : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (g k ω) ∂μ) +
          (∫⁻ ω, ENNReal.ofReal (-r k ω) ∂μ) =
        (∫⁻ ω, ENNReal.ofReal (f k ω) ∂μ) +
          (∫⁻ ω, ENNReal.ofReal (r k ω) ∂μ) +
          (∫⁻ ω, ENNReal.ofReal (-g k ω) ∂μ) := by
    have hsum : AEMeasurable
        (fun ω => ENNReal.ofReal (f k ω) + ENNReal.ofReal (r k ω)) μ :=
      (hfm k).ennreal_ofReal.add (hrm k).ennreal_ofReal
    rw [← lintegral_add_left' (hgm k).ennreal_ofReal,
      ← lintegral_add_left' (hfm k).ennreal_ofReal,
      ← lintegral_add_left' hsum]
    apply lintegral_congr_ae
    filter_upwards [hf k, hrel k] with ω hω hωrel
    exact ofReal_balance _ _ _ hω hωrel
  rw [positiveSeries_eq_tsum μ g hgm,
    positiveSeries_eq_tsum μ (fun k ω => -r k ω) (fun k => (hrm k).neg),
    positiveSeries_eq_tsum μ f hfm, positiveSeries_eq_tsum μ r hrm,
    positiveSeries_eq_tsum μ (fun k ω => -g k ω) (fun k => (hgm k).neg),
    ← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  exact tsum_congr hk

private lemma ereal_balance_sub (a b : EReal) (p n q : ℝ)
    (h : a + (n : EReal) = b + (p : EReal) + (q : EReal)) :
    a - (q : EReal) = b + ((p - n : ℝ) : EReal) := by
  have hh := congrArg (fun z : EReal => z - (q : EReal) - (n : EReal)) h
  have hleft : (a + (n : EReal)) - (q : EReal) - (n : EReal) =
      a - (q : EReal) := by
    rw [show a + (n : EReal) - (q : EReal) =
        a - (q : EReal) + (n : EReal) by
      simp only [sub_eq_add_neg, add_right_comm], EReal.add_sub_cancel_right]
  rw [hleft, EReal.add_sub_cancel_right] at hh
  have hright : b + (p : EReal) - (n : EReal) = b + ((p - n : ℝ) : EReal) := by
    rw [sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_add]
    simp only [sub_eq_add_neg]
  rw [hright] at hh
  exact hh

lemma summable_integral_of_abs (μ : Measure Ω) (r : ℕ → Ω → ℝ)
    (hrs : Summable (fun k => ∫ ω, |r k ω| ∂μ)) :
    Summable (fun k => ∫ ω, r k ω ∂μ) := by
  apply hrs.of_norm_bounded
  intro k
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (r k) (μ := μ)

/-- Absolute summability of expected corrections permits adding them to a
nonnegative extended total. In particular, the corrected negative-part total
is finite, even when the positive-part total is infinite. -/
lemma signedSeries_correction (μ : Measure Ω) (f g r : ℕ → Ω → ℝ)
    (hf : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ f k ω)
    (hfm : ∀ k, AEMeasurable (f k) μ)
    (hgm : ∀ k, AEMeasurable (g k) μ)
    (hri : ∀ k, Integrable (r k) μ)
    (hrs : Summable (fun k => ∫ ω, |r k ω| ∂μ))
    (hrel : ∀ k, ∀ᵐ ω ∂μ, g k ω = f k ω + r k ω) :
    positiveSeries μ (fun k ω => -g k ω) ≠ ⊤ ∧
      signedSeries μ g = signedSeries μ f +
        ((∑' k, ∫ ω, r k ω ∂μ : ℝ) : EReal) := by
  let rp : ℕ → Ω → ℝ := fun k ω => max (r k ω) 0
  let rn : ℕ → Ω → ℝ := fun k ω => max (-r k ω) 0
  have hrpi (k : ℕ) : Integrable (rp k) μ :=
    (hri k).pos_part
  have hrni (k : ℕ) : Integrable (rn k) μ :=
    (hri k).neg_part
  have hrp0 (k : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ rp k ω :=
    ae_of_all _ (fun _ => le_max_right _ _)
  have hrn0 (k : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ rn k ω :=
    ae_of_all _ (fun _ => le_max_right _ _)
  have hrps : Summable (fun k => ∫ ω, rp k ω ∂μ) := by
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg_of_ae (hrp0 k)) _ hrs
    intro k
    apply integral_mono (hrpi k) (hri k).abs
    intro ω
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hrns : Summable (fun k => ∫ ω, rn k ω ∂μ) := by
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg_of_ae (hrn0 k)) _ hrs
    intro k
    apply integral_mono (hrni k) (hri k).abs
    intro ω
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hpos : positiveSeries μ r =
      ENNReal.ofReal (∑' k, ∫ ω, rp k ω ∂μ) := by
    rw [← positiveSeries_posPart μ r]
    exact positiveSeries_eq_ofReal_tsum μ rp hrpi hrp0 hrps
  have hneg : positiveSeries μ (fun k ω => -r k ω) =
      ENNReal.ofReal (∑' k, ∫ ω, rn k ω ∂μ) := by
    rw [← positiveSeries_posPart μ (fun k ω => -r k ω)]
    exact positiveSeries_eq_ofReal_tsum μ rn hrni hrn0 hrns
  have hpos0 : 0 ≤ ∑' k, ∫ ω, rp k ω ∂μ :=
    tsum_nonneg (fun k => integral_nonneg_of_ae (hrp0 k))
  have hneg0 : 0 ≤ ∑' k, ∫ ω, rn k ω ∂μ :=
    tsum_nonneg (fun k => integral_nonneg_of_ae (hrn0 k))
  have hgneg : positiveSeries μ (fun k ω => -g k ω) ≠ ⊤ := by
    have hrneg : positiveSeries μ (fun k ω => -r k ω) ≠ ⊤ := by
      rw [hneg]
      exact ENNReal.ofReal_ne_top
    apply ne_top_of_le_ne_top hrneg
    apply positiveSeries_mono μ (fun k ω => -g k ω) (fun k ω => -r k ω)
    intro k
    filter_upwards [hf k, hrel k] with ω hω hωrel
    linarith only [hω, hωrel]
  refine ⟨hgneg, ?_⟩
  have hcorr : (∑' k, ∫ ω, rp k ω ∂μ) - (∑' k, ∫ ω, rn k ω ∂μ) =
      ∑' k, ∫ ω, r k ω ∂μ := by
    rw [← hrps.tsum_sub hrns]
    apply tsum_congr
    intro k
    rw [← integral_sub (hrpi k) (hrni k)]
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => max_zero_sub_max_neg_zero_eq_self (r k ω))
  have hbalance := congrArg (fun x : ENNReal => (x : EReal))
    (positiveSeries_balance μ f g r hf hfm hgm
      (fun k => (hri k).aestronglyMeasurable.aemeasurable) hrel)
  simp only [EReal.coe_ennreal_add] at hbalance
  rw [hpos, hneg, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
    max_eq_left hpos0, max_eq_left hneg0,
    ← EReal.coe_ennreal_toReal hgneg] at hbalance
  rw [signedSeries, ← EReal.coe_ennreal_toReal hgneg,
    signedSeries_of_nonneg μ f hf]
  exact (ereal_balance_sub _ _ _ _ _ hbalance).trans (by rw [hcorr])

/-- A bound on the finite expected correction gives an extended-total bound. -/
lemma signedSeries_le_of_correction (μ : Measure Ω) (f g r : ℕ → Ω → ℝ)
    (hf : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ f k ω)
    (hfm : ∀ k, AEMeasurable (f k) μ)
    (hgm : ∀ k, AEMeasurable (g k) μ)
    (hri : ∀ k, Integrable (r k) μ)
    (hrs : Summable (fun k => ∫ ω, |r k ω| ∂μ))
    (hrel : ∀ k, ∀ᵐ ω ∂μ, g k ω = f k ω + r k ω)
    (c : ℝ) (hc : (∑' k, ∫ ω, r k ω ∂μ) ≤ c) :
    signedSeries μ g ≤ signedSeries μ f + (c : EReal) := by
  rw [(signedSeries_correction μ f g r hf hfm hgm hri hrs hrel).2]
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hc)

lemma discCost_eq_signedSeries {S A : Type*} (sys : ControlSystem S A)
    (α : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (π : Policy A) (s₀ : S) :
    sys.discCost α ν π s₀ = signedSeries (Measure.infinitePi fun _ : ℕ => ν)
      (fun k ω => α ^ k * sys.cost (sys.traj π s₀ ω k) (π k ω)) := rfl

end FZEchelon.Discounted.Accounting

/- Inlined source: FollowComparison. -/

open MeasureTheory Filter Topology
open FZEchelon.Discounted.Accounting

namespace FZEchelon.Discounted

variable (M : Model)

/-- For an arbitrary admissible order stream, replacing only its shipments by
the critical capped shipments weakly reduces the full discounted system cost. -/
lemma follow_discCost_le (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (π : Policy (ℝ × ℝ)) (s : M.State) (hs : M.InDomain s)
    (hπ : M.system.Admissible π s) :
    M.system.discCost M.α M.ν (followOrders M (projectOrders π) xstar s) s ≤
      M.system.discCost M.α M.ν π s := by
  have hd := projectOrders_admissible M xstar π s hπ
  have hn : ∀ n ω, 0 ≤ projectOrders π n ω := fun n ω => hd.2.2 ω n
  have hfollow := followOrders_admissible M (projectOrders π) xstar s hd.1 hd.2.1 hn hs
  change signedSeries (pathMeasure M)
    (systemStage M (followOrders M (projectOrders π) xstar s) s) ≤
      signedSeries (pathMeasure M) (systemStage M π s)
  rw [signedSeries_of_nonneg _ _ (fun k => ae_of_all _
      (systemStage_nonneg M hM hcost _ _ hfollow k)),
    signedSeries_of_nonneg _ _ (fun k => ae_of_all _
      (systemStage_nonneg M hM hcost _ _ hπ k)),
    EReal.coe_ennreal_le_coe_ennreal_iff]
  apply lintegral_series_le_of_partial_le (pathMeasure M)
    (systemStage M π s) (systemStage M (followOrders M (projectOrders π) xstar s) s)
    (terminalError M.α M.cr (max xstar s.2.2 - s.2.2))
  · intro k
    exact ae_of_all _ (systemStage_nonneg M hM hcost _ _ hπ k)
  · intro k
    exact ae_of_all _ (systemStage_nonneg M hM hcost _ _ hfollow k)
  · intro k
    exact (systemStage_measurable M hM _ s hfollow.1 k).aemeasurable
  · intro n
    exact terminalError_integrable M hM _ _ _ n
  · intro n
    filter_upwards [path_nonneg M hM] with ω hω
    exact mul_nonneg (mul_nonneg hM.cr_pos.le (pow_nonneg hM.α_nonneg n))
      (add_nonneg (sub_nonneg.mpr (le_max_right _ _)) (demandPrefix_nonneg n ω hω))
  · exact terminalError_integral_tendsto_zero M hM hα _ _
  · intro n
    filter_upwards [path_nonneg M hM] with ω hω
    exact followPartial_le M hM xstar hx π s hπ hs ω hω n

end FZEchelon.Discounted

/- Inlined source: CorrectionBounds. -/

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

variable (M : Model)

/-- The correction from a capped-shipment system's nonnegative stage costs to
its depot stage costs. Unlike either stage cost, this has an order-independent
integrable bound. -/
noncomputable def cappedCorrection (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  depotStage M xstar πd (s.1, s.2.1) n ω -
    systemStage M (followOrders M πd xstar s) s n ω

lemma cappedCorrection_measurable (hM : M.StandingAssumptions) (πd : Policy ℝ)
    (xstar : ℝ) (s : M.State) (hm : ∀ n, Measurable (πd n)) (n : ℕ) :
    Measurable (cappedCorrection M πd xstar s n) := by
  apply (depotStage_measurable M hM xstar πd (s.1, s.2.1) hm n).sub
  apply systemStage_measurable M hM
  intro k
  exact follow_action_measurable M xstar _ _ (followTraj_measurable M πd xstar s hm k) (hm k)

lemma cappedCorrection_eq (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (hnn : ∀ n ω, 0 ≤ πd n ω) (hs : M.InDomain s)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    cappedCorrection M πd xstar s n ω = -M.α ^ n *
      (stationaryObjective M xstar +
        M.cr * (M.α * ((followTraj M πd xstar s ω n).2.2 +
          (followOrders M πd xstar s n ω).2) - (followTraj M πd xstar s ω n).2.2) +
        convexGapExcess (stationaryObjective M) xstar (unservedStock s.2.2 ω n)) := by
  have hg := follow_pathGap M πd xstar s hnn hs ω hω n
  have hd := one_step_decomposition M xstar
    (M.system.traj (followOrders M πd xstar s) s ω n) (followOrders M πd xstar s n ω)
  have hp := projectOrders_traj M xstar (followOrders M πd xstar s) s ω n
  rw [projectOrders_follow] at hp
  simp only [followOrders_traj] at hp hd hg
  change _ = _ + _ + _ + stageGap M xstar (followTraj M πd xstar s ω n)
    (followOrders M πd xstar s n ω) at hd
  rw [hg] at hd
  have hfirst : (followOrders M πd xstar s n ω).1 = πd n ω := rfl
  rw [hfirst] at hd
  unfold cappedCorrection depotStage systemStage
  rw [followOrders_traj, hp]
  change M.α ^ n * (M.depotSystem xstar).cost
    ((followTraj M πd xstar s ω n).1, (followTraj M πd xstar s ω n).2.1) (πd n ω) -
      M.α ^ n * M.system.cost (followTraj M πd xstar s ω n)
        (followOrders M πd xstar s n ω) = _
  rw [hd]
  ring

lemma follow_stock_abs_le (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    |(followTraj M πd xstar s ω n).2.2| ≤ |xstar| + |s.2.2| + demandPrefix n ω := by
  have hlo := follow_stock_lower M πd xstar s ω n
  have hup := follow_stock_uniform_upper M πd xstar s ω hω n
  have hdn := demandPrefix_nonneg n ω hω
  have hmax : max xstar s.2.2 ≤ |xstar| + |s.2.2| :=
    max_le (by linarith [le_abs_self xstar, abs_nonneg s.2.2])
      (by linarith [le_abs_self s.2.2, abs_nonneg xstar])
  dsimp only [unservedStock] at hlo
  change s.2.2 - demandPrefix n ω ≤ _ at hlo
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le s.2.2, abs_nonneg xstar]
  · linarith

lemma follow_post_abs_le (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    |(followTraj M πd xstar s ω n).2.2 + (followOrders M πd xstar s n ω).2| ≤
      |xstar| + |s.2.2| + demandPrefix n ω := by
  have hx := follow_stock_abs_le M πd xstar s ω hω n
  have hup := follow_stock_uniform_upper M πd xstar s ω hω n
  have hcap := capped_post_le xstar (followTraj M πd xstar s ω n).2.2
    ((followTraj M πd xstar s ω n).2.1 + M.arrival (followTraj M πd xstar s ω n).1 (πd n ω))
  have hmax : max xstar s.2.2 ≤ |xstar| + |s.2.2| :=
    max_le (by linarith [le_abs_self xstar, abs_nonneg s.2.2])
      (by linarith [le_abs_self s.2.2, abs_nonneg xstar])
  have hz : 0 ≤ (followOrders M πd xstar s n ω).2 := le_max_left _ _
  have hh : max xstar (followTraj M πd xstar s ω n).2.2 ≤ max xstar s.2.2 :=
    max_le (le_max_left _ _) hup
  apply abs_le.mpr
  constructor
  · linarith [(abs_le.mp hx).1]
  · change (followTraj M πd xstar s ω n).2.2 +
      max 0 (min xstar ((followTraj M πd xstar s ω n).2.1 +
        M.arrival (followTraj M πd xstar s ω n).1 (πd n ω)) -
          (followTraj M πd xstar s ω n).2.2) ≤ _
    linarith [demandPrefix_nonneg n ω hω]

lemma baseline_excess_bounds (hM : M.StandingAssumptions) (xstar x : ℝ)
    (hx : M.IsStationaryCriticalNumber xstar) (ω : ℕ → ℝ)
    (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    0 ≤ convexGapExcess (stationaryObjective M) xstar (unservedStock x ω n) ∧
      convexGapExcess (stationaryObjective M) xstar (unservedStock x ω n) ≤
        convexGapExcess (stationaryObjective M) xstar x := by
  constructor
  · exact convexGapExcess_nonneg _ _ _ (stationaryObjective_min M xstar hx)
  · apply convexGapExcess_monotone _ _ (stationaryObjective_convex M hM)
      (stationaryObjective_min M xstar hx)
    exact sub_le_self _ (demandPrefix_nonneg n ω hω)

noncomputable def correctionA (xstar x : ℝ) : ℝ :=
  |stationaryObjective M xstar| + M.cr * (M.α + 1) * (|xstar| + |x|) +
    convexGapExcess (stationaryObjective M) xstar x

noncomputable def correctionB : ℝ := M.cr * (M.α + 1)

lemma cappedCorrection_abs_le (hM : M.StandingAssumptions) (πd : Policy ℝ)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar) (s : M.State)
    (hnn : ∀ n ω, 0 ≤ πd n ω) (hs : M.InDomain s)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    |cappedCorrection M πd xstar s n ω| ≤
      demandEnvelope M.α (correctionA M xstar s.2.2) (correctionB M) n ω := by
  let B := |xstar| + |s.2.2| + demandPrefix n ω
  have hb : 0 ≤ B := add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (demandPrefix_nonneg n ω hω)
  have hxabs := follow_stock_abs_le M πd xstar s ω hω n
  have huabs := follow_post_abs_le M πd xstar s ω hω n
  have he := baseline_excess_bounds M hM xstar s.2.2 hx ω hω n
  have hterm : |M.α * ((followTraj M πd xstar s ω n).2.2 +
      (followOrders M πd xstar s n ω).2) - (followTraj M πd xstar s ω n).2.2| ≤
        (M.α + 1) * B := by
    calc
      _ ≤ |M.α * ((followTraj M πd xstar s ω n).2.2 +
          (followOrders M πd xstar s n ω).2)| + |(followTraj M πd xstar s ω n).2.2| :=
        abs_sub _ _
      _ = M.α * |(followTraj M πd xstar s ω n).2.2 +
          (followOrders M πd xstar s n ω).2| + |(followTraj M πd xstar s ω n).2.2| := by
        rw [abs_mul, abs_of_nonneg hM.α_nonneg]
      _ ≤ M.α * B + B := add_le_add (mul_le_mul_of_nonneg_left huabs hM.α_nonneg) hxabs
      _ = _ := by ring
  rw [cappedCorrection_eq M πd xstar s hnn hs ω hω n, abs_mul,
    abs_neg, abs_of_nonneg (pow_nonneg hM.α_nonneg n)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hM.α_nonneg n)
  calc
    _ ≤ |stationaryObjective M xstar| +
        |M.cr * (M.α * ((followTraj M πd xstar s ω n).2.2 +
          (followOrders M πd xstar s n ω).2) - (followTraj M πd xstar s ω n).2.2)| +
        |convexGapExcess (stationaryObjective M) xstar (unservedStock s.2.2 ω n)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |stationaryObjective M xstar| + M.cr * ((M.α + 1) * B) +
        convexGapExcess (stationaryObjective M) xstar s.2.2 := by
      rw [abs_mul, abs_of_nonneg hM.cr_pos.le, abs_of_nonneg he.1]
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hterm hM.cr_pos.le)) he.2
    _ = _ := by unfold correctionA correctionB B; ring

lemma cappedCorrection_integrable (hM : M.StandingAssumptions) (πd : Policy ℝ)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar) (s : M.State)
    (hm : ∀ n, Measurable (πd n)) (hnn : ∀ n ω, 0 ≤ πd n ω)
    (hs : M.InDomain s) (n : ℕ) :
    Integrable (cappedCorrection M πd xstar s n) (pathMeasure M) := by
  apply (demandEnvelope_integrable M hM M.α (correctionA M xstar s.2.2) (correctionB M) n).mono'
    (cappedCorrection_measurable M hM πd xstar s hm n).aestronglyMeasurable
  filter_upwards [path_nonneg M hM] with ω hω
  simpa only [Real.norm_eq_abs] using cappedCorrection_abs_le M hM πd xstar hx s hnn hs ω hω n

lemma cappedCorrection_abs_summable (hM : M.StandingAssumptions) (hα : M.α < 1)
    (πd : Policy ℝ) (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar) (s : M.State)
    (hm : ∀ n, Measurable (πd n)) (hnn : ∀ n ω, 0 ≤ πd n ω) (hs : M.InDomain s) :
    Summable (fun n => ∫ ω, |cappedCorrection M πd xstar s n ω| ∂pathMeasure M) := by
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => abs_nonneg _))
    (fun n => ?_) (demandEnvelope_integral_summable M hM hα
      (correctionA M xstar s.2.2) (correctionB M))
  apply integral_mono_ae (cappedCorrection_integrable M hM πd xstar hx s hm hnn hs n).abs
    (demandEnvelope_integrable M hM _ _ _ n)
  filter_upwards [path_nonneg M hM] with ω hω
  exact cappedCorrection_abs_le M hM πd xstar hx s hnn hs ω hω n

end FZEchelon.Discounted

/- Inlined source: CorrectionLimit. -/

open MeasureTheory Filter Topology
open FZEchelon.Discounted.Accounting

namespace FZEchelon.Discounted

variable (M : Model)

noncomputable def correctionTotal (πd : Policy ℝ) (xstar : ℝ) (s : M.State) : ℝ :=
  ∑' n, ∫ ω, cappedCorrection M πd xstar s n ω ∂pathMeasure M

lemma cappedCorrection_sum (πd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (hnn : ∀ n ω, 0 ≤ πd n ω) (hs : M.InDomain s)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    (∑ k ∈ Finset.range n, cappedCorrection M πd xstar s k ω) =
      -commonPartial M xstar s.2.2 ω n -
        M.cr * M.α ^ n * (followTraj M πd xstar s ω n).2.2 := by
  have h := followPartial_decomposition M πd xstar s hnn hs ω hω n
  simp only [cappedCorrection, Finset.sum_sub_distrib]
  change depotPartial M xstar πd (s.1, s.2.1) ω n -
    systemPartial M (followOrders M πd xstar s) s ω n = _
  linarith

lemma cappedCorrection_sum_diff_abs_le (hM : M.StandingAssumptions)
    (πd τd : Policy ℝ) (xstar : ℝ) (s : M.State)
    (hπ : ∀ n ω, 0 ≤ πd n ω) (hτ : ∀ n ω, 0 ≤ τd n ω) (hs : M.InDomain s)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) (n : ℕ) :
    |(∑ k ∈ Finset.range n, cappedCorrection M πd xstar s k ω) -
      (∑ k ∈ Finset.range n, cappedCorrection M τd xstar s k ω)| ≤
        terminalError M.α (2 * M.cr) (|xstar| + |s.2.2|) n ω := by
  rw [cappedCorrection_sum M πd xstar s hπ hs ω hω n,
    cappedCorrection_sum M τd xstar s hτ hs ω hω n]
  have heq : (-commonPartial M xstar s.2.2 ω n -
      M.cr * M.α ^ n * (followTraj M πd xstar s ω n).2.2) -
        (-commonPartial M xstar s.2.2 ω n -
          M.cr * M.α ^ n * (followTraj M τd xstar s ω n).2.2) =
      M.cr * M.α ^ n * ((followTraj M τd xstar s ω n).2.2 -
        (followTraj M πd xstar s ω n).2.2) := by ring
  rw [heq, abs_mul, abs_of_nonneg (mul_nonneg hM.cr_pos.le (pow_nonneg hM.α_nonneg n))]
  have hdiff := (abs_sub (followTraj M τd xstar s ω n).2.2
    (followTraj M πd xstar s ω n).2.2).trans
      (add_le_add (follow_stock_abs_le M τd xstar s ω hω n)
        (follow_stock_abs_le M πd xstar s ω hω n))
  calc
    _ ≤ M.cr * M.α ^ n *
        ((|xstar| + |s.2.2| + demandPrefix n ω) +
          (|xstar| + |s.2.2| + demandPrefix n ω)) :=
      mul_le_mul_of_nonneg_left hdiff (mul_nonneg hM.cr_pos.le (pow_nonneg hM.α_nonneg n))
    _ = _ := by unfold terminalError; ring

/-- Capped policies have the same total expected depot-to-system correction,
even when their depot and system positive totals are infinite. -/
lemma correctionTotal_eq (hM : M.StandingAssumptions) (hα : M.α < 1)
    (πd τd : Policy ℝ) (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (s : M.State) (hs : M.InDomain s)
    (hπm : ∀ n, Measurable (πd n)) (hτm : ∀ n, Measurable (τd n))
    (hπ : ∀ n ω, 0 ≤ πd n ω) (hτ : ∀ n ω, 0 ≤ τd n ω) :
    correctionTotal M πd xstar s = correctionTotal M τd xstar s := by
  let p := cappedCorrection M πd xstar s
  let q := cappedCorrection M τd xstar s
  have hpi (n : ℕ) : Integrable (p n) (pathMeasure M) :=
    cappedCorrection_integrable M hM πd xstar hx s hπm hπ hs n
  have hqi (n : ℕ) : Integrable (q n) (pathMeasure M) :=
    cappedCorrection_integrable M hM τd xstar hx s hτm hτ hs n
  have hps := summable_integral_of_abs (pathMeasure M) p
    (cappedCorrection_abs_summable M hM hα πd xstar hx s hπm hπ hs)
  have hqs := summable_integral_of_abs (pathMeasure M) q
    (cappedCorrection_abs_summable M hM hα τd xstar hx s hτm hτ hs)
  have hcomm (n : ℕ) :
      (∑ k ∈ Finset.range n, ∫ ω, p k ω ∂pathMeasure M) -
        (∑ k ∈ Finset.range n, ∫ ω, q k ω ∂pathMeasure M) =
      ∫ ω, (∑ k ∈ Finset.range n, p k ω) - (∑ k ∈ Finset.range n, q k ω)
        ∂pathMeasure M := by
    rw [integral_sub (integrable_finsetSum _ (fun k _ => hpi k))
      (integrable_finsetSum _ (fun k _ => hqi k)),
      integral_finsetSum _ (fun k _ => hpi k), integral_finsetSum _ (fun k _ => hqi k)]
  have hbound (n : ℕ) :
      ‖(∑ k ∈ Finset.range n, ∫ ω, p k ω ∂pathMeasure M) -
        (∑ k ∈ Finset.range n, ∫ ω, q k ω ∂pathMeasure M)‖ ≤
      ∫ ω, terminalError M.α (2 * M.cr) (|xstar| + |s.2.2|) n ω ∂pathMeasure M := by
    rw [hcomm]
    apply norm_integral_le_of_norm_le (terminalError_integrable M hM _ _ _ n)
    filter_upwards [path_nonneg M hM] with ω hω
    exact cappedCorrection_sum_diff_abs_le M hM πd τd xstar s hπ hτ hs ω hω n
  have hz := squeeze_zero_norm hbound
    (terminalError_integral_tendsto_zero M hM hα (2 * M.cr) (|xstar| + |s.2.2|))
  exact sub_eq_zero.mp (tendsto_nhds_unique
    (hps.hasSum.tendsto_sum_nat.sub hqs.hasSum.tendsto_sum_nat) hz)

lemma depot_discCost_eq_capped_add (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (πd : Policy ℝ) (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (s : M.State) (hs : M.InDomain s)
    (hπ : (M.depotSystem xstar).Admissible πd (s.1, s.2.1)) :
    (M.depotSystem xstar).discCost M.α M.ν πd (s.1, s.2.1) =
      M.system.discCost M.α M.ν (followOrders M πd xstar s) s +
        (correctionTotal M πd xstar s : EReal) := by
  have hn : ∀ n ω, 0 ≤ πd n ω := fun n ω => hπ.2.2 ω n
  have hf := followOrders_admissible M πd xstar s hπ.1 hπ.2.1 hn hs
  change signedSeries (pathMeasure M) (depotStage M xstar πd (s.1, s.2.1)) =
    signedSeries (pathMeasure M) (systemStage M (followOrders M πd xstar s) s) + _
  exact (signedSeries_correction (pathMeasure M)
    (systemStage M (followOrders M πd xstar s) s)
    (depotStage M xstar πd (s.1, s.2.1)) (cappedCorrection M πd xstar s)
    (fun n => ae_of_all _ (systemStage_nonneg M hM hcost _ _ hf n))
    (fun n => (systemStage_measurable M hM _ s hf.1 n).aemeasurable)
    (fun n => (depotStage_measurable M hM xstar πd (s.1, s.2.1) hπ.1 n).aemeasurable)
    (cappedCorrection_integrable M hM πd xstar hx s hπ.1 hn hs)
    (cappedCorrection_abs_summable M hM hα πd xstar hx s hπ.1 hn hs)
    (fun n => ae_of_all _ (fun ω => by unfold cappedCorrection; ring))).2

lemma capped_discCost_le_of_depot (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (πd τd : Policy ℝ) (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (s : M.State) (hs : M.InDomain s)
    (hπ : (M.depotSystem xstar).Admissible πd (s.1, s.2.1))
    (hτ : (M.depotSystem xstar).Admissible τd (s.1, s.2.1))
    (hle : (M.depotSystem xstar).discCost M.α M.ν πd (s.1, s.2.1) ≤
      (M.depotSystem xstar).discCost M.α M.ν τd (s.1, s.2.1)) :
    M.system.discCost M.α M.ν (followOrders M πd xstar s) s ≤
      M.system.discCost M.α M.ν (followOrders M τd xstar s) s := by
  rw [depot_discCost_eq_capped_add M hM hα hcost πd xstar hx s hs hπ,
    depot_discCost_eq_capped_add M hM hα hcost τd xstar hx s hs hτ,
    correctionTotal_eq M hM hα πd τd xstar hx s hs hπ.1 hτ.1
      (fun n ω => hπ.2.2 ω n) (fun n ω => hτ.2.2 ω n)] at hle
  exact (EReal.addLECancellable_coe (correctionTotal M τd xstar s)).add_le_add_iff_right.mp hle

end FZEchelon.Discounted

/- Inlined source: Root. -/

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

lemma discounted_policy_optimal (M : Model) (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (σd : M.DepotState → ℝ) (hσm : Measurable σd) (hσnn : ∀ p, 0 ≤ σd p)
    (hσopt : ∀ p : M.DepotState, (∀ k, 0 ≤ p.1 k) → ∀ πd : Policy ℝ,
      (M.depotSystem xstar).Admissible πd p →
      (M.depotSystem xstar).discCost M.α M.ν ((M.depotSystem xstar).stationary σd p) p ≤
        (M.depotSystem xstar).discCost M.α M.ν πd p) :
    Measurable (M.piStar σd xstar) ∧
    ∀ s : M.State, M.InDomain s →
      M.system.Admissible (M.system.stationary (M.piStar σd xstar) s) s ∧
      ∀ π : Policy (ℝ × ℝ), M.system.Admissible π s →
        M.system.discCost M.α M.ν (M.system.stationary (M.piStar σd xstar) s) s ≤
          M.system.discCost M.α M.ν π s := by
  refine ⟨piStar_measurable M σd xstar hσm, ?_⟩
  intro s hs
  refine ⟨piStar_admissible M σd xstar hσm hσnn s hs, ?_⟩
  intro π hπ
  have hp := projectOrders_admissible M xstar π s hπ
  have hd := depot_stationary_admissible M σd hσm hσnn xstar (s.1, s.2.1)
  have hdepot := hσopt (s.1, s.2.1) hs.1 (projectOrders π) hp
  have hcap := capped_discCost_le_of_depot M hM hα hcost
    ((M.depotSystem xstar).stationary σd (s.1, s.2.1)) (projectOrders π)
    xstar hx s hs hd hp hdepot
  rw [followOrders_stationary M σd xstar s] at hcap
  exact hcap.trans (follow_discCost_le M hM hα hcost xstar hx π s hs hπ)

end FZEchelon.Discounted

open FZEchelon.Discounted

/-- Theorem 1, p. 827: the policy `π_α*` (orders by an optimal stationary policy `σd` of the depot
problem `IH_α^d`, shipments up to `x^{r*}` as far as depot stock allows) is a measurable stationary
policy, admissible from every physical state, and optimal for `IH_α`: its expected discounted cost
is at most that of every admissible policy, from every physical state. -/
theorem solution (M : Model) (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (σd : M.DepotState → ℝ) (hσm : Measurable σd) (hσnn : ∀ p, 0 ≤ σd p)
    (hσopt : ∀ p : M.DepotState, (∀ k, 0 ≤ p.1 k) → ∀ πd : Policy ℝ,
      (M.depotSystem xstar).Admissible πd p →
      (M.depotSystem xstar).discCost M.α M.ν ((M.depotSystem xstar).stationary σd p) p ≤
        (M.depotSystem xstar).discCost M.α M.ν πd p) :
    Measurable (M.piStar σd xstar) ∧
      ∀ s : M.State, M.InDomain s →
        M.system.Admissible (M.system.stationary (M.piStar σd xstar) s) s ∧
        ∀ π : Policy (ℝ × ℝ), M.system.Admissible π s →
          M.system.discCost M.α M.ν (M.system.stationary (M.piStar σd xstar) s) s ≤
            M.system.discCost M.α M.ν π s := by
  exact FZEchelon.Discounted.discounted_policy_optimal M hM hα hcost xstar hx σd hσm hσnn hσopt
