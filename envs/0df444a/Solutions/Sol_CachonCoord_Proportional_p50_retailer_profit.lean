-- Prove2me | solution 1 for CachonCoord.Proportional.p50_retailer_profit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:50:23.727003+00:00
-- url     : https://prove2.me/submissions/f0843250-15fd-454f-bc56-32352e21b0a0

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

open MeasureTheory ProbabilityTheory Filter Topology

namespace CachonCoord.Proportional

namespace Model

variable (M : Model)

lemma cpF_nonneg (y : ℝ) : 0 ≤ M.F y := by
  haveI := M.isProb; exact cdf_nonneg _ _

lemma cpF_le_one (y : ℝ) : M.F y ≤ 1 := by
  haveI := M.isProb; exact cdf_le_one _ _

lemma cpF_mono : Monotone M.F := monotone_cdf _

lemma cpF_zero : M.F 0 = 0 := M.cdf_zero

lemma cpF_nonpos (y : ℝ) (hy : y ≤ 0) : M.F y = 0 :=
  le_antisymm (by have := M.cpF_mono hy; rwa [M.cpF_zero] at this) (M.cpF_nonneg y)

lemma cpF_strict {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : M.F x < M.F y :=
  M.strictMonoOn_cdf (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (by linarith)) hxy

lemma cpF_lt_one (y : ℝ) (hy : 0 ≤ y) : M.F y < 1 :=
  lt_of_lt_of_le (M.cpF_strict hy (lt_add_one y)) (M.cpF_le_one _)

lemma cpF_pos (y : ℝ) (hy : 0 < y) : 0 < M.F y := by
  have := M.cpF_strict le_rfl hy; rwa [M.cpF_zero] at this

lemma cpF_cont : Continuous M.F := by
  rw [continuous_iff_continuousAt]; intro y
  rcases lt_trichotomy y 0 with h | h | h
  · have : M.F =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds h] with z hz; exact M.cpF_nonpos z (le_of_lt hz)
    exact (continuousAt_const).congr this.symm
  · subst h
    have hr : ContinuousWithinAt M.F (Set.Ici 0) 0 := (cdf M.law).right_continuous 0
    have hl : ContinuousWithinAt M.F (Set.Iic 0) 0 := by
      apply (continuousWithinAt_const (b := (0:ℝ))).congr
      · intro z hz; exact M.cpF_nonpos z hz
      · exact M.cpF_nonpos 0 le_rfl
    exact continuousAt_iff_continuous_left_right.2 ⟨hl, hr⟩
  · exact (M.hasDerivAt_cdf y h).continuousAt

lemma cpF_tendsto_top : Tendsto M.F atTop (𝓝 1) := by
  haveI := M.isProb; exact tendsto_cdf_atTop M.law

lemma density_nonneg (y : ℝ) (hy : 0 < y) : 0 ≤ M.density y :=
  (M.hasDerivAt_cdf y hy).nonneg_of_monotone (monotone_cdf _)

/-- `G(q) = ∫_0^q F`. -/
noncomputable def cpG (q : ℝ) : ℝ := ∫ x in (0:ℝ)..q, M.F x

lemma cpG_deriv (q : ℝ) : HasDerivAt M.cpG (M.F q) q :=
  (M.cpF_cont.integral_hasStrictDerivAt 0 q).hasDerivAt

lemma cpG_cont : Continuous M.cpG :=
  continuous_iff_continuousAt.2 fun q => (M.cpG_deriv q).continuousAt

lemma cpG_zero : M.cpG 0 = 0 := by simp [cpG]

lemma avgF_eq (q : ℝ) : M.avgF q = M.cpG q / q := by
  simp only [avgF, cpG]; ring

lemma cpG_lt (q : ℝ) (hq : 0 < q) : M.cpG q < q * M.F q := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := M.F) (g := fun _ => M.F q) hq M.cpF_cont.continuousOn continuousOn_const
    (fun x hx => M.cpF_mono hx.2) ⟨0, ⟨le_rfl, hq.le⟩, by rw [M.cpF_zero]; exact M.cpF_pos q hq⟩
  simpa [cpG, mul_comm] using h

lemma cpG_pos (q : ℝ) (hq : 0 < q) : 0 < M.cpG q := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ => (0:ℝ)) (g := M.F) hq continuousOn_const M.cpF_cont.continuousOn
    (fun x _ => M.cpF_nonneg x) ⟨q, ⟨hq.le, le_rfl⟩, M.cpF_pos q hq⟩
  simpa [cpG] using h

lemma cpG_nonneg (q : ℝ) (hq : 0 ≤ q) : 0 ≤ M.cpG q := by
  rcases eq_or_lt_of_le hq with h | h
  · rw [← h, M.cpG_zero]
  · exact (M.cpG_pos q h).le

lemma avg_lt_F (q : ℝ) (hq : 0 < q) : M.cpG q / q < M.F q := by
  rw [div_lt_iff₀ hq]; linarith [M.cpG_lt q hq]

lemma avg_nonneg (q : ℝ) (hq : 0 < q) : 0 ≤ M.cpG q / q :=
  div_nonneg (M.cpG_nonneg q hq.le) hq.le

lemma cp_ae_nonneg : ∀ᵐ d ∂M.law, 0 ≤ d := by
  rw [ae_iff]; simp only [not_le]; exact M.nonneg

lemma cp_I_eq (x : ℝ) : M.I x = M.cpG x := by
  haveI := M.isProb
  unfold I cpG
  rcases le_or_gt 0 x with hx | hx
  · have hint : Integrable (fun d => max (x - d) 0) M.law := by
      refine Integrable.mono' (integrable_const x) ?_ ?_
      · exact (by fun_prop : Continuous fun d : ℝ => max (x-d) 0).aestronglyMeasurable
      · filter_upwards [M.cp_ae_nonneg] with d hd
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) hx
    rw [hint.integral_eq_integral_Ioc_meas_le (M := x)
      (Filter.Eventually.of_forall fun d => le_max_right _ _)]
    · have h2 : ∫ t in Set.Ioc 0 x, M.law.real {a | t ≤ max (x - a) 0}
          = ∫ t in Set.Ioc 0 x, M.F (x - t) := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
        have : {a : ℝ | t ≤ max (x - a) 0} = Set.Iic (x - t) := by
          ext a; simp only [Set.mem_setOf_eq, Set.mem_Iic]
          constructor
          · intro h; rcases le_max_iff.mp h with h | h
            · linarith
            · linarith [ht.1]
          · intro h; exact le_max_of_le_left (by linarith)
        rw [this]; simp only [F]; rw [cdf_eq_real]
      rw [h2, ← intervalIntegral.integral_of_le hx, intervalIntegral.integral_comp_sub_left]
      simp
    · filter_upwards [M.cp_ae_nonneg] with d hd
      exact max_le (by linarith) hx
  · have h1 : ∫ d, max (x - d) 0 ∂M.law = 0 := by
      rw [integral_congr_ae (g := fun _ => (0:ℝ))]
      · simp
      filter_upwards [M.cp_ae_nonneg] with d hd
      exact max_eq_right (by linarith)
    have h2 : ∫ y in (0:ℝ)..x, M.F y = ∫ y in (0:ℝ)..x, (0:ℝ) := by
      refine intervalIntegral.integral_congr ?_
      intro y hy
      rw [Set.uIcc_of_ge hx.le] at hy
      exact M.cpF_nonpos y (by linarith [hy.2])
    rw [h1, h2]; simp

lemma cp_int_min (q : ℝ) : Integrable (fun d => min q d) M.law := by
  haveI := M.isProb
  refine Integrable.mono' ((integrable_const |q|).add M.integrable.norm) ?_ ?_
  · exact (by fun_prop : Continuous fun d : ℝ => min q d).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun d => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rcases le_total q d with h | h
    · rw [min_eq_left h]; linarith [abs_nonneg d, le_abs_self q, neg_abs_le q, le_abs_self d, neg_abs_le d]
    · rw [min_eq_right h]; linarith [abs_nonneg q, le_abs_self q, neg_abs_le q, le_abs_self d, neg_abs_le d]

lemma cp_int_max (q : ℝ) : Integrable (fun d => max (q - d) 0) M.law := by
  haveI := M.isProb
  have : (fun d => max (q - d) 0) = fun d => q - min q d := by
    funext d; rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]
  rw [this]; exact (integrable_const q).sub (M.cp_int_min q)

lemma cp_S_eq (q : ℝ) : M.S q = q - M.cpG q := by
  haveI := M.isProb
  rw [← M.cp_I_eq]
  unfold S I
  have : (fun d => min q d) = fun d => q - max (q - d) 0 := by
    funext d; rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [this, integral_sub (integrable_const q) (M.cp_int_max q)]
  simp

lemma chain_eq (q : ℝ) : M.chainProfit q = M.p * (q - M.cpG q) - M.c * q := by
  rw [chainProfit, M.cp_S_eq]

/-- p. 50 formula for the retailer profit. -/
lemma rp_eq (w b x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    M.retailerProfit w b x s =
      (M.p - w) * x - (M.p - b) * (x / (x + s)) * M.cpG (x + s) := by
  haveI := M.isProb
  rcases eq_or_lt_of_le (add_nonneg hx hs) with h | h
  · have hx0 : x = 0 := by linarith
    have hs0 : s = 0 := by linarith
    subst hx0 hs0; simp [retailerProfit]
  · have ht : 0 ≤ x / (x + s) := div_nonneg hx h.le
    have hxq : x / (x + s) * (x + s) = x := div_mul_cancel₀ x h.ne'
    have hfun : (fun d => M.p * min x (x / (x + s) * d) + b * max (x - x / (x + s) * d) 0 - w * x)
        = fun d => x / (x + s) * (M.p * min (x + s) d + b * max ((x + s) - d) 0) - w * x := by
      funext d
      have e1 : min x (x / (x + s) * d) = x / (x + s) * min (x + s) d := by
        rw [mul_min_of_nonneg _ _ ht, hxq]
      have e2 : max (x - x / (x + s) * d) 0 = x / (x + s) * max ((x + s) - d) 0 := by
        rw [mul_max_of_nonneg _ _ ht, mul_zero, mul_sub, hxq]
      rw [e1, e2]; ring
    unfold retailerProfit
    rw [hfun, integral_sub, integral_const_mul, integral_add, integral_const_mul,
      integral_const_mul]
    · have hS := M.cp_S_eq (x + s)
      have hI := M.cp_I_eq (x + s)
      unfold S at hS; unfold I at hI
      rw [hS, hI]; simp
      linear_combination M.p * hxq
    · exact (M.cp_int_min _).const_mul _
    · exact (M.cp_int_max _).const_mul _
    · exact (((M.cp_int_min _).const_mul _).add ((M.cp_int_max _).const_mul _)).const_mul _
    · exact integrable_const _

theorem p50_core (w b x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    M.retailerProfit w b x s =
      (M.p - w) * x - (M.p - b) * (x / (x + s)) * ∫ y in (0 : ℝ)..(x + s), M.F y :=
  M.rp_eq w b x s hx hs

end Model

end CachonCoord.Proportional

open CachonCoord.Proportional


theorem solution (M : Model) (w b x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    M.retailerProfit w b x s =
      (M.p - w) * x - (M.p - b) * (x / (x + s)) * ∫ y in (0 : ℝ)..(x + s), M.F y := by
  exact M.p50_core w b x s hx hs
