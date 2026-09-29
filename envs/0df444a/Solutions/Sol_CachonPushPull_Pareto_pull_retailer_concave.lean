-- Prove2me | solution 1 for CachonPushPull.Pareto.pull_retailer_concave
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:12:13.067701+00:00
-- url     : https://prove2.me/submissions/d47ecc4c-0198-4008-bcaa-3cc7840702d5

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

theorem aux_prc_F_lt_one (μ : Measure ℝ) (f : ℝ → ℝ)
    (hD : DemandModel μ f) {x : ℝ} (hx : 0 ≤ x) : cdf μ x < 1 := by
  have h1 : cdf μ x < cdf μ (x + 1) :=
    hD.strictMonoOn (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (by linarith)) (by linarith)
  exact lt_of_lt_of_le h1 (cdf_le_one μ _)

theorem aux_prc_f_nonneg (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) {x : ℝ}
    (hx : 0 < x) : 0 ≤ f x := by
  rw [← (hD.hasDerivAt x hx).deriv]
  exact (monotone_cdf μ).deriv_nonneg

theorem aux_prc_g_mono (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) :
    StrictMonoOn (fun y : ℝ => y * f y / (1 - cdf μ y)) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact (differentiableAt_of_deriv_ne_zero (hD.igfr x hx).ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact hD.igfr x hx

theorem aux_prc_S_hasDerivAt (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) {q : ℝ}
    (hq : 0 < q) : HasDerivAt (S μ) (1 - cdf μ q) q := by
  have hmeas : Measurable (cdf μ) := (monotone_cdf μ).measurable
  have hint : HasDerivAt (fun u => ∫ x in (0:ℝ)..u, cdf μ x) (cdf μ q) q :=
    intervalIntegral.integral_hasDerivAt_right ((monotone_cdf μ).intervalIntegrable)
      hmeas.stronglyMeasurable.stronglyMeasurableAtFilter (hD.hasDerivAt q hq).continuousAt
  show HasDerivAt (fun q => q - ∫ x in (0:ℝ)..q, cdf μ x) _ q
  exact (hasDerivAt_id' q).sub hint

theorem aux_prc_S_cont (μ : Measure ℝ) : Continuous (S μ) := by
  show Continuous (fun q => q - ∫ x in (0:ℝ)..q, cdf μ x)
  exact continuous_id.sub
    (intervalIntegral.continuous_primitive (fun a b => (monotone_cdf μ).intervalIntegrable) 0)

theorem aux_prc_S_div (μ : Measure ℝ) {q : ℝ} (hq : 0 < q) :
    S μ q / q = ∫ t in (0:ℝ)..1, (1 - cdf μ (q * t)) := by
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun x => 1 - cdf μ x) hq.ne'
  rw [h, mul_zero, mul_one, intervalIntegral.integral_sub intervalIntegrable_const
    (monotone_cdf μ).intervalIntegrable, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, mul_one, S]
  field_simp

theorem aux_prc_ratio (μ : Measure ℝ) {q : ℝ} (hq : 0 < q) :
    S μ q / (q * (1 - cdf μ q)) = ∫ t in (0:ℝ)..1, (1 - cdf μ (q * t)) / (1 - cdf μ q) := by
  rw [intervalIntegral.integral_div, ← aux_prc_S_div μ hq, div_div]

theorem aux_prc_pointwise (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) {a b t : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - cdf μ (a * t)) / (1 - cdf μ a) ≤ (1 - cdf μ (b * t)) / (1 - cdf μ b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hFa := aux_prc_F_lt_one μ f hD ha.le
  have hFb := aux_prc_F_lt_one μ f hD hb.le
  rcases ht0.eq_or_lt with h | ht
  · subst h
    simp only [mul_zero, hD.cdf_zero, sub_zero]
    apply one_div_le_one_div_of_le (by linarith)
    have := monotone_cdf μ hab
    linarith
  · -- φ(q) = log(1 - F(q t)) - log(1 - F q) is monotone on (0, ∞)
    set φ : ℝ → ℝ := fun q => Real.log (1 - cdf μ (q * t)) - Real.log (1 - cdf μ q) with hφ
    have hderiv : ∀ q : ℝ, 0 < q → HasDerivAt φ
        ((-(f (q * t) * t)) / (1 - cdf μ (q * t)) - (-(f q)) / (1 - cdf μ q)) q := by
      intro q hq
      have hqt : 0 < q * t := mul_pos hq ht
      have h1 : HasDerivAt (fun x => cdf μ (x * t)) (f (q * t) * t) q := by
        have := (hD.hasDerivAt (q * t) hqt).comp q (hasDerivAt_mul_const t)
        exact this
      have h2 := (h1.const_sub 1).log (by linarith [aux_prc_F_lt_one μ f hD hqt.le])
      have h3 := ((hD.hasDerivAt q hq).const_sub 1).log
        (by linarith [aux_prc_F_lt_one μ f hD hq.le])
      exact h2.sub h3
    have hmono : MonotoneOn φ (Set.Ioi 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      · intro x hx
        exact (hderiv x hx).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Ioi] at hx
        exact (hderiv x hx).differentiableAt.differentiableWithinAt
      · intro q hq
        rw [interior_Ioi] at hq
        have hq' : (0:ℝ) < q := hq
        rw [(hderiv q hq').deriv]
        have hqt : 0 < q * t := mul_pos hq' ht
        have hA := aux_prc_F_lt_one μ f hD hqt.le
        have hB := aux_prc_F_lt_one μ f hD hq'.le
        have hA' : 1 - cdf μ (q * t) ≠ 0 := by linarith
        have hB' : 1 - cdf μ q ≠ 0 := by linarith
        have key : (q * t) * f (q * t) / (1 - cdf μ (q * t)) ≤ q * f q / (1 - cdf μ q) :=
          (aux_prc_g_mono μ f hD).monotoneOn hqt hq' (by nlinarith)
        have heq : (-(f (q * t) * t)) / (1 - cdf μ (q * t)) - (-(f q)) / (1 - cdf μ q)
            = (q * f q / (1 - cdf μ q) - (q * t) * f (q * t) / (1 - cdf μ (q * t))) / q := by
          field_simp
          ring
        rw [heq]
        exact div_nonneg (sub_nonneg.2 key) hq'.le
    have hle := hmono ha hb hab
    simp only [hφ] at hle
    have hat : 0 < 1 - cdf μ (a * t) := by
      linarith [aux_prc_F_lt_one μ f hD (mul_pos ha ht).le]
    have hbt : 0 < 1 - cdf μ (b * t) := by
      linarith [aux_prc_F_lt_one μ f hD (mul_pos hb ht).le]
    have hpa : 0 < 1 - cdf μ a := by linarith
    have hpb : 0 < 1 - cdf μ b := by linarith
    rw [← Real.log_le_log_iff (div_pos hat hpa) (div_pos hbt hpb),
      Real.log_div hat.ne' hpa.ne', Real.log_div hbt.ne' hpb.ne']
    exact hle

theorem aux_prc_ratio_integrable (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) {q : ℝ}
    (hq : 0 < q) :
    IntervalIntegrable (fun t => (1 - cdf μ (q * t)) / (1 - cdf μ q)) volume 0 1 := by
  apply Antitone.intervalIntegrable
  intro x y hxy
  have hp : 0 < 1 - cdf μ q := by linarith [aux_prc_F_lt_one μ f hD hq.le]
  apply div_le_div_of_nonneg_right _ hp.le
  have := monotone_cdf μ (mul_le_mul_of_nonneg_left hxy hq.le)
  linarith

theorem aux_prc_jh_mono (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) :
    MonotoneOn (fun q => S μ q * f q / (1 - cdf μ q) ^ 2) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0:ℝ) < a := ha
  have hb' : (0:ℝ) < b := hb
  have hpa : 0 < 1 - cdf μ a := by linarith [aux_prc_F_lt_one μ f hD ha'.le]
  have hpb : 0 < 1 - cdf μ b := by linarith [aux_prc_F_lt_one μ f hD hb'.le]
  have hA : S μ a / (a * (1 - cdf μ a)) ≤ S μ b / (b * (1 - cdf μ b)) := by
    rw [aux_prc_ratio μ ha', aux_prc_ratio μ hb']
    apply intervalIntegral.integral_mono_on zero_le_one (aux_prc_ratio_integrable μ f hD ha')
      (aux_prc_ratio_integrable μ f hD hb')
    intro t ht
    exact aux_prc_pointwise μ f hD ha' hab ht.1 ht.2
  have hA0 : 0 ≤ S μ a / (a * (1 - cdf μ a)) := by
    rw [aux_prc_ratio μ ha']
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t _
    apply div_nonneg _ hpa.le
    linarith [cdf_le_one μ (a * t)]
  have hg : a * f a / (1 - cdf μ a) ≤ b * f b / (1 - cdf μ b) :=
    (aux_prc_g_mono μ f hD).monotoneOn ha hb hab
  have hg0 : 0 ≤ b * f b / (1 - cdf μ b) :=
    div_nonneg (mul_nonneg hb'.le (aux_prc_f_nonneg μ f hD hb')) hpb.le
  have hea : S μ a * f a / (1 - cdf μ a) ^ 2
      = S μ a / (a * (1 - cdf μ a)) * (a * f a / (1 - cdf μ a)) := by
    field_simp
  have heb : S μ b * f b / (1 - cdf μ b) ^ 2
      = S μ b / (b * (1 - cdf μ b)) * (b * f b / (1 - cdf μ b)) := by
    field_simp
  show S μ a * f a / (1 - cdf μ a) ^ 2 ≤ S μ b * f b / (1 - cdf μ b) ^ 2
  rw [hea, heb]
  calc S μ a / (a * (1 - cdf μ a)) * (a * f a / (1 - cdf μ a))
      ≤ S μ a / (a * (1 - cdf μ a)) * (b * f b / (1 - cdf μ b)) :=
        mul_le_mul_of_nonneg_left hg hA0
    _ ≤ S μ b / (b * (1 - cdf μ b)) * (b * f b / (1 - cdf μ b)) :=
        mul_le_mul_of_nonneg_right hA hg0

theorem aux_prc_deriv (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) (p c v : ℝ) {q : ℝ}
    (hq : 0 < q) :
    deriv (pullRetailerProfit μ p c v) q =
      (p - v) * (1 - cdf μ q) - (c - v) - (c - v) * (S μ q * f q / (1 - cdf μ q) ^ 2) := by
  have hF := hD.hasDerivAt q hq
  have hS := aux_prc_S_hasDerivAt μ f hD hq
  have hp : 0 < 1 - cdf μ q := by linarith [aux_prc_F_lt_one μ f hD hq.le]
  have hw := ((hF.const_mul v).const_sub c).div (hF.const_sub 1) hp.ne'
  have hπ := (hw.const_sub p).mul hS
  have e : pullRetailerProfit μ p c v =
      fun x => (p - (c - v * cdf μ x) / (1 - cdf μ x)) * S μ x := by
    funext x
    rfl
  rw [e]
  refine hπ.deriv.trans ?_
  simp only [Pi.div_apply]
  field_simp
  ring

theorem aux_prc_F_contOn (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) :
    ContinuousOn (cdf μ) (Set.Ici 0) := by
  intro x hx
  rcases (Set.mem_Ici.1 hx).eq_or_lt with h | h
  · subst h
    exact (cdf μ).right_continuous 0
  · exact (hD.hasDerivAt x h).continuousAt.continuousWithinAt

end CachonPushPull.Pareto

open CachonPushPull.Pareto
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    StrictConcaveOn ℝ (Set.Ici 0) (pullRetailerProfit μ p c v) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
  · have e : pullRetailerProfit μ p c v =
        fun x => (p - (c - v * cdf μ x) / (1 - cdf μ x)) * S μ x := by
      funext x
      rfl
    rw [e]
    have hF := aux_prc_F_contOn μ f hD
    apply ContinuousOn.mul _ (aux_prc_S_cont μ).continuousOn
    apply continuousOn_const.sub
    apply ContinuousOn.div (continuousOn_const.sub (continuousOn_const.mul hF))
      (continuousOn_const.sub hF)
    intro x hx
    have := aux_prc_F_lt_one μ f hD (Set.mem_Ici.1 hx)
    show (1:ℝ) - cdf μ x ≠ 0
    exact (sub_pos.2 this).ne'
  · rw [interior_Ici]
    intro a ha b hb hab
    have ha' : (0:ℝ) < a := ha
    have hb' : (0:ℝ) < b := hb
    rw [aux_prc_deriv μ f hD p c v ha', aux_prc_deriv μ f hD p c v hb']
    have hF : cdf μ a < cdf μ b :=
      hD.strictMonoOn (Set.mem_Ici.2 ha'.le) (Set.mem_Ici.2 hb'.le) hab
    have hjh := aux_prc_jh_mono μ f hD ha hb hab.le
    simp only at hjh
    have h1 : (p - v) * (1 - cdf μ b) < (p - v) * (1 - cdf μ a) := by
      apply mul_lt_mul_of_pos_left _ (by linarith)
      linarith
    have h2 : (c - v) * (S μ a * f a / (1 - cdf μ a) ^ 2)
        ≤ (c - v) * (S μ b * f b / (1 - cdf μ b) ^ 2) :=
      mul_le_mul_of_nonneg_left hjh (by linarith)
    linarith
