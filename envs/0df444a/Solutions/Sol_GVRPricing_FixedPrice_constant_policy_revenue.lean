-- Prove2me | solution 1 for GVRPricing.FixedPrice.constant_policy_revenue
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T22:13:44.04664+00:00
-- url     : https://prove2.me/submissions/8a9e3e1f-ccaf-4283-804f-727f2c5dfd01

import Init
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FixedClock
open GVRPricing.FixedPrice
variable (M : Model) (c : ℝ) (hc : c ∈ M.Λ) (hc0 : 0 < c)

include hc hc0 in
lemma cumulative (j : ℕ) (τ : Fin j → ℝ) (s : ℝ) :
    (constPolicy M c).cumIntensity j τ s = ENNReal.ofReal (c * (s - lastTime j τ)) := by
  simp only [Policy.cumIntensity, constPolicy, if_pos hc, setLIntegral_const, Real.volume_Ioc]
  exact (ENNReal.ofReal_mul hc0.le).symm

include hc hc0 in
lemma next_sale (j : ℕ) (τ : Fin j → ℝ) (e : ℝ) (he : 0 ≤ e) :
    (constPolicy M c).nextSale j τ e = some (lastTime j τ + e / c) := by
  have hset : {s : ℝ | lastTime j τ ≤ s ∧ ENNReal.ofReal e ≤ (constPolicy M c).cumIntensity j τ s} =
      Ici (lastTime j τ + e / c) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    rw [cumulative M c hc hc0]
    constructor
    · rintro ⟨hs, hh⟩
      have hbound := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc0.le (sub_nonneg.mpr hs))).1 hh
      have hdiv : e / c ≤ s - lastTime j τ := (div_le_iff₀ hc0).2 (by nlinarith)
      linarith
    · intro hs
      have hdiv : 0 ≤ e / c := div_nonneg he hc0.le
      have hbase : lastTime j τ ≤ s := by linarith
      refine ⟨hbase, ENNReal.ofReal_le_ofReal ?_⟩
      have hh : e / c ≤ s - lastTime j τ := by linarith
      have := (div_le_iff₀ hc0).1 hh
      nlinarith
  simp only [Policy.nextSale, hset, nonempty_Ici, ↓reduceIte, csInf_Ici]

noncomputable def times (c : ℝ) (E : ℕ → ℝ) : (j : ℕ) → (Fin j → ℝ)
  | 0 => Fin.elim0
  | j + 1 => Fin.snoc (α := fun _ => ℝ) (times c E j) ((∑ k ∈ Finset.range (j + 1), E k) / c)

lemma last_times (E : ℕ → ℝ) (j : ℕ) :
    lastTime j (times c E j) = (∑ k ∈ Finset.range j, E k) / c := by
  cases j with
  | zero => simp [lastTime]
  | succ j => simp [lastTime, times]

include hc hc0 in
lemma history (E : ℕ → ℝ) (hE : ∀ k, 0 ≤ E k) (j : ℕ) :
    (constPolicy M c).history E j = some (times c E j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Policy.history, ih]
    simp only [Option.bind_some, next_sale M c hc hc0 _ _ _ (hE j), Option.map_some]
    rw [last_times]
    simp only [times, Finset.sum_range_succ, add_div]

include hc hc0 in
lemma sale_time (E : ℕ → ℝ) (hE : ∀ k, 0 ≤ E k) (j : ℕ) :
    (constPolicy M c).saleTime E j = (((∑ k ∈ Finset.range j, E k) / c : ℝ) : WithTop ℝ) := by
  simp only [Policy.saleTime, history M c hc hc0 E hE, Option.elim_some, last_times]

include hc hc0 in
lemma sales_by (n : ℕ) (t : ℝ) (E : ℕ → ℝ) (hE : ∀ k, 0 ≤ E k) :
    (constPolicy M c).salesBy n t E =
      ((Finset.range n).filter fun j => (∑ k ∈ Finset.range (j + 1), E k) ≤ c * t).card := by
  classical
  unfold Policy.salesBy
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [sale_time M c hc hc0 E hE]
  simp only [WithTop.coe_le_coe, div_le_iff₀ hc0]
  rw [mul_comm t c]

include hc hc0 in
lemma revenue_on (n : ℕ) (t : ℝ) (E : ℕ → ℝ) (hE : ∀ k, 0 ≤ E k) :
    (constPolicy M c).revenueOn n t E =
      ∑ j ∈ Finset.range n,
        if (∑ k ∈ Finset.range (j + 1), E k) ≤ c * t then ENNReal.ofReal (M.p c) else 0 := by
  classical
  unfold Policy.revenueOn
  apply Finset.sum_congr rfl
  intro j hj
  rw [history M c hc hc0 E hE]
  simp only [Option.elim_some, times, Fin.snoc_last, constPolicy, if_pos hc, Model.price,
    if_neg (ne_of_gt hc0), div_le_iff₀ hc0, mul_comm t c]

end FixedClock

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FixedClock
open GVRPricing.FixedPrice

lemma exp_nonnegative : ∀ᵐ x ∂expMeasure 1, 0 ≤ x := by
  rw [ae_iff]
  change (expMeasure 1) {x : ℝ | ¬ 0 ≤ x} = 0
  simp only [not_le]
  change (expMeasure 1) (Iio 0) = 0
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos (le_refl 0)

lemma clocks_nonnegative : ∀ᵐ E ∂clockLaw, ∀ k, 0 ≤ E k := by
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure (by norm_num)
  apply ae_all_iff.mpr
  intro k
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => expMeasure (1 : ℝ)) k).quasiMeasurePreserving.ae exp_nonnegative

lemma partial_sum_measurable (j : ℕ) :
    Measurable (fun E : ℕ → ℝ => ∑ k ∈ Finset.range j, E k) := by
  fun_prop

lemma arrival_event_measurable (j : ℕ) (x : ℝ) :
    MeasurableSet {E : ℕ → ℝ | (∑ k ∈ Finset.range j, E k) ≤ x} :=
  measurableSet_le (partial_sum_measurable j) measurable_const

variable (M : Model) (c : ℝ) (hc : c ∈ M.Λ) (hc0 : 0 < c)

include hc hc0 in
lemma expected_revenue_tails (n : ℕ) (t : ℝ) :
    (constPolicy M c).expectedRevenue n t =
      ENNReal.ofReal (M.p c) * ∑ j ∈ Finset.range n,
        clockLaw {E : ℕ → ℝ | (∑ k ∈ Finset.range (j + 1), E k) ≤ c * t} := by
  classical
  unfold Policy.expectedRevenue
  calc
    _ = ∫⁻ E, ∑ j ∈ Finset.range n,
        if (∑ k ∈ Finset.range (j + 1), E k) ≤ c * t then ENNReal.ofReal (M.p c) else 0 ∂clockLaw := by
      apply lintegral_congr_ae
      filter_upwards [clocks_nonnegative] with E hE
      exact revenue_on M c hc hc0 n t E hE
    _ = ∑ j ∈ Finset.range n, ∫⁻ E,
        if (∑ k ∈ Finset.range (j + 1), E k) ≤ c * t then ENNReal.ofReal (M.p c) else 0 ∂clockLaw := by
      apply lintegral_finsetSum
      intro j hj
      exact Measurable.ite (arrival_event_measurable (j+1) (c*t)) measurable_const measurable_const
    _ = ∑ j ∈ Finset.range n, ENNReal.ofReal (M.p c) *
        clockLaw {E : ℕ → ℝ | (∑ k ∈ Finset.range (j + 1), E k) ≤ c * t} := by
      apply Finset.sum_congr rfl
      intro j hj
      change (∫⁻ E, ({E : ℕ → ℝ | (∑ k ∈ Finset.range (j + 1), E k) ≤ c * t}).indicator
        (fun _ => ENNReal.ofReal (M.p c)) E ∂clockLaw) = _
      rw [lintegral_indicator (arrival_event_measurable (j+1) (c*t)), setLIntegral_const]
    _ = _ := (Finset.mul_sum _ _ _).symm

end FixedClock

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FixedClock

lemma truncated_count (n k : ℕ) :
    ENNReal.ofReal ((k : ℝ) - max ((k : ℝ) - n) 0) =
      ∑ j ∈ Finset.range n, if j < k then (1 : ℝ≥0∞) else 0 := by
  classical
  have hr : (k : ℝ) - max ((k : ℝ) - n) 0 = (min n k : ℕ) := by
    by_cases h : n ≤ k
    · have hh : (n : ℝ) ≤ k := by exact_mod_cast h
      rw [max_eq_left (by linarith), min_eq_left h]
      ring
    · have hh : (k : ℝ) ≤ n := by exact_mod_cast le_of_not_ge h
      rw [max_eq_right (by linarith), min_eq_right (le_of_not_ge h)]
      simp
  rw [hr]
  have hs : (Finset.range n).filter (fun j => j < k) = Finset.range (min n k) := by
    ext j
    simp [lt_min_iff]
  rw [← Finset.sum_filter, hs]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, ENNReal.ofReal_natCast]

lemma truncated_expectation (μ : Measure ℕ) (n : ℕ) :
    (∫⁻ k, ENNReal.ofReal ((k : ℝ) - max ((k : ℝ) - n) 0) ∂μ) =
      ∑ j ∈ Finset.range n, μ {k : ℕ | j < k} := by
  classical
  simp_rw [truncated_count]
  rw [lintegral_finsetSum _ (fun _ _ => measurable_of_countable _)]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [Set.indicator, Set.mem_setOf_eq, setLIntegral_const, one_mul] using
    (lintegral_indicator (μ := μ) (f := fun _ : ℕ => (1 : ℝ≥0∞))
      ((Set.to_countable {k : ℕ | j < k}).measurableSet))

open GVRPricing.FixedPrice
variable (M : Model) (c : ℝ) (hc : c ∈ M.Λ) (hc0 : 0 < c)

include hc hc0 in
lemma revenue_from_arrival_tails (n : ℕ) (t : ℝ)
    (h : ∀ j < n,
      clockLaw {E : ℕ → ℝ | (∑ k ∈ Finset.range (j+1), E k) ≤ c*t} =
        poissonMeasure (Real.toNNReal (c*t)) {k : ℕ | j < k}) :
    (constPolicy M c).expectedRevenue n t =
      ENNReal.ofReal (M.p c) *
        ∫⁻ k, ENNReal.ofReal ((k : ℝ) - max ((k : ℝ) - n) 0) ∂poissonMeasure (Real.toNNReal (c*t)) := by
  rw [expected_revenue_tails M c hc hc0, truncated_expectation]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact h j (Finset.mem_range.mp hj)

end FixedClock

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FixedClock
open GVRPricing.FixedPrice

lemma first_arrival_probability (x : ℝ) (hx : 0 ≤ x) :
    clockLaw {E : ℕ → ℝ | (∑ k ∈ Finset.range 1, E k) ≤ x} =
      ENNReal.ofReal (1 - Real.exp (-x)) := by
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure (by norm_num)
  simp only [Finset.sum_range_one]
  change clockLaw ((fun E : ℕ → ℝ => E 0) ⁻¹' Iic x) = _
  rw [← Measure.map_apply (measurable_pi_apply 0) measurableSet_Iic]
  rw [clockLaw, Measure.infinitePi_map_eval]
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iic]
  change (∫⁻ y in Iic x, exponentialPDF 1 y) = _
  rw [lintegral_exponentialPDF_eq_antiDeriv (by norm_num)]
  simp [hx]

lemma poisson_positive_probability (x : ℝ) (hx : 0 ≤ x) :
    poissonMeasure (Real.toNNReal x) {k : ℕ | 0 < k} =
      ENNReal.ofReal (1 - Real.exp (-x)) := by
  have hs : {k : ℕ | 0 < k} = ({0} : Set ℕ)ᶜ := by ext k; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]; omega
  rw [hs, measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), measure_univ,
    poissonMeasure_singleton]
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, Real.coe_toNNReal _ hx]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (Real.exp_pos (-x)).le]

variable (M : Model) (c : ℝ) (hc : c ∈ M.Λ) (hc0 : 0 < c)

include hc hc0 in
lemma one_item_revenue (t : ℝ) (ht : 0 ≤ t) :
    (constPolicy M c).expectedRevenue 1 t =
      ENNReal.ofReal (M.p c) * ENNReal.ofReal (1 - Real.exp (-(c*t))) := by
  rw [expected_revenue_tails M c hc hc0]
  simp only [Finset.sum_range_one]
  rw [first_arrival_probability (c*t) (mul_nonneg hc0.le ht)]

include hc hc0 in
lemma one_item_poisson_formula (t : ℝ) (ht : 0 ≤ t) :
    (constPolicy M c).expectedRevenue 1 t =
      ENNReal.ofReal (M.p c) *
        ∫⁻ k, ENNReal.ofReal ((k : ℝ) - max ((k : ℝ) - 1) 0) ∂poissonMeasure (Real.toNNReal (c*t)) := by
  have h : ∀ j < 1, clockLaw {E : ℕ → ℝ | (∑ k ∈ Finset.range (j+1), E k) ≤ c*t} =
      poissonMeasure (Real.toNNReal (c*t)) {k : ℕ | j < k} := by
    intro j hj
    have : j = 0 := by omega
    subst j
    rw [first_arrival_probability (c*t) (mul_nonneg hc0.le ht),
      poisson_positive_probability (c*t) (mul_nonneg hc0.le ht)]
  simpa only [Nat.cast_one] using revenue_from_arrival_tails M c hc hc0 1 t h

end FixedClock

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FixedClock
open GVRPricing.FixedPrice

lemma partial_sum_independent (j : ℕ) :
    IndepFun (fun E : ℕ → ℝ => ∑ k ∈ Finset.range j, E k) (fun E => E j) clockLaw := by
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure (by norm_num)
  have hi : iIndepFun (fun k (E : ℕ → ℝ) => E k) clockLaw :=
    iIndepFun_infinitePi (X := fun (_ : ℕ) (x : ℝ) => x) (by intro i; fun_prop)
  have h := hi.indepFun_finsetSum_of_notMem
    (fun i => measurable_pi_apply i) (s := Finset.range j) (by simp : j ∉ Finset.range j)
  convert h using 1
  funext E
  simp only [Finset.sum_apply]

lemma arrival_recurrence (j : ℕ) (x : ℝ) :
    clockLaw {E : ℕ → ℝ | (∑ k ∈ Finset.range (j+1), E k) ≤ x} =
      ∫⁻ y, clockLaw {E : ℕ → ℝ | (∑ k ∈ Finset.range j, E k) ≤ x-y} ∂expMeasure 1 := by
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure (by norm_num)
  haveI : IsProbabilityMeasure clockLaw := by unfold clockLaw; infer_instance
  let f : (ℕ → ℝ) → ℝ := fun E => ∑ k ∈ Finset.range j, E k
  have hf : Measurable f := partial_sum_measurable j
  have hmap : clockLaw.map (fun E : ℕ → ℝ => (E j, f E)) =
      (expMeasure 1).prod (clockLaw.map f) := by
    rw [(partial_sum_independent j).symm.map_prod_eq_prod_map_map (measurable_pi_apply j).aemeasurable hf.aemeasurable]
    congr 1
    exact Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure (1 : ℝ)) j
  let A : Set (ℝ × ℝ) := {p | p.2 ≤ x - p.1}
  have hA : MeasurableSet A := measurableSet_le measurable_snd (measurable_const.sub measurable_fst)
  calc
    _ = (clockLaw.map (fun E : ℕ → ℝ => (E j, f E))) A := by
      rw [Measure.map_apply ((measurable_pi_apply j).prodMk hf) hA]
      congr 1
      ext E
      simp only [Set.mem_setOf_eq, Set.mem_preimage, A, f, Finset.sum_range_succ]
      constructor <;> intro h <;> linarith
    _ = ((expMeasure 1).prod (clockLaw.map f)) A := by rw [hmap]
    _ = ∫⁻ y, (clockLaw.map f) (Iic (x-y)) ∂expMeasure 1 := by
      rw [Measure.prod_apply hA]
      rfl
    _ = _ := by
      apply lintegral_congr
      intro y
      rw [Measure.map_apply hf measurableSet_Iic]
      rfl

end FixedClock

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FixedClock

lemma poisson_initial_segment (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    poissonMeasure (Real.toNNReal x) (Finset.range n : Set ℕ) =
      ENNReal.ofReal (Real.exp (-x) * ∑ k ∈ Finset.range n, x^k / (k.factorial : ℝ)) := by
  rw [← sum_measure_singleton]
  simp_rw [poissonMeasure_singleton, Real.coe_toNNReal _ hx]
  rw [← ENNReal.ofReal_sum_of_nonneg (by intro k hk; positivity)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma poisson_tail_series (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    poissonMeasure (Real.toNNReal x) {k : ℕ | n ≤ k} =
      ENNReal.ofReal (1 - Real.exp (-x) * ∑ k ∈ Finset.range n, x^k / (k.factorial : ℝ)) := by
  have hs : {k : ℕ | n ≤ k} = (Finset.range n : Set ℕ)ᶜ := by
    ext k
    simp
  rw [hs, measure_compl (Finset.measurableSet _) (measure_ne_top _ _), measure_univ,
    poisson_initial_segment n x hx, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by positivity)]

lemma poisson_partial_series_le_one (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) * (∑ k ∈ Finset.range n, x^k / (k.factorial : ℝ)) ≤ 1 := by
  have h := measure_mono (μ := poissonMeasure (Real.toNNReal x))
    (Set.subset_univ (Finset.range n : Set ℕ))
  rw [poisson_initial_segment n x hx, measure_univ] at h
  exact (ENNReal.ofReal_le_one).1 h

end FixedClock

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FixedClock

noncomputable def primitiveSeries (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, y^(k+1) / ((k+1).factorial : ℝ)

lemma primitive_series_derivative (n : ℕ) (y : ℝ) :
    HasDerivAt (primitiveSeries n) (∑ k ∈ Finset.range n, y^k / (k.factorial : ℝ)) y := by
  unfold primitiveSeries
  apply HasDerivAt.fun_sum
  intro k hk
  convert! ((hasDerivAt_id y).pow (k+1)).div_const ((k+1).factorial : ℝ) using 1
  simp only [id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one, Nat.factorial_succ, Nat.cast_mul]
  field_simp

lemma series_successor (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (n+1), x^k / (k.factorial : ℝ)) = 1 + primitiveSeries n x := by
  rw [Finset.sum_range_succ']
  simp [primitiveSeries, add_comm]

lemma shifted_series_integral (n : ℕ) (x : ℝ) :
    (∫ y in 0..x, Real.exp (-y) - Real.exp (-x) *
      (∑ k ∈ Finset.range n, (x-y)^k / (k.factorial : ℝ))) =
      1 - Real.exp (-x) * (∑ k ∈ Finset.range (n+1), x^k / (k.factorial : ℝ)) := by
  let F : ℝ → ℝ := fun y => -Real.exp (-y) + Real.exp (-x) * primitiveSeries n (x-y)
  have hd : ∀ y, HasDerivAt F (Real.exp (-y) - Real.exp (-x) *
      (∑ k ∈ Finset.range n, (x-y)^k / (k.factorial : ℝ))) y := by
    intro y
    have he := ((hasDerivAt_id y).neg.exp).neg
    have hq := (primitive_series_derivative n (x-y)).comp y
      ((hasDerivAt_const y x).sub (hasDerivAt_id y))
    convert! he.add (hq.const_mul (Real.exp (-x))) using 1 <;> simp [F, sub_eq_add_neg]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hd y) (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [F, sub_self, primitiveSeries, zero_pow (Nat.add_one_ne_zero _), zero_div,
    Finset.sum_const_zero, mul_zero, add_zero, neg_zero, Real.exp_zero, sub_zero]
  rw [series_successor]
  unfold primitiveSeries
  ring

end FixedClock

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FixedClock
open GVRPricing.FixedPrice

noncomputable def cdfSeries (n : ℕ) (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 - Real.exp (-x) * ∑ k ∈ Finset.range n, x^k / (k.factorial : ℝ) else 0

lemma exponential_product (x y : ℝ) :
    Real.exp (-y) * Real.exp (-(x-y)) = Real.exp (-x) := by
  rw [← Real.exp_add]
  congr 1
  ring

lemma cdf_convolution (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (∫⁻ y, ENNReal.ofReal (cdfSeries n (x-y)) ∂expMeasure 1) =
      ENNReal.ofReal (cdfSeries (n+1) x) := by
  classical
  let f : ℝ → ℝ := fun y => Real.exp (-y) - Real.exp (-x) *
    (∑ k ∈ Finset.range n, (x-y)^k / (k.factorial : ℝ))
  have hf : Continuous f := by fun_prop
  have hfactor (y : ℝ) (hy : y ≤ x) :
      Real.exp (-y) * cdfSeries n (x-y) = f y := by
    rw [cdfSeries, if_pos (by linarith : 0 ≤ x-y)]
    dsimp [f]
    rw [mul_sub, mul_one, ← mul_assoc, exponential_product]
  have hnonneg : ∀ y ∈ Icc 0 x, 0 ≤ f y := by
    intro y hy
    rw [← hfactor y hy.2, cdfSeries, if_pos (by linarith [hy.2] : 0 ≤ x-y)]
    exact mul_nonneg (Real.exp_pos _).le
      (sub_nonneg.mpr (poisson_partial_series_le_one n (x-y) (by linarith [hy.2])))
  have hk (y : ℝ) : exponentialPDF 1 y * ENNReal.ofReal (cdfSeries n (x-y)) =
      (Icc 0 x).indicator (fun y => ENNReal.ofReal (f y)) y := by
    by_cases hy : 0 ≤ y
    · rw [exponentialPDF_of_nonneg hy]
      simp only [one_mul]
      by_cases hyx : y ≤ x
      · rw [Set.indicator_of_mem (show y ∈ Icc 0 x from ⟨hy,hyx⟩), ← ENNReal.ofReal_mul (Real.exp_pos _).le, hfactor y hyx]
      · rw [cdfSeries, if_neg (by linarith : ¬ 0 ≤ x-y), ENNReal.ofReal_zero, mul_zero,
          Set.indicator_of_notMem (by exact fun h => hyx h.2)]
    · rw [exponentialPDF_of_neg (lt_of_not_ge hy), zero_mul,
        Set.indicator_of_notMem (by exact fun h => hy h.1)]
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul volume
    (by unfold gammaPDF; fun_prop) (by
      unfold cdfSeries
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.ite (measurableSet_le measurable_const (measurable_const.sub measurable_id))
      · fun_prop
      · exact measurable_const)]
  change (∫⁻ y, exponentialPDF 1 y * ENNReal.ofReal (cdfSeries n (x-y))) = _
  simp_rw [hk]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn_Icc
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy; exact hnonneg y hy)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  change ENNReal.ofReal (∫ y in 0..x, Real.exp (-y) - Real.exp (-x) *
    (∑ k ∈ Finset.range n, (x-y)^k / (k.factorial : ℝ))) = _
  rw [shifted_series_integral]
  simp only [cdfSeries, if_pos hx]

lemma arrival_probability_negative (n : ℕ) (x : ℝ) (hx : x < 0) :
    clockLaw {E : ℕ → ℝ | (∑ k ∈ Finset.range n, E k) ≤ x} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [clocks_nonnegative] with E hE
  intro h
  have hs : 0 ≤ ∑ k ∈ Finset.range n, E k := Finset.sum_nonneg (fun k hk => hE k)
  exact (not_le.mpr (lt_of_lt_of_le hx hs)) h

lemma arrival_distribution (n : ℕ) (x : ℝ) :
    clockLaw {E : ℕ → ℝ | (∑ k ∈ Finset.range n, E k) ≤ x} =
      ENNReal.ofReal (cdfSeries n x) := by
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure (by norm_num)
  haveI : IsProbabilityMeasure clockLaw := by unfold clockLaw; infer_instance
  induction n generalizing x with
  | zero =>
    by_cases hx : 0 ≤ x <;> simp [cdfSeries, hx]
  | succ n ih =>
    by_cases hx : 0 ≤ x
    · rw [arrival_recurrence]
      simp_rw [ih]
      exact cdf_convolution n x hx
    · rw [arrival_probability_negative (n+1) x (lt_of_not_ge hx)]
      simp [cdfSeries, hx]

lemma arrival_poisson_tail (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    clockLaw {E : ℕ → ℝ | (∑ k ∈ Finset.range n, E k) ≤ x} =
      poissonMeasure (Real.toNNReal x) {k : ℕ | n ≤ k} := by
  rw [arrival_distribution, poisson_tail_series n x hx]
  simp only [cdfSeries, if_pos hx]

end FixedClock

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open GVRPricing.FixedPrice

theorem solution (M : Model) (c : ℝ) (hc : c ∈ M.Λ) (hc0 : 0 < c) (n : ℕ) (t : ℝ)
    (ht : 0 ≤ t) :
    (constPolicy M c).expectedRevenue n t =
      ENNReal.ofReal (M.p c) *
        ∫⁻ k, ENNReal.ofReal ((k : ℝ) - max ((k : ℝ) - n) 0) ∂poissonMeasure (Real.toNNReal (c * t)) := by
  apply FixedClock.revenue_from_arrival_tails M c hc hc0
  intro j hj
  rw [FixedClock.arrival_poisson_tail (j+1) (c*t) (mul_nonneg hc0.le ht)]
  congr 1

#print axioms solution
