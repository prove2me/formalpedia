-- Prove2me | solution 1 for GVRPricing.FixedPrice.fp_abundant_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T02:22:37.176868+00:00
-- url     : https://prove2.me/submissions/c2d4a5a6-bbb3-445f-a310-f9651c12926a

import Init
import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_Deterministic
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory Set Function Classical
noncomputable section
namespace Pricing
open GVRPricing.FixedPrice
lemma star_mem (M : Model) : M.lstar ∈ M.Λ := M.isLeast_lstar.1.1
lemma star_nonneg (M : Model) : 0 ≤ M.lstar := M.nonneg _ (star_mem M)
lemma r_nonneg (M : Model) {l : ℝ} (hl : l ∈ M.Λ) : 0 ≤ M.r l := by
  by_cases he : l=0
  · simp [he,Model.r]
  · exact mul_nonneg (M.nonneg _ hl) (M.price_nonneg _ hl he)
lemma r_le_star (M : Model) {l : ℝ} (hl : l ∈ M.Λ) : M.r l ≤ M.rstar := M.isLeast_lstar.1.2 l hl
lemma interval_mem (M : Model) : Icc 0 M.lstar ⊆ M.Λ :=
  M.ordConnected.out M.zero_mem (star_mem M)
lemma chosen_mem (M : Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    min M.lstar (x/t) ∈ Icc 0 M.lstar :=
  ⟨le_min (star_nonneg M) (div_nonneg hx ht.le),min_le_left _ _⟩
lemma r_monotone (M : Model) : MonotoneOn M.r (Icc 0 M.lstar) := by
  intro a ha b hb hab
  rcases hab.eq_or_lt with rfl|hab
  · rfl
  by_cases he : b=M.lstar
  · simpa [he,Model.rstar] using r_le_star M (interval_mem M ha)
  have hbs : b<M.lstar := lt_of_le_of_ne hb.2 he
  have hsl := M.concaveOn.slope_anti_adjacent (interval_mem M ha) (star_mem M) hab hbs
  have hn : 0 ≤ (M.r M.lstar-M.r b)/(M.lstar-b) :=
    div_nonneg (sub_nonneg.mpr (r_le_star M (interval_mem M hb))) (sub_pos.mpr hbs).le
  have := hn.trans hsl
  have : 0 ≤ (M.r b-M.r a) := by simpa [Model.r] using (le_div_iff₀ (sub_pos.mpr hab)).mp this
  linarith
lemma constant_feasible (M : Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    IsFeasiblePath M x t (fun _ => min M.lstar (x/t)) := by
  refine ⟨⟨measurable_const,fun s hs => interval_mem M (chosen_mem M x t hx ht),intervalIntegrable_const⟩,?_⟩
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  calc t * min M.lstar (x/t) ≤ t*(x/t) := mul_le_mul_of_nonneg_left (min_le_right _ _) ht.le
       _ = x := mul_div_cancel₀ x ht.ne'
end Pricing

open MeasureTheory Set Function Classical
noncomputable section
namespace Pricing
open GVRPricing.FixedPrice

lemma revenue_integrable (M : Model) (t : ℝ) (ℓ : ℝ → ℝ) (hℓ : IsRatePath M t ℓ) :
    IntegrableOn (fun s => M.r (ℓ s)) (Ioc 0 t) := by
  let R : ℝ → ℝ := M.Λ.piecewise M.r (fun _ => 0)
  have hm : Measurable R := M.continuousOn.measurable_piecewise continuousOn_const M.ordConnected.measurableSet
  have hmeas : AEStronglyMeasurable (fun s => M.r (ℓ s)) (volume.restrict (Ioc 0 t)) := by
    apply (hm.comp hℓ.1).aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp [R,Set.piecewise,hℓ.2.1 s ⟨hs.1.le,hs.2⟩]
  apply (integrable_const M.rstar).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs,abs_of_nonneg (r_nonneg M (hℓ.2.1 s ⟨hs.1.le,hs.2⟩))]
  exact r_le_star M (hℓ.2.1 s ⟨hs.1.le,hs.2⟩)

lemma clipped_rate_pos (M : Model) (t : ℝ) (ht : 0 ≤ t) (ℓ : ℝ → ℝ) (hℓ : IsRatePath M t ℓ) :
    IsRatePath M t (fun s => min M.lstar (ℓ s)) := by
  have hm : Measurable (fun s => min M.lstar (ℓ s)) := measurable_const.min hℓ.1
  have hs (s : ℝ) (ht : s ∈ Icc 0 t) : min M.lstar (ℓ s) ∈ Icc 0 M.lstar :=
    ⟨le_min (star_nonneg M) (M.nonneg _ (hℓ.2.1 s ht)),min_le_left _ _⟩
  refine ⟨hm,fun s ht => interval_mem M (hs s ht),?_⟩
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
  apply (integrable_const M.lstar).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s ht
  rw [Real.norm_eq_abs,abs_of_nonneg (hs s ⟨ht.1.le,ht.2⟩).1]
  exact (hs s ⟨ht.1.le,ht.2⟩).2

lemma cap_improves (M : Model) {l : ℝ} (hl : l ∈ M.Λ) : M.r l ≤ M.r (min M.lstar l) := by
  rcases le_total M.lstar l with h|h
  · simpa [min_eq_left h,Model.rstar] using r_le_star M hl
  · rw [min_eq_right h]
end Pricing

open MeasureTheory Set Function Classical
noncomputable section
namespace Pricing
open GVRPricing.FixedPrice

theorem revenue_optimal (M : Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t)
    (ℓ : ℝ → ℝ) (hℓ : IsFeasiblePath M x t ℓ) :
    (∫ s in (0 : ℝ)..t, M.r (ℓ s)) ≤ t*M.r (min M.lstar (x/t)) := by
  let k : ℝ → ℝ := fun s => min M.lstar (ℓ s)
  have hk : IsRatePath M t k := clipped_rate_pos M t ht.le ℓ hℓ.1
  have hki : IntegrableOn k (Ioc 0 t) := hk.2.2.1
  have hkri := revenue_integrable M t k hk
  have hlri := revenue_integrable M t ℓ hℓ.1
  have hkmem : ∀ᵐ s ∂volume.restrict (Ioc 0 t), k s ∈ Icc 0 M.lstar := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact ⟨le_min (star_nonneg M) (M.nonneg _ (hℓ.1.2.1 s ⟨hs.1.le,hs.2⟩)),min_le_left _ _⟩
  have hj := (M.concaveOn.subset (interval_mem M) (convex_Icc _ _)).set_average_mem_hypograph
    (M.continuousOn.mono (interval_mem M)) isClosed_Icc
    (show volume (Ioc (0:ℝ) t) ≠ 0 by simp [Real.volume_Ioc,ht.ne',not_le.mpr ht])
    (show volume (Ioc (0:ℝ) t) ≠ ⊤ by simp [Real.volume_Ioc]) hkmem hki hkri
  change (⨍ s in Ioc (0:ℝ) t,k s) ∈ Icc 0 M.lstar ∧
    (⨍ s in Ioc (0:ℝ) t,M.r (k s)) ≤ M.r (⨍ s in Ioc (0:ℝ) t,k s) at hj
  have havg (f : ℝ → ℝ) : (⨍ s in Ioc (0:ℝ) t, f s) = (∫ s in Ioc (0:ℝ) t,f s)/t := by
    simp [setAverage_eq,measureReal_def,Real.volume_Ioc,ht.le,smul_eq_mul,div_eq_inv_mul]
  have hcons : (∫ s in Ioc (0:ℝ) t,k s) ≤ x := by
    calc _ ≤ ∫ s in Ioc (0:ℝ) t,ℓ s := integral_mono_ae hki hℓ.1.2.2.1
            (Filter.Eventually.of_forall fun s => min_le_right _ _)
         _ ≤ x := by simpa [intervalIntegral.integral_of_le ht.le] using hℓ.2
  have havle : (⨍ s in Ioc (0:ℝ) t,k s) ≤ min M.lstar (x/t) := by
    refine le_min hj.1.2 ?_
    rw [havg]
    exact div_le_div_of_nonneg_right hcons ht.le
  have hm := r_monotone M hj.1 (chosen_mem M x t hx ht) havle
  have hj' : (∫ s in Ioc (0:ℝ) t,M.r (k s)) ≤ t*M.r (min M.lstar (x/t)) := by
    have hh := hj.2.trans hm
    rw [havg] at hh
    have hh := (div_le_iff₀ ht).mp hh
    simpa [mul_comm] using hh
  rw [intervalIntegral.integral_of_le ht.le]
  apply le_trans (integral_mono_ae hlri hkri ?_) hj'
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact cap_improves M (hℓ.1.2.1 s ⟨hs.1.le,hs.2⟩)
#print axioms revenue_optimal
end Pricing

open MeasureTheory Set Function Classical
noncomputable section
namespace Pricing
open GVRPricing.FixedPrice

theorem value_eq (M : Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    detValue M x t = t*M.r (min M.lstar (x/t)) := by
  let V : Set ℝ := (fun ℓ : ℝ → ℝ => ∫ s in (0:ℝ)..t,M.r (ℓ s)) '' {ℓ | IsFeasiblePath M x t ℓ}
  have hc : t*M.r (min M.lstar (x/t)) ∈ V := by
    refine ⟨fun _ => min M.lstar (x/t),constant_feasible M x t hx ht,?_⟩
    simp
  have hb : ∀ y ∈ V, y ≤ t*M.r (min M.lstar (x/t)) := by
    rintro y ⟨ℓ,hℓ,rfl⟩
    exact revenue_optimal M x t hx ht ℓ hℓ
  exact le_antisymm (csSup_le ⟨_,hc⟩ hb) (le_csSup ⟨_,hb⟩ hc)

theorem pricing_price (M : Model) (x t : ℝ) (ht : 0 < t)
    (hs : 0 < M.lstar) (hx : 0 < x) (hΛ : x/t ∈ M.Λ) :
    M.p (min M.lstar (x/t)) = max M.pstar (M.p (x/t)) := by
  unfold Model.pstar
  have hstar : M.lstar ∈ M.Λ \ {0} := ⟨star_mem M,by simpa using hs.ne'⟩
  have hrun : x/t ∈ M.Λ \ {0} := ⟨hΛ,by simpa using (div_pos hx ht).ne'⟩
  rcases le_total M.lstar (x/t) with h|h
  · rw [min_eq_left h,max_eq_left (M.strictAntiOn.antitoneOn hstar hrun h)]
  · rw [min_eq_right h,max_eq_right (M.strictAntiOn.antitoneOn hrun hstar h)]

end Pricing

theorem prior_deterministic (M : GVRPricing.FixedPrice.Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    GVRPricing.FixedPrice.IsFeasiblePath M x t (fun _ => min M.lstar (x / t)) ∧
    (∀ ℓ : ℝ → ℝ, GVRPricing.FixedPrice.IsFeasiblePath M x t ℓ →
      ∫ s in (0 : ℝ)..t, M.r (ℓ s) ≤ ∫ s in (0 : ℝ)..t, M.r (min M.lstar (x / t))) ∧
    GVRPricing.FixedPrice.detValue M x t = t * M.r (min M.lstar (x / t)) ∧
    (x ≤ M.lstar * t → GVRPricing.FixedPrice.detValue M x t = t * min M.rstar (M.r (x / t))) ∧
    (M.lstar * t ≤ x → GVRPricing.FixedPrice.detValue M x t = t * M.rstar) ∧
    (0 < M.lstar → 0 < x → x / t ∈ M.Λ →
      M.p (min M.lstar (x / t)) = max M.pstar (M.p (x / t))) := by
  refine ⟨Pricing.constant_feasible M x t hx ht,?_,Pricing.value_eq M x t hx ht,?_,?_,
    Pricing.pricing_price M x t ht⟩
  · intro ℓ hℓ
    simpa using Pricing.revenue_optimal M x t hx ht ℓ hℓ
  · intro h
    have hr : x/t≤M.lstar := (div_le_iff₀ ht).mpr h
    have hm : x/t∈M.Λ := Pricing.interval_mem M ⟨div_nonneg hx ht.le,hr⟩
    rw [Pricing.value_eq M x t hx ht,min_eq_right hr,min_eq_right (Pricing.r_le_star M hm)]
  · intro h
    have hr : M.lstar≤x/t := (le_div_iff₀ ht).mpr h
    rw [Pricing.value_eq M x t hx ht,min_eq_left hr]
    rfl
#print axioms prior_deterministic

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

theorem constant_revenue (M : Model) (c : ℝ) (hc : c ∈ M.Λ) (hc0 : 0 < c) (n : ℕ) (t : ℝ)
    (ht : 0 ≤ t) :
    (constPolicy M c).expectedRevenue n t =
      ENNReal.ofReal (M.p c) *
        ∫⁻ k, ENNReal.ofReal ((k : ℝ) - max ((k : ℝ) - n) 0) ∂poissonMeasure (Real.toNNReal (c * t)) := by
  apply FixedClock.revenue_from_arrival_tails M c hc hc0
  intro j hj
  rw [FixedClock.arrival_poisson_tail (j+1) (c*t) (mul_nonneg hc0.le ht)]
  congr 1

#print axioms constant_revenue

open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace E7a4e382Aux

lemma key {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (C : ℝ) :
    ∫ ω, max (X ω - C) 0 ∂P ≤
        (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) / 2 := by
  set Y : Ω → ℝ := fun ω => X ω - C with hYdef
  have hY : MemLp Y 2 P := hX.sub (memLp_const C)
  have hXi : Integrable X P := hX.integrable one_le_two
  have hYi : Integrable Y P := hY.integrable one_le_two
  have hVY : variance Y P = variance X P :=
    variance_sub_const hX.aestronglyMeasurable C
  have hEY : ∫ ω, Y ω ∂P = (∫ ω, X ω ∂P) - C := by
    simp only [hYdef]
    rw [integral_sub hXi (integrable_const C), integral_const]
    simp
  set A : Ω → ℝ := fun ω => |Y ω| with hAdef
  have hA : MemLp A 2 P := hY.abs
  have hAi : Integrable A P := hA.integrable one_le_two
  have hA2 : (A ^ 2) = (Y ^ 2) := by
    funext ω; simp [hAdef, sq_abs]
  have hvarA := variance_nonneg A P
  rw [variance_eq_sub hA, hA2] at hvarA
  have hvarY := variance_eq_sub hY
  rw [hVY] at hvarY
  -- (E A)^2 ≤ E[Y^2] = Var X + (C - E X)^2
  have hsq : (∫ ω, A ω ∂P) ^ 2 ≤ variance X P + (C - ∫ ω, X ω ∂P) ^ 2 := by
    have h1 : P[Y ^ 2] = variance X P + (∫ ω, Y ω ∂P) ^ 2 := by linarith
    rw [hEY] at h1
    have h2 : (∫ ω, A ω ∂P) ^ 2 ≤ P[Y ^ 2] := by linarith
    calc (∫ ω, A ω ∂P) ^ 2 ≤ P[Y ^ 2] := h2
      _ = variance X P + (C - ∫ ω, X ω ∂P) ^ 2 := by rw [h1]; ring
  have hEA0 : 0 ≤ ∫ ω, A ω ∂P := integral_nonneg (fun ω => abs_nonneg _)
  have hEA : ∫ ω, A ω ∂P ≤ Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) :=
    Real.le_sqrt_of_sq_le hsq
  have hmax : (fun ω => max (X ω - C) 0) = fun ω => (Y ω + A ω) / 2 := by
    funext ω
    simp only [hAdef, hYdef]
    rcases le_total 0 (X ω - C) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  rw [hmax, integral_div, integral_add hYi hAi, hEY]
  linarith

end E7a4e382Aux

open MeasureTheory ProbabilityTheory in
theorem gallego_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (C : ℝ) :
    ∫ ω, max (X ω - C) 0 ∂P ≤
        (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) / 2 ∧
      (0 < ∫ ω, X ω ∂P → ∫ ω, X ω ∂P ≤ C →
        (∫ ω, max (X ω - C) 0 ∂P) / (∫ ω, X ω ∂P) ≤
            (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) /
              (2 * ∫ ω, X ω ∂P) ∧
          (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) /
              (2 * ∫ ω, X ω ∂P) ≤
            (Real.sqrt (variance X P) / ∫ ω, X ω ∂P) / 2) := by
  have hk := E7a4e382Aux.key P X hX C
  refine ⟨hk, fun hpos hle => ⟨?_, ?_⟩⟩
  · have h := div_le_div_of_nonneg_right hk hpos.le
    rwa [div_div] at h
  · set m := ∫ ω, X ω ∂P
    set V := variance X P
    have hV : 0 ≤ V := variance_nonneg X P
    have ha : 0 ≤ C - m := by linarith
    have hs : Real.sqrt (V + (C - m) ^ 2) ≤ Real.sqrt V + (C - m) := by
      have h0 := Real.sqrt_nonneg V
      have h1 := Real.sq_sqrt hV
      exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    rw [div_div, mul_comm m 2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace PricingPoisson

def weight (r : ℝ≥0) (n : ℕ) : ℝ := Real.exp (-r) * (r:ℝ)^n / n.factorial
lemma weight_succ (r : ℝ≥0) (k : ℕ) :
    weight r (k+1)*((k:ℝ)+1) = (r:ℝ)*weight r k := by
  unfold weight
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hk : (k.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring
lemma weight_two (r : ℝ≥0) (k : ℕ) :
    weight r (k+2)*((k:ℝ)+2)*((k:ℝ)+1) = (r:ℝ)^2*weight r k := by
  have h1 := weight_succ r (k+1)
  have h0 := weight_succ r k
  push_cast at h1
  calc
    _ = ((r:ℝ)*weight r (k+1))*((k:ℝ)+1) := by rw [show (k:ℝ)+2 = (k:ℝ)+1+1 by ring,h1]
    _ = (r:ℝ)*((r:ℝ)*weight r k) := by rw [mul_assoc,h0]
    _ = _ := by ring
lemma mean_series (r : ℝ≥0) : HasSum (fun k : ℕ => weight r k*(k:ℝ)) (r:ℝ) := by
  have hbase : HasSum (weight r) 1 := hasSum_one_poissonMeasure r
  have h : HasSum (fun k => (r:ℝ)*weight r k) (r:ℝ) := by
    simpa only [mul_one] using hbase.mul_left (r:ℝ)
  have hs : HasSum (fun k : ℕ => weight r (k+1)*((k+1:ℕ):ℝ)) (r:ℝ) := by
    convert h using 1
    funext k
    rw [Nat.cast_add,Nat.cast_one,weight_succ]
  have h' := (hasSum_nat_add_iff (f := fun k : ℕ => weight r k*(k:ℝ)) 1).mp hs
  simpa only [Finset.sum_range_one,Nat.cast_zero,mul_zero,add_zero] using h'
lemma factorial_series (r : ℝ≥0) :
    HasSum (fun k : ℕ => weight r k*(k:ℝ)*((k:ℝ)-1)) ((r:ℝ)^2) := by
  have hbase : HasSum (weight r) 1 := hasSum_one_poissonMeasure r
  have h : HasSum (fun k => (r:ℝ)^2*weight r k) ((r:ℝ)^2) := by
    simpa only [mul_one] using hbase.mul_left ((r:ℝ)^2)
  have hs : HasSum (fun k : ℕ => weight r (k+2)*((k+2:ℕ):ℝ)*(((k+2:ℕ):ℝ)-1)) ((r:ℝ)^2) := by
    convert h using 1
    funext k
    push_cast
    have he : (k:ℝ)+2-1 = (k:ℝ)+1 := by ring
    rw [he,weight_two]
  have h' := (hasSum_nat_add_iff
    (f := fun k : ℕ => weight r k*(k:ℝ)*((k:ℝ)-1)) 2).mp hs
  simpa [Finset.sum_range_succ] using h'
lemma square_series (r : ℝ≥0) : HasSum (fun k : ℕ => weight r k*(k:ℝ)^2) ((r:ℝ)^2+r) := by
  convert (factorial_series r).add (mean_series r) using 1
  funext k
  ring
lemma integrable_id (r : ℝ≥0) : Integrable (fun k : ℕ => (k:ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa [weight] using (mean_series r).summable
lemma integral_id (r : ℝ≥0) : (∫ k : ℕ, (k:ℝ) ∂poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  exact (mean_series r).tsum_eq
lemma integrable_square (r : ℝ≥0) : Integrable (fun k : ℕ => (k:ℝ)^2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa [weight] using (square_series r).summable
lemma integral_square (r : ℝ≥0) : (∫ k : ℕ, (k:ℝ)^2 ∂poissonMeasure r) = (r:ℝ)^2+r := by
  rw [integral_poissonMeasure]
  exact (square_series r).tsum_eq
lemma memLp_id (r : ℝ≥0) : MemLp (fun k : ℕ => (k:ℝ)) 2 (poissonMeasure r) := by
  exact (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).mpr
    (integrable_square r)
lemma variance_id (r : ℝ≥0) : variance (fun k : ℕ => (k:ℝ)) (poissonMeasure r) = r := by
  rw [variance_eq_sub (memLp_id r),integral_id]
  change (∫ k : ℕ, (k:ℝ)^2 ∂poissonMeasure r) - (r:ℝ)^2 = r
  rw [integral_square]
  ring
end PricingPoisson

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace PricingPoisson

lemma truncated_lower (r : ℝ≥0) (n : ℕ) :
    ENNReal.ofReal ((r:ℝ)-(Real.sqrt ((r:ℝ)+((n:ℝ)-r)^2)-((n:ℝ)-r))/2) ≤
      ∫⁻ k : ℕ, ENNReal.ofReal ((k:ℝ)-max ((k:ℝ)-n) 0) ∂poissonMeasure r := by
  have hi := integrable_id r
  have hs : Integrable (fun k : ℕ => max ((k:ℝ)-n) 0) (poissonMeasure r) :=
    (hi.sub (integrable_const _)).pos_part
  have ht : Integrable (fun k : ℕ => (k:ℝ)-max ((k:ℝ)-n) 0) (poissonMeasure r) := hi.sub hs
  have hnon (k : ℕ) : 0 ≤ (k:ℝ)-max ((k:ℝ)-n) 0 := by
    by_cases h : (n:ℝ) ≤ k
    · rw [max_eq_left (sub_nonneg.mpr h)]; nlinarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]
    · rw [max_eq_right (by linarith)]; simp
  rw [← ofReal_integral_eq_lintegral_ofReal ht (ae_of_all _ hnon)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_sub hi hs,integral_id]
  have h := (gallego_bound (poissonMeasure r) (fun k : ℕ => (k:ℝ)) (memLp_id r) (n:ℝ)).1
  rw [variance_id,integral_id] at h
  linarith

open GVRPricing.FixedPrice
lemma constant_lower (M : Model) (c : ℝ) (hc : c ∈ M.Λ) (hc0 : 0 < c)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (M.p c * (c*t-(Real.sqrt (c*t+((n:ℝ)-c*t)^2)-((n:ℝ)-c*t))/2)) ≤
      (constPolicy M c).expectedRevenue n t := by
  have hp : 0 ≤ M.p c := M.price_nonneg c hc hc0.ne'
  rw [constant_revenue M c hc hc0 n t ht,ENNReal.ofReal_mul hp]
  gcongr
  have h := truncated_lower (Real.toNNReal (c*t)) n
  simpa only [Real.coe_toNNReal _ (mul_nonneg hc0.le ht)] using h

end PricingPoisson

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
open GVRPricing.FixedPrice

theorem solution (M : Model) (n : ℕ) (t : ℝ) (ht : 0 < t) (hl : 0 < M.lstar)
    (h : M.lstar*t ≤ n) :
    ENNReal.ofReal (M.pstar * (M.lstar*t-
      (Real.sqrt (M.lstar*t+((n:ℝ)-M.lstar*t)^2)-((n:ℝ)-M.lstar*t))/2)) ≤ fpValue M n t ∧
    M.pstar*M.lstar*t*(1-1/(2*Real.sqrt (M.lstar*t))) ≤
      M.pstar*(M.lstar*t-(Real.sqrt (M.lstar*t+((n:ℝ)-M.lstar*t)^2)-((n:ℝ)-M.lstar*t))/2) ∧
    M.pstar*M.lstar*t*(1-1/(2*Real.sqrt (M.lstar*t))) =
      M.rstar*t*(1-1/(2*Real.sqrt (M.lstar*t))) := by
  have hp : 0 ≤ M.pstar := M.price_nonneg _ (Pricing.star_mem M) hl.ne'
  have ha : 0 < M.lstar*t := mul_pos hl ht
  have hs : 0 < Real.sqrt (M.lstar*t) := Real.sqrt_pos.mpr ha
  have hsq := Real.sq_sqrt ha.le
  refine ⟨?_,?_,?_⟩
  · unfold fpValue
    rw [min_eq_left ((le_div_iff₀ ht).mpr h)]
    exact PricingPoisson.constant_lower M M.lstar (Pricing.star_mem M) hl n t ht.le
  · have hroot : Real.sqrt (M.lstar*t+((n:ℝ)-M.lstar*t)^2) ≤
        Real.sqrt (M.lstar*t)+((n:ℝ)-M.lstar*t) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · exact add_nonneg hs.le (sub_nonneg.mpr h)
      · nlinarith [mul_nonneg hs.le (sub_nonneg.mpr h)]
    have halg : M.lstar*t*(1-1/(2*Real.sqrt (M.lstar*t))) =
        M.lstar*t-Real.sqrt (M.lstar*t)/2 := by
      field_simp
      nlinarith
    calc
      _ = M.pstar*(M.lstar*t*(1-1/(2*Real.sqrt (M.lstar*t)))) := by ring
      _ = M.pstar*(M.lstar*t-Real.sqrt (M.lstar*t)/2) := by rw [halg]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hp
  · unfold Model.rstar Model.pstar Model.r
    ring
