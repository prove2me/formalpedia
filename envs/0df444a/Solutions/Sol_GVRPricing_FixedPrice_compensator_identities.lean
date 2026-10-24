-- Prove2me | solution 1 for GVRPricing.FixedPrice.compensator_identities
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T01:12:42.403334+00:00
-- url     : https://prove2.me/submissions/b2c66c24-ff2b-48dc-8c0a-7cbf13413ff6

import Init
import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
lemma rate_measurable (j : ℕ) (τ : Fin j → ℝ) : Measurable (fun s => u.φ j s τ) :=
  (u.measurable j).comp (measurable_id.prodMk measurable_const)
lemma rate_nonneg (j : ℕ) (τ : Fin j → ℝ) (s : ℝ) : 0 ≤ u.φ j s τ :=
  M.nonneg _ (u.mem j s τ)
lemma rate_integrableOn (j : ℕ) (τ : Fin j → ℝ) (a b : ℝ) :
    IntegrableOn (fun s => u.φ j s τ) (Ioc a b) := by
  refine ⟨(rate_measurable u j τ).aestronglyMeasurable,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (rate_nonneg u j τ))).mpr
    (lt_top_iff_ne_top.mpr (u.locallyIntegrable j τ a b))
lemma rate_intervalIntegrable (j : ℕ) (τ : Fin j → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun s => u.φ j s τ) volume a b :=
  ⟨rate_integrableOn u j τ a b,rate_integrableOn u j τ b a⟩
lemma hazard_primitive (j : ℕ) (τ : Fin j → ℝ) (s : ℝ) :
    u.cumIntensity j τ s = ENNReal.ofReal (∫ v in lastTime j τ..max (lastTime j τ) s,
      u.φ j v τ) := by
  rw [intervalIntegral.integral_of_le (le_max_left _ _)]
  have he : Ioc (lastTime j τ) (max (lastTime j τ) s) = Ioc (lastTime j τ) s := by
    by_cases h : lastTime j τ ≤ s
    · rw [max_eq_right h]
    · rw [max_eq_left (le_of_not_ge h), Ioc_self, Ioc_eq_empty_of_le (le_of_not_ge h)]
  rw [he]
  exact (ofReal_integral_eq_lintegral_ofReal (rate_integrableOn u j τ _ _)
    (Eventually.of_forall (rate_nonneg u j τ))).symm
lemma hazard_continuous (j : ℕ) (τ : Fin j → ℝ) : Continuous (u.cumIntensity j τ) := by
  have he : u.cumIntensity j τ = (fun s => ENNReal.ofReal
      (∫ v in lastTime j τ..max (lastTime j τ) s, u.φ j v τ)) :=
    funext (hazard_primitive u j τ)
  rw [he]
  exact ENNReal.continuous_ofReal.comp
    ((intervalIntegral.continuous_primitive (rate_intervalIntegrable u j τ) _).comp
      (continuous_const.max continuous_id))
lemma hazard_mono (j : ℕ) (τ : Fin j → ℝ) : Monotone (u.cumIntensity j τ) := by
  intro s t hst
  exact lintegral_mono_set (Ioc_subset_Ioc_right hst)
lemma hazard_finite (j : ℕ) (τ : Fin j → ℝ) (s : ℝ) : u.cumIntensity j τ s ≠ ⊤ :=
  u.locallyIntegrable j τ _ s
lemma hazard_start (j : ℕ) (τ : Fin j → ℝ) : u.cumIntensity j τ (lastTime j τ) = 0 := by
  simp [Policy.cumIntensity]
lemma hitset_closed (j : ℕ) (τ : Fin j → ℝ) (e : ℝ) :
    IsClosed {s : ℝ | lastTime j τ ≤ s ∧ ENNReal.ofReal e ≤ u.cumIntensity j τ s} :=
  isClosed_Ici.inter (isClosed_le continuous_const (hazard_continuous u j τ))
lemma hitset_bddBelow (j : ℕ) (τ : Fin j → ℝ) (e : ℝ) :
    BddBelow {s : ℝ | lastTime j τ ≤ s ∧ ENNReal.ofReal e ≤ u.cumIntensity j τ s} :=
  ⟨lastTime j τ,fun _ h => h.1⟩
lemma nextSale_spec (j : ℕ) (τ : Fin j → ℝ) (e s : ℝ)
    (hs : u.nextSale j τ e = some s) :
    lastTime j τ ≤ s ∧ ENNReal.ofReal e ≤ u.cumIntensity j τ s := by
  unfold Policy.nextSale at hs
  split_ifs at hs with h
  · have he : sInf {x : ℝ | lastTime j τ ≤ x ∧ ENNReal.ofReal e ≤ u.cumIntensity j τ x} = s :=
      Option.some.inj hs
    rw [← he]
    exact (hitset_closed u j τ e).csInf_mem h (hitset_bddBelow u j τ e)
lemma nextSale_le_iff (j : ℕ) (τ : Fin j → ℝ) (e t : ℝ) (ht : lastTime j τ ≤ t) :
    (∃ s, u.nextSale j τ e = some s ∧ s ≤ t) ↔ ENNReal.ofReal e ≤ u.cumIntensity j τ t := by
  constructor
  · rintro ⟨s,hs,hst⟩
    exact (nextSale_spec u j τ e s hs).2.trans (hazard_mono u j τ hst)
  · intro he
    have hn : {s : ℝ | lastTime j τ ≤ s ∧ ENNReal.ofReal e ≤ u.cumIntensity j τ s}.Nonempty :=
      ⟨t,ht,he⟩
    refine ⟨_,?_,csInf_le (hitset_bddBelow u j τ e) ⟨ht,he⟩⟩
    simp [Policy.nextSale,hn]
#print axioms hazard_continuous
#print axioms nextSale_le_iff
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
lemma nextSale_event (j : ℕ) (τ : Fin j → ℝ) (t : ℝ) (ht : lastTime j τ ≤ t) :
    {e : ℝ | ∃ s, u.nextSale j τ e = some s ∧ s ≤ t} =
      Iic (u.cumIntensity j τ t).toReal := by
  ext e
  exact (nextSale_le_iff u j τ e t ht).trans
    (ENNReal.ofReal_le_iff_le_toReal (hazard_finite u j τ t))
lemma exponential_cdf (x : ℝ) (hx : 0 ≤ x) :
    expMeasure 1 (Iic x) = ENNReal.ofReal (1-Real.exp (-x)) := by
  rw [expMeasure,gammaMeasure,withDensity_apply _ measurableSet_Iic]
  change (∫⁻ y in Iic x, exponentialPDF 1 y) = _
  rw [lintegral_exponentialPDF_eq_antiDeriv (by norm_num)]
  simp [hx]
theorem nextSale_probability (j : ℕ) (τ : Fin j → ℝ) (t : ℝ) (ht : lastTime j τ ≤ t) :
    expMeasure 1 {e : ℝ | ∃ s, u.nextSale j τ e = some s ∧ s ≤ t} =
      ENNReal.ofReal (1-Real.exp (-(u.cumIntensity j τ t).toReal)) := by
  rw [nextSale_event u j τ t ht]
  exact exponential_cdf _ ENNReal.toReal_nonneg
lemma lastTime_measurable (j : ℕ) : Measurable (lastTime j) := by
  cases j with
  | zero => exact measurable_const
  | succ j => exact measurable_pi_apply _
lemma hazard_joint_measurable (j : ℕ) :
    Measurable (fun q : (Fin j → ℝ) × ℝ => u.cumIntensity j q.1 q.2) := by
  have hm : Measurable (fun p : ((Fin j → ℝ) × ℝ) × ℝ =>
      if lastTime j p.1.1 < p.2 ∧ p.2 ≤ p.1.2 then ENNReal.ofReal (u.φ j p.2 p.1.1) else 0) := by
    apply Measurable.ite
    · exact (measurableSet_lt ((lastTime_measurable j).comp measurable_fst.fst) measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst.snd)
    · exact ((u.measurable j).comp (measurable_snd.prodMk measurable_fst.fst)).ennreal_ofReal
    · exact measurable_const
  convert! (Measurable.lintegral_prod_right (ν := volume) (f := fun (q : (Fin j → ℝ) × ℝ) (v : ℝ) =>
    if lastTime j q.1 < v ∧ v ≤ q.2 then ENNReal.ofReal (u.φ j v q.1) else 0) hm) using 1
  ext q
  rw [Policy.cumIntensity,← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro v
  simp [Set.indicator_apply, mem_Ioc]
#print axioms nextSale_probability
#print axioms hazard_joint_measurable
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
lemma nextSale_minimal (j : ℕ) (τ : Fin j → ℝ) (e s t : ℝ)
    (hs : u.nextSale j τ e = some s) (ht : lastTime j τ ≤ t)
    (he : ENNReal.ofReal e ≤ u.cumIntensity j τ t) : s ≤ t := by
  obtain ⟨z,hz,hzt⟩ := (nextSale_le_iff u j τ e t ht).mpr he
  have : s = z := Option.some.inj (hs.symm.trans hz)
  simpa [this] using hzt
lemma hazard_at_sale (j : ℕ) (τ : Fin j → ℝ) (e s : ℝ)
    (hs : u.nextSale j τ e = some s) : u.cumIntensity j τ s = ENNReal.ofReal e := by
  have hspec := nextSale_spec u j τ e s hs
  have he : ENNReal.ofReal e ∈ Icc (u.cumIntensity j τ (lastTime j τ)) (u.cumIntensity j τ s) := by
    rw [hazard_start]
    exact ⟨zero_le,hspec.2⟩
  obtain ⟨x,hx,hxe⟩ := intermediate_value_Icc hspec.1 (hazard_continuous u j τ).continuousOn he
  have hmin := nextSale_minimal u j τ e s x hs hx.1 (le_of_eq hxe.symm)
  have : x = s := le_antisymm hx.2 hmin
  simpa [this] using hxe
lemma stopped_hazard (j : ℕ) (τ : Fin j → ℝ) (e s t : ℝ)
    (hs : u.nextSale j τ e = some s) :
    u.cumIntensity j τ (min s t) = min (ENNReal.ofReal e) (u.cumIntensity j τ t) := by
  rw [(hazard_mono u j τ).map_min, hazard_at_sale u j τ e s hs]
lemma no_sale_bound (j : ℕ) (τ : Fin j → ℝ) (e t : ℝ)
    (hn : u.nextSale j τ e = none) (ht : lastTime j τ ≤ t) :
    u.cumIntensity j τ t < ENNReal.ofReal e := by
  apply lt_of_not_ge
  intro he
  obtain ⟨s,hs,_⟩ := (nextSale_le_iff u j τ e t ht).mpr he
  rw [hn] at hs
  cases hs
#print axioms hazard_at_sale
#print axioms stopped_hazard
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
def nextTime (j : ℕ) (τ : Fin j → ℝ) (e : ℝ) : WithTop ℝ :=
  (u.nextSale j τ e).elim ⊤ (fun s => (s : WithTop ℝ))
lemma nextTime_le_iff (j : ℕ) (τ : Fin j → ℝ) (e t : ℝ) :
    nextTime u j τ e ≤ (t : WithTop ℝ) ↔
      lastTime j τ ≤ t ∧ ENNReal.ofReal e ≤ u.cumIntensity j τ t := by
  constructor
  · intro h
    cases he : u.nextSale j τ e with
    | none => simp [nextTime,he] at h
    | some s =>
      have hst : s ≤ t := by simpa [nextTime,he] using h
      exact ⟨(nextSale_spec u j τ e s he).1.trans hst,
        (nextSale_spec u j τ e s he).2.trans (hazard_mono u j τ hst)⟩
  · rintro ⟨ha,he⟩
    obtain ⟨s,hs,hst⟩ := (nextSale_le_iff u j τ e t ha).mpr he
    simpa [nextTime,hs] using hst
lemma nextTime_measurable (j : ℕ) :
    Measurable (fun p : (Fin j → ℝ) × ℝ => nextTime u j p.1 p.2) := by
  apply measurable_of_Iic
  intro x
  cases x with
  | top => simpa using (MeasurableSet.univ : MeasurableSet (Set.univ : Set ((Fin j → ℝ) × ℝ)))
  | coe t =>
    have hm := (measurableSet_le ((lastTime_measurable j).comp measurable_fst) (measurable_const (a := t))).inter
      (measurableSet_le measurable_snd.ennreal_ofReal
        ((hazard_joint_measurable u j).comp (measurable_fst.prodMk (measurable_const (a := t)))))
    convert! hm using 1
    ext p
    exact nextTime_le_iff u j p.1 p.2 t
lemma stopped_intensity (j : ℕ) (τ : Fin j → ℝ) (e t : ℝ) (ht : lastTime j τ ≤ t) :
    (∫⁻ v in Ioc (lastTime j τ) t,
      if (v : WithTop ℝ) ≤ nextTime u j τ e then ENNReal.ofReal (u.φ j v τ) else 0) =
      min (ENNReal.ofReal e) (u.cumIntensity j τ t) := by
  cases he : u.nextSale j τ e with
  | none =>
    simp only [nextTime,he,Option.elim_none,le_top,ite_true]
    exact (min_eq_right (no_sale_bound u j τ e t he ht).le).symm
  | some s =>
    simp only [nextTime,he,Option.elim_some,WithTop.coe_le_coe]
    change (∫⁻ v in Ioc (lastTime j τ) t,
      (Iic s).indicator (fun v => ENNReal.ofReal (u.φ j v τ)) v) = _
    rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hset : Iic s ∩ Ioc (lastTime j τ) t = Ioc (lastTime j τ) (min s t) := by
      ext v
      simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]
      tauto
    rw [hset]
    exact stopped_hazard u j τ e s t he
#print axioms nextTime_measurable
#print axioms stopped_intensity
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace AdaptiveClock
lemma exponential_tail (s : ℝ) (hs : 0 ≤ s) :
    expMeasure 1 (Ioi s) = ENNReal.ofReal (Real.exp (-s)) := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  rw [← compl_Iic,measure_compl measurableSet_Iic (measure_ne_top _ _),measure_univ,
    exponential_cdf s hs]
  have he : Real.exp (-s) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hs)
  rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 (sub_nonneg.mpr he)]
  congr 1
  ring
lemma truncated_exponential_mean (x : ℝ) (hx : 0 ≤ x) :
    (∫⁻ e, min (ENNReal.ofReal e) (ENNReal.ofReal x) ∂expMeasure 1) =
      ENNReal.ofReal (1 - Real.exp (-x)) := by
  have hf : Measurable (fun e : ℝ => min (max 0 e) x) :=
    (measurable_const.max measurable_id).min measurable_const
  have hn : ∀ e : ℝ, 0 ≤ min (max 0 e) x := fun e => le_min (le_max_left _ _) hx
  have heq : ∀ e : ℝ, min (ENNReal.ofReal e) (ENNReal.ofReal x) =
      ENNReal.ofReal (min (max 0 e) x) := by
    intro e
    simp [ENNReal.ofReal_min,ENNReal.ofReal_max]
  simp_rw [heq]
  rw [lintegral_eq_lintegral_meas_lt (expMeasure 1) (Eventually.of_forall hn) hf.aemeasurable]
  have hi : (∫⁻ s in Ioi 0, expMeasure 1 {e : ℝ | s < min (max 0 e) x}) =
      ∫⁻ s in Ioi 0, (Iio x).indicator (fun s => ENNReal.ofReal (Real.exp (-s))) s := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    by_cases hxs : s < x
    · have hset : {e : ℝ | s < min (max 0 e) x} = Ioi s := by
        ext e
        simp only [mem_setOf_eq,lt_min_iff,lt_max_iff,mem_Ioi]
        exact ⟨fun h => h.1.resolve_left (not_lt_of_ge hs.le),fun h => ⟨Or.inr h,hxs⟩⟩
      rw [hset,indicator_of_mem (show s ∈ Iio x from hxs),exponential_tail s hs.le]
    · have hset : {e : ℝ | s < min (max 0 e) x} = ∅ := by
        ext e
        simp only [mem_setOf_eq,lt_min_iff,mem_empty_iff_false,iff_false,not_and]
        exact fun _ => hxs
      rw [hset,measure_empty,indicator_of_notMem (show s ∉ Iio x from hxs)]
  rw [hi,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio x ∩ Ioi (0 : ℝ) = Ioo 0 x := by ext s; simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo]; tauto
  rw [hset,restrict_Ioo_eq_restrict_Ioc]
  have hp : (∫⁻ s in Ioc 0 x, ENNReal.ofReal (Real.exp (-s))) =
      ∫⁻ s in Ioc 0 x, exponentialPDF 1 s := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp [exponentialPDF_of_nonneg hs.1.le]
  rw [hp,restrict_Ioc_eq_restrict_Icc]
  have h := lintegral_exponentialPDF_eq_antiDeriv (r := 1) (by norm_num) x
  rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ hx,
    lintegral_exponentialPDF_of_nonpos (le_refl 0),zero_add] at h
  simpa [hx] using h
#print axioms truncated_exponential_mean
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
theorem conditional_sales_compensator (j : ℕ) (τ : Fin j → ℝ) (t : ℝ)
    (ht : lastTime j τ ≤ t) :
    expMeasure 1 {e : ℝ | ∃ s, u.nextSale j τ e = some s ∧ s ≤ t} =
      ∫⁻ e, (∫⁻ v in Ioc (lastTime j τ) t,
        if (v : WithTop ℝ) ≤ nextTime u j τ e then ENNReal.ofReal (u.φ j v τ) else 0)
        ∂expMeasure 1 := by
  rw [nextSale_probability u j τ t ht]
  simp_rw [stopped_intensity u j τ _ t ht]
  have he := truncated_exponential_mean (u.cumIntensity j τ t).toReal ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal (hazard_finite u j τ t)] at he
  exact he.symm
#print axioms conditional_sales_compensator
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
def histVec (E : ℕ → ℝ) (j : ℕ) : Fin j → ℝ := (u.history E j).getD 0
lemma history_congr (j : ℕ) (E F : ℕ → ℝ) (he : ∀ k < j, E k = F k) :
    u.history E j = u.history F j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Policy.history,ih (fun k hk => he k (by omega)),he j (by omega)]
lemma history_step (E : ℕ → ℝ) (j : ℕ) :
    u.history E (j+1) = (u.history E j).bind (fun τ =>
      (u.nextSale j τ (E j)).map fun s => Fin.snoc (α := fun _ => ℝ) τ s) := rfl
lemma alive_step (E : ℕ → ℝ) (j : ℕ) :
    u.history E (j+1) ≠ none ↔ u.history E j ≠ none ∧ nextTime u j (histVec u E j) (E j) ≠ ⊤ := by
  cases h : u.history E j with
  | none => simp [history_step,h]
  | some τ =>
    cases hnext : u.nextSale j τ (E j) with
    | none => simp [history_step,h,histVec,nextTime,hnext]
    | some s => simp [history_step,h,histVec,nextTime,hnext]
lemma histVec_step (E : ℕ → ℝ) (j : ℕ) :
    histVec u E (j+1) = if u.history E (j+1) ≠ none then
      Fin.snoc (α := fun _ => ℝ) (histVec u E j)
        ((nextTime u j (histVec u E j) (E j)).untopD 0) else 0 := by
  classical
  cases h : u.history E j with
  | none => simp [histVec,history_step,h]
  | some τ =>
    cases hnext : u.nextSale j τ (E j) with
    | none => simp [histVec,history_step,h,nextTime,hnext]
    | some s => simp [histVec,history_step,h,nextTime,hnext]
lemma history_measurable (j : ℕ) :
    MeasurableSet {E : ℕ → ℝ | u.history E j ≠ none} ∧ Measurable (fun E : ℕ → ℝ => histVec u E j) := by
  classical
  induction j with
  | zero => simp only [Policy.history,ne_eq,reduceCtorEq,not_false_eq_true,ofPred_true]; exact ⟨MeasurableSet.univ,measurable_const⟩
  | succ j ih =>
    have ht : Measurable (fun E : ℕ → ℝ => nextTime u j (histVec u E j) (E j)) :=
      (nextTime_measurable u j).comp (ih.2.prodMk (measurable_pi_apply j))
    have hn : MeasurableSet {E : ℕ → ℝ | u.history E (j+1) ≠ none} := by
      simp_rw [alive_step]
      exact ih.1.inter (measurableSet_eq_fun ht measurable_const).compl
    refine ⟨hn,?_⟩
    simp_rw [histVec_step]
    apply Measurable.ite hn ?_ measurable_const
    apply measurable_pi_lambda
    intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simpa using ht.untopD (0 : ℝ)
    · simpa [Function.comp_def] using (measurable_pi_apply k).comp ih.2
lemma next_saleTime (E : ℕ → ℝ) (j : ℕ) (τ : Fin j → ℝ) (hh : u.history E j = some τ) :
    u.saleTime E (j+1) = nextTime u j τ (E j) := by
  cases hn : u.nextSale j τ (E j) with
  | none => simp [Policy.saleTime,Policy.history,hh,hn,nextTime]
  | some s => simp [Policy.saleTime,Policy.history,hh,hn,nextTime,lastTime]
lemma saleTime_measurable (j : ℕ) : Measurable (fun E : ℕ → ℝ => u.saleTime E j) := by
  classical
  have he (E : ℕ → ℝ) : u.saleTime E j = if u.history E j ≠ none then
      ((lastTime j (histVec u E j) : ℝ) : WithTop ℝ) else ⊤ := by
    cases h : u.history E j <;> simp [Policy.saleTime,h,histVec]
  simp_rw [he]
  exact Measurable.ite (history_measurable u j).1
    (((lastTime_measurable j).comp (history_measurable u j).2).withTop_coe) measurable_const
#print axioms history_congr
#print axioms history_measurable
#print axioms saleTime_measurable
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdaptiveClock
open GVRPricing.FixedPrice
instance expClockProbability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)
instance clockProbability : IsProbabilityMeasure clockLaw := by unfold clockLaw; infer_instance
variable {M : Model} (u : Policy M)
def past (j : ℕ) (E : ℕ → ℝ) : Fin j → ℝ := fun k => E k
private def extendPast (j : ℕ) (x : Fin j → ℝ) : ℕ → ℝ :=
  fun k => if h : k < j then x ⟨k,h⟩ else 0
private lemma extendPast_measurable (j : ℕ) : Measurable (extendPast j) := by
  apply measurable_pi_lambda
  intro k
  by_cases h : k < j
  · simpa only [extendPast,dif_pos h] using (measurable_pi_apply (⟨k,h⟩ : Fin j))
  · simp only [extendPast,dif_neg h]; exact measurable_const
lemma past_independent_clock (j : ℕ) : IndepFun (past j) (fun E : ℕ → ℝ => E j) clockLaw := by
  have hd : Disjoint (Finset.range j) ({j} : Finset ℕ) := by simp
  have hi : iIndepFun (fun k (E : ℕ → ℝ) => E k) clockLaw :=
    iIndepFun_infinitePi (X := fun (_ : ℕ) (x : ℝ) => x) (fun _ => measurable_id)
  have h := iIndepFun.indepFun_finset (Finset.range j) {j} hd hi (fun k => measurable_pi_apply k)
  have hleft : Measurable (fun x : (Finset.range j) → ℝ => fun k : Fin j => x ⟨k,by simpa using k.isLt⟩) := by fun_prop
  have hright : Measurable (fun x : ({j} : Finset ℕ) → ℝ => x ⟨j,by simp⟩) := by fun_prop
  unfold past
  exact h.comp hleft hright
open Classical in
def historyData (j : ℕ) (E : ℕ → ℝ) : Bool × (Fin j → ℝ) :=
  (if u.history E j ≠ none then true else false, histVec u E j)
lemma historyData_measurable (j : ℕ) : Measurable (historyData u j) := by
  classical
  exact (Measurable.ite (history_measurable u j).1 measurable_const measurable_const).prodMk
    (history_measurable u j).2
lemma historyData_restrict (j : ℕ) (E : ℕ → ℝ) :
    historyData u j (extendPast j (past j E)) = historyData u j E := by
  have hh := history_congr u j (extendPast j (past j E)) E (by intro k hk; simp [extendPast,past,hk])
  simp only [historyData,histVec,hh]
lemma history_independent_clock (j : ℕ) :
    IndepFun (historyData u j) (fun E : ℕ → ℝ => E j) clockLaw := by
  have h := (past_independent_clock j).comp
    ((historyData_measurable u j).comp (extendPast_measurable j)) measurable_id
  simpa [Function.comp_def,historyData_restrict] using h
lemma history_clock_lintegral (j : ℕ) (g : (Bool × (Fin j → ℝ)) × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ E, g (historyData u j E,E j) ∂clockLaw) =
      ∫⁻ a, ∫⁻ e, g (a,e) ∂expMeasure 1 ∂(clockLaw.map (historyData u j)) := by
  have hm := (history_independent_clock u j).map_prod_eq_prod_map_map
    (historyData_measurable u j).aemeasurable (measurable_pi_apply j).aemeasurable
  have he : clockLaw.map (fun E : ℕ → ℝ => E j) = expMeasure 1 :=
    Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) j
  rw [he] at hm
  rw [← lintegral_map hg ((historyData_measurable u j).prodMk (measurable_pi_apply j)),hm]
  exact lintegral_prod _ hg.aemeasurable
#print axioms history_independent_clock
#print axioms history_clock_lintegral
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
open Classical in
def saleStep (j : ℕ) (t : ℝ) (a : Bool × (Fin j → ℝ)) (e : ℝ) : ℝ≥0∞ :=
  if a.1 = true ∧ nextTime u j a.2 e ≤ (t : WithTop ℝ) then 1 else 0
open Classical in
def hazardStep (j : ℕ) (t : ℝ) (a : Bool × (Fin j → ℝ)) (e : ℝ) : ℝ≥0∞ :=
  if a.1 = true then min (ENNReal.ofReal e) (u.cumIntensity j a.2 t) else 0
lemma saleStep_measurable (j : ℕ) (t : ℝ) :
    Measurable (fun p : (Bool × (Fin j → ℝ)) × ℝ => saleStep u j t p.1 p.2) := by
  classical
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_eq_fun measurable_fst.fst measurable_const).inter
    (measurableSet_le ((nextTime_measurable u j).comp (measurable_fst.snd.prodMk measurable_snd)) measurable_const)
lemma hazardStep_measurable (j : ℕ) (t : ℝ) :
    Measurable (fun p : (Bool × (Fin j → ℝ)) × ℝ => hazardStep u j t p.1 p.2) := by
  classical
  exact Measurable.ite (measurableSet_eq_fun measurable_fst.fst measurable_const)
    (measurable_snd.ennreal_ofReal.min ((hazard_joint_measurable u j).comp
      (measurable_fst.snd.prodMk (measurable_const (a := t))))) measurable_const
lemma conditional_step (j : ℕ) (t : ℝ) (a : Bool × (Fin j → ℝ)) :
    (∫⁻ e, saleStep u j t a e ∂expMeasure 1) =
      ∫⁻ e, hazardStep u j t a e ∂expMeasure 1 := by
  classical
  rcases a with ⟨b,τ⟩
  cases b
  · simp [saleStep,hazardStep]
  · simp only [saleStep,hazardStep,Bool.true_eq, true_and,ite_true]
    by_cases ht : lastTime j τ ≤ t
    · have hevent : {e : ℝ | nextTime u j τ e ≤ (t : WithTop ℝ)} =
          {e : ℝ | ∃ s, u.nextSale j τ e = some s ∧ s ≤ t} := by
        ext e
        cases hn : u.nextSale j τ e <;> simp [nextTime,hn]
      have hmeas : MeasurableSet {e : ℝ | nextTime u j τ e ≤ (t : WithTop ℝ)} :=
        measurableSet_le ((nextTime_measurable u j).comp (measurable_const.prodMk measurable_id)) measurable_const
      have hi : (∫⁻ e, if nextTime u j τ e ≤ (t : WithTop ℝ) then (1 : ℝ≥0∞) else 0 ∂expMeasure 1) =
          expMeasure 1 {e : ℝ | nextTime u j τ e ≤ (t : WithTop ℝ)} := by
        simpa only [Set.indicator_apply,Pi.one_apply,Set.mem_setOf_eq] using lintegral_indicator_one hmeas
      rw [hi,hevent,nextSale_probability u j τ t ht]
      have h := truncated_exponential_mean (u.cumIntensity j τ t).toReal ENNReal.toReal_nonneg
      rw [ENNReal.ofReal_toReal (hazard_finite u j τ t)] at h
      exact h.symm
    · have he : ∀ e, ¬ nextTime u j τ e ≤ (t : WithTop ℝ) := fun e he => ht ((nextTime_le_iff u j τ e t).mp he).1
      have hz : u.cumIntensity j τ t = 0 := by simp [Policy.cumIntensity,Ioc_eq_empty (not_lt.mpr (le_of_not_ge ht))]
      simp [he,hz]
lemma saleStep_eq (j : ℕ) (t : ℝ) (E : ℕ → ℝ) :
    saleStep u j t (historyData u j E) (E j) =
      if u.saleTime E (j+1) ≤ (t : WithTop ℝ) then 1 else 0 := by
  classical
  cases hh : u.history E j with
  | none => simp [saleStep,historyData,hh,Policy.saleTime,Policy.history]
  | some τ => rw [next_saleTime u E j τ hh]; simp [saleStep,historyData,histVec,hh]
lemma adaptive_stage_compensation (j : ℕ) (t : ℝ) :
    (∫⁻ E, (if u.saleTime E (j+1) ≤ (t : WithTop ℝ) then 1 else 0 : ℝ≥0∞) ∂clockLaw) =
      ∫⁻ E, hazardStep u j t (historyData u j E) (E j) ∂clockLaw := by
  simp_rw [←saleStep_eq u j t]
  rw [history_clock_lintegral u j _ (saleStep_measurable u j t),
    history_clock_lintegral u j _ (hazardStep_measurable u j t)]
  apply lintegral_congr
  intro a
  exact conditional_step u j t a
#print axioms conditional_step
#print axioms adaptive_stage_compensation
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
lemma history_last_nonneg (E : ℕ → ℝ) (j : ℕ) (τ : Fin j → ℝ)
    (hh : u.history E j = some τ) : 0 ≤ lastTime j τ := by
  induction j with
  | zero => exact le_refl _
  | succ j ih =>
    cases hp : u.history E j with
    | none => simp [Policy.history,hp] at hh
    | some σ =>
      cases hn : u.nextSale j σ (E j) with
      | none => simp [Policy.history,hp,hn] at hh
      | some s =>
        have he : Fin.snoc (α := fun _ => ℝ) σ s = τ := by simpa [Policy.history,hp,hn] using hh
        rw [←he]
        simpa [lastTime] using (ih σ hp).trans (nextSale_spec u j σ (E j) s hn).1
open Classical in
def stageRate (j : ℕ) (E : ℕ → ℝ) (s : ℝ) : ℝ :=
  (u.history E j).elim 0 fun τ =>
    if lastTime j τ < s ∧ (s : WithTop ℝ) ≤ u.saleTime E (j+1) then u.φ j s τ else 0
lemma stageRate_nonneg (j : ℕ) (E : ℕ → ℝ) (s : ℝ) : 0 ≤ stageRate u j E s := by
  classical
  cases hh : u.history E j with
  | none => simp [stageRate,hh]
  | some τ => simp only [stageRate,hh,Option.elim_some]; split_ifs; exact rate_nonneg u j τ s; rfl
lemma stageRate_measurable (j : ℕ) (E : ℕ → ℝ) : Measurable (stageRate u j E) := by
  classical
  unfold stageRate
  cases hh : u.history E j with
  | none => simp only [hh,Option.elim_none]; exact measurable_const
  | some τ =>
    simp only [hh,Option.elim_some]
    exact Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id.withTop_coe measurable_const))
      ((u.measurable j).comp (measurable_id.prodMk measurable_const)) measurable_const
lemma stopped_intensity_all (j : ℕ) (τ : Fin j → ℝ) (e t : ℝ) :
    (∫⁻ s in Ioc (lastTime j τ) t,
      if (s : WithTop ℝ) ≤ nextTime u j τ e then ENNReal.ofReal (u.φ j s τ) else 0) =
      min (ENNReal.ofReal e) (u.cumIntensity j τ t) := by
  by_cases ht : lastTime j τ ≤ t
  · exact stopped_intensity u j τ e t ht
  · simp [Policy.cumIntensity,Ioc_eq_empty (not_lt.mpr (le_of_not_ge ht))]
lemma stageRate_integral (j : ℕ) (E : ℕ → ℝ) (t : ℝ) :
    (∫⁻ s in Ioc 0 t, ENNReal.ofReal (stageRate u j E s)) =
      hazardStep u j t (historyData u j E) (E j) := by
  classical
  cases hh : u.history E j with
  | none => simp [stageRate,hazardStep,historyData,hh]
  | some τ =>
    have ht := history_last_nonneg u E j τ hh
    simp only [stageRate,hh,Option.elim_some]
    rw [next_saleTime u E j τ hh]
    simp only [hazardStep,historyData,histVec,hh,reduceCtorEq,not_false_eq_true,ite_true,
      Option.getD_some,Bool.true_eq,ite_true]
    calc
      _ = ∫⁻ s in Ioc 0 t, (Ioi (lastTime j τ)).indicator
          (fun s => if (s : WithTop ℝ) ≤ nextTime u j τ (E j) then ENNReal.ofReal (u.φ j s τ) else 0) s := by
        apply lintegral_congr
        intro s
        by_cases h : lastTime j τ < s <;> by_cases hn : (s : WithTop ℝ) ≤ nextTime u j τ (E j) <;>
          simp [Set.indicator_apply,h,hn]
      _ = ∫⁻ s in Ioc (lastTime j τ) t,
          if (s : WithTop ℝ) ≤ nextTime u j τ (E j) then ENNReal.ofReal (u.φ j s τ) else 0 := by
        rw [lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
        have he : Ioi (lastTime j τ) ∩ Ioc 0 t = Ioc (lastTime j τ) t := by
          ext s
          simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
          exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,ht.trans_lt h.1,h.2⟩⟩
        rw [he]
      _ = _ := stopped_intensity_all u j τ (E j) t
#print axioms stageRate_integral
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
lemma sales_count_sum (n : ℕ) (t : ℝ) (E : ℕ → ℝ) :
    (u.salesBy n t E : ℝ≥0∞) =
      ∑ j ∈ Finset.range n, if u.saleTime E (j+1) ≤ (t : WithTop ℝ) then 1 else 0 := by
  classical
  unfold Policy.salesBy
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp
lemma expectedSales_sum (n : ℕ) (t : ℝ) :
    u.expectedSales n t = ∑ j ∈ Finset.range n,
      ∫⁻ E, (if u.saleTime E (j+1) ≤ (t : WithTop ℝ) then 1 else 0 : ℝ≥0∞) ∂clockLaw := by
  classical
  unfold Policy.expectedSales
  simp_rw [sales_count_sum]
  apply lintegral_finsetSum
  intro j hj
  exact Measurable.ite (measurableSet_le (saleTime_measurable u (j+1)) measurable_const)
    measurable_const measurable_const
lemma expectedIntensity_sum (n : ℕ) (t : ℝ) :
    u.expectedCumIntensity n t = ∑ j ∈ Finset.range n,
      ∫⁻ E, hazardStep u j t (historyData u j E) (E j) ∂clockLaw := by
  classical
  have he (E : ℕ → ℝ) : (∫⁻ s in Ioc 0 t, ENNReal.ofReal (u.intensityAt n E s)) =
      ∑ j ∈ Finset.range n, ∫⁻ s in Ioc 0 t, ENNReal.ofReal (stageRate u j E s) := by
    change (∫⁻ s in Ioc 0 t, ENNReal.ofReal (∑ j ∈ Finset.range n,stageRate u j E s)) = _
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => stageRate_nonneg u j E _)]
    apply lintegral_finsetSum
    intro j hj
    exact (stageRate_measurable u j E).ennreal_ofReal
  unfold Policy.expectedCumIntensity
  simp_rw [he,stageRate_integral]
  apply lintegral_finsetSum
  intro j hj
  exact (hazardStep_measurable u j t).comp ((historyData_measurable u j).prodMk (measurable_pi_apply j))
theorem sales_compensator (n : ℕ) (t : ℝ) : u.expectedSales n t = u.expectedCumIntensity n t := by
  rw [expectedSales_sum,expectedIntensity_sum]
  exact Finset.sum_congr rfl (fun j hj => adaptive_stage_compensation u j t)
lemma expectedSales_le_stock (n : ℕ) (t : ℝ) : u.expectedSales n t ≤ n := by
  have hn (E : ℕ → ℝ) : u.salesBy n t E ≤ n := by
    unfold Policy.salesBy
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)
  calc
    _ ≤ ∫⁻ _E : ℕ → ℝ, (n : ℝ≥0∞) ∂clockLaw := lintegral_mono (fun E => Nat.cast_le.mpr (hn E))
    _ = _ := by simp
theorem sales_compensator_and_bound (n : ℕ) (t : ℝ) :
    u.expectedSales n t = u.expectedCumIntensity n t ∧ u.expectedCumIntensity n t ≤ n :=
  ⟨sales_compensator u n t,(sales_compensator u n t).symm.le.trans (expectedSales_le_stock u n t)⟩
#print axioms sales_compensator_and_bound
end AdaptiveClock

open MeasureTheory Set
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MarkedClock
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable (T : Ω → WithTop ℝ)
def saleMeasure : Measure ℝ :=
  (μ.restrict {ω | T ω ≠ ⊤}).map (fun ω => (T ω).untopD 0)

instance finite_saleMeasure : IsFiniteMeasure (saleMeasure μ T) := by
  unfold saleMeasure
  infer_instance

theorem saleMeasure_Iic (hT : Measurable T) (t : ℝ) :
    saleMeasure μ T (Iic t) = μ {ω | T ω ≤ (t : WithTop ℝ)} := by
  rw [saleMeasure,Measure.map_apply (hT.untopD 0) measurableSet_Iic,
    Measure.restrict_apply ((hT.untopD 0) measurableSet_Iic)]
  congr 1
  ext ω
  cases h : T ω <;> simp [h]

theorem measure_eq_of_cdf (hT : Measurable T) (q : Ω × ℝ → ℝ≥0∞)
    (hq : Measurable q)
    (hcdf : ∀ t : ℝ, μ {ω | T ω ≤ (t : WithTop ℝ)} =
      ∫⁻ ω, ∫⁻ s in Iic t, q (ω,s) ∂volume ∂μ) :
    saleMeasure μ T = volume.withDensity (fun s => ∫⁻ ω, q (ω,s) ∂μ) := by
  apply Measure.ext_of_Iic
  intro t
  rw [saleMeasure_Iic μ T hT t,hcdf,withDensity_apply _ measurableSet_Iic]
  exact lintegral_lintegral_swap hq.aemeasurable

theorem marked_identity (hT : Measurable T) (q : Ω × ℝ → ℝ≥0∞)
    (hq : Measurable q)
    (hcdf : ∀ t : ℝ, μ {ω | T ω ≤ (t : WithTop ℝ)} =
      ∫⁻ ω, ∫⁻ s in Iic t, q (ω,s) ∂volume ∂μ)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ ω, if T ω = ⊤ then 0 else w ((T ω).untopD 0) ∂μ) =
      ∫⁻ ω, ∫⁻ s, q (ω,s) * w s ∂volume ∂μ := by
  classical
  have hfinite : MeasurableSet {ω | T ω ≠ ⊤} :=
    (measurableSet_eq_fun hT measurable_const).compl
  have hmap : (∫⁻ s, w s ∂saleMeasure μ T) =
      ∫⁻ ω, if T ω = ⊤ then 0 else w ((T ω).untopD 0) ∂μ := by
    rw [saleMeasure,lintegral_map hw (hT.untopD 0),← lintegral_indicator hfinite]
    apply lintegral_congr
    intro ω
    simp only [Set.indicator_apply,Set.mem_setOf_eq]
    split_ifs <;> simp_all
  rw [←hmap,measure_eq_of_cdf μ T hT q hq hcdf]
  have hd : Measurable (fun s => ∫⁻ ω, q (ω,s) ∂μ) :=
    Measurable.lintegral_prod_right (ν := μ) (f := fun s ω => q (ω,s)) (hq.comp measurable_swap)
  rw [lintegral_withDensity_eq_lintegral_mul volume hd hw]
  have he (s : ℝ) : (∫⁻ ω, q (ω,s) ∂μ) * w s = ∫⁻ ω, q (ω,s) * w s ∂μ :=
    (lintegral_mul_const (w s) (hq.comp (measurable_id.prodMk measurable_const))).symm
  simp only [Pi.mul_apply]
  simp_rw [he]
  exact (lintegral_lintegral_swap (hq.mul (hw.comp measurable_snd)).aemeasurable).symm
#print axioms marked_identity
end MarkedClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
open Classical in
def stoppedDensity (j : ℕ) (τ : Fin j → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  if lastTime j τ < p.2 ∧ (p.2 : WithTop ℝ) ≤ nextTime u j τ p.1
    then ENNReal.ofReal (u.φ j p.2 τ) else 0
lemma stoppedDensity_measurable (j : ℕ) (τ : Fin j → ℝ) :
    Measurable (stoppedDensity u j τ) := by
  classical
  exact Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd.withTop_coe
      ((nextTime_measurable u j).comp (measurable_const.prodMk measurable_fst))))
    (((u.measurable j).comp (measurable_snd.prodMk measurable_const)).ennreal_ofReal)
    measurable_const
lemma stoppedDensity_Iic (j : ℕ) (τ : Fin j → ℝ) (e t : ℝ) :
    (∫⁻ s in Iic t, stoppedDensity u j τ (e,s)) =
    ∫⁻ s in Ioc (lastTime j τ) t,
      if (s : WithTop ℝ) ≤ nextTime u j τ e then ENNReal.ofReal (u.φ j s τ) else 0 := by
  classical
  have he : (fun s => stoppedDensity u j τ (e,s)) =
      (Ioi (lastTime j τ)).indicator (fun s =>
        if (s : WithTop ℝ) ≤ nextTime u j τ e then ENNReal.ofReal (u.φ j s τ) else 0) := by
    ext s
    by_cases h : lastTime j τ < s <;> simp [stoppedDensity,Set.indicator_apply,h]
  rw [he,lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  rfl
lemma stoppedDensity_cdf (j : ℕ) (τ : Fin j → ℝ) (t : ℝ) :
    expMeasure 1 {e : ℝ | nextTime u j τ e ≤ (t : WithTop ℝ)} =
      ∫⁻ e, ∫⁻ s in Iic t, stoppedDensity u j τ (e,s) ∂volume ∂expMeasure 1 := by
  simp_rw [stoppedDensity_Iic]
  by_cases ht : lastTime j τ ≤ t
  · have hevent : {e : ℝ | nextTime u j τ e ≤ (t : WithTop ℝ)} =
        {e : ℝ | ∃ s, u.nextSale j τ e = some s ∧ s ≤ t} := by
      ext e
      cases hn : u.nextSale j τ e <;> simp [nextTime,hn]
    rw [hevent]
    exact conditional_sales_compensator u j τ t ht
  · have hempty : {e : ℝ | nextTime u j τ e ≤ (t : WithTop ℝ)} = ∅ := by
      ext e
      simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
      exact fun he => ht ((nextTime_le_iff u j τ e t).mp he).1
    simp [hempty,Ioc_eq_empty (not_lt.mpr (le_of_not_ge ht))]

theorem conditional_marked_compensator (j : ℕ) (τ : Fin j → ℝ)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ e, if nextTime u j τ e = ⊤ then 0 else w ((nextTime u j τ e).untopD 0)
      ∂expMeasure 1) =
      ∫⁻ e, ∫⁻ s, stoppedDensity u j τ (e,s) * w s ∂volume ∂expMeasure 1 := by
  exact MarkedClock.marked_identity (expMeasure 1) (nextTime u j τ)
    ((nextTime_measurable u j).comp (measurable_const.prodMk measurable_id))
    (stoppedDensity u j τ) (stoppedDensity_measurable u j τ) (stoppedDensity_cdf u j τ) w hw
#print axioms conditional_marked_compensator
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
lemma revenue_rate_measurable {α : Type*} [MeasurableSpace α] (f : α → ℝ)
    (hf : Measurable f) (hmem : ∀ a, f a ∈ M.Λ) : Measurable (fun a => M.r (f a)) := by
  classical
  have hm : Measurable (M.Λ.piecewise M.r (fun _ => 0)) :=
    M.continuousOn.measurable_piecewise continuousOn_const M.ordConnected.measurableSet
  convert! hm.comp hf using 1
  ext a
  simp [Set.piecewise,hmem]
lemma price_eq_div (x : ℝ) : M.price x = M.r x / x := by
  by_cases hx : x = 0
  · simp [hx,Model.price,Model.r]
  · simp [Model.price,Model.r,hx,mul_div_cancel_left₀]
lemma price_measurable {α : Type*} [MeasurableSpace α] (f : α → ℝ)
    (hf : Measurable f) (hmem : ∀ a, f a ∈ M.Λ) : Measurable (fun a => M.price (f a)) := by
  simp_rw [price_eq_div]
  exact (revenue_rate_measurable f hf hmem).div hf
lemma rate_price (x : ℝ) : x * M.price x = M.r x := by
  by_cases hx : x = 0 <;> simp [Model.price,Model.r,hx]
lemma ofReal_rate_price (j : ℕ) (τ : Fin j → ℝ) (s : ℝ) :
    ENNReal.ofReal (u.φ j s τ) * ENNReal.ofReal (M.price (u.φ j s τ)) =
      ENNReal.ofReal (M.r (u.φ j s τ)) := by
  rw [← ENNReal.ofReal_mul (rate_nonneg u j τ s),rate_price]
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
theorem conditional_revenue (j : ℕ) (τ : Fin j → ℝ) (t : ℝ) :
    (∫⁻ e, (u.nextSale j τ e).elim 0 (fun s =>
      if s ≤ t then ENNReal.ofReal (M.price (u.φ j s τ)) else 0) ∂expMeasure 1) =
    ∫⁻ e, ∫⁻ s in Ioc (lastTime j τ) t,
      if (s : WithTop ℝ) ≤ nextTime u j τ e then ENNReal.ofReal (M.r (u.φ j s τ)) else 0
      ∂volume ∂expMeasure 1 := by
  classical
  let w : ℝ → ℝ≥0∞ := fun s => if s ≤ t then ENNReal.ofReal (M.price (u.φ j s τ)) else 0
  have hw : Measurable w := Measurable.ite (measurableSet_le measurable_id measurable_const)
    (price_measurable (fun s => u.φ j s τ) (rate_measurable u j τ) (fun s => u.mem j s τ)).ennreal_ofReal
    measurable_const
  have h := conditional_marked_compensator u j τ w hw
  have hleft (e : ℝ) : (if nextTime u j τ e = ⊤ then 0 else w ((nextTime u j τ e).untopD 0)) =
      (u.nextSale j τ e).elim 0 (fun s => if s ≤ t then ENNReal.ofReal (M.price (u.φ j s τ)) else 0) := by
    cases hn : u.nextSale j τ e <;> simp [nextTime,hn,w]
  simp_rw [hleft] at h
  rw [h]
  apply lintegral_congr
  intro e
  have he : (fun s => stoppedDensity u j τ (e,s) * w s) =
      (Ioc (lastTime j τ) t).indicator (fun s =>
        if (s : WithTop ℝ) ≤ nextTime u j τ e then ENNReal.ofReal (M.r (u.φ j s τ)) else 0) := by
    ext s
    by_cases ha : lastTime j τ < s <;> by_cases ht : s ≤ t <;>
      by_cases hn : (s : WithTop ℝ) ≤ nextTime u j τ e <;>
      simp [stoppedDensity,w,Set.indicator_apply,ha,ht,hn,ofReal_rate_price]
  rw [he,lintegral_indicator measurableSet_Ioc]
#print axioms conditional_revenue
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
lemma saleTime_mono (E : ℕ → ℝ) : Monotone (u.saleTime E) := by
  apply monotone_nat_of_le_succ
  intro j
  cases hh : u.history E j with
  | none => simp [Policy.saleTime,Policy.history,hh]
  | some τ =>
    rw [next_saleTime u E j τ hh]
    change ((u.history E j).elim ⊤ (fun τ => (lastTime j τ : WithTop ℝ))) ≤ _
    rw [hh]
    cases hn : u.nextSale j τ (E j) with
    | none => simp [nextTime,hn]
    | some s => simpa [nextTime,hn] using (nextSale_spec u j τ (E j) s hn).1
lemma stageRate_mem (j : ℕ) (E : ℕ → ℝ) (s : ℝ) : stageRate u j E s ∈ M.Λ := by
  classical
  cases hh : u.history E j with
  | none => simpa [stageRate,hh] using M.zero_mem
  | some τ => simp only [stageRate,hh,Option.elim_some]; split_ifs; exact u.mem j s τ; exact M.zero_mem
lemma stageRate_interval (j : ℕ) (E : ℕ → ℝ) (s : ℝ) (h : stageRate u j E s ≠ 0) :
    u.saleTime E j < (s : WithTop ℝ) ∧ (s : WithTop ℝ) ≤ u.saleTime E (j+1) := by
  classical
  cases hh : u.history E j with
  | none => simp [stageRate,hh] at h
  | some τ =>
    simp only [stageRate,hh,Option.elim_some] at h
    split_ifs at h with hs
    · simpa [Policy.saleTime,hh] using hs
    · exact (h rfl).elim
lemma stageRate_unique (E : ℕ → ℝ) (s : ℝ) (i j : ℕ)
    (hi : stageRate u i E s ≠ 0) (hj : stageRate u j E s ≠ 0) : i = j := by
  have hI := stageRate_interval u i E s hi
  have hJ := stageRate_interval u j E s hj
  rcases lt_trichotomy i j with h | h | h
  · have hc := (hI.2.trans (saleTime_mono u E (Nat.succ_le_of_lt h))).trans_lt hJ.1
    exact (lt_irrefl _ hc).elim
  · exact h
  · have hc := (hJ.2.trans (saleTime_mono u E (Nat.succ_le_of_lt h))).trans_lt hI.1
    exact (lt_irrefl _ hc).elim
lemma revenueRate_sum (n : ℕ) (E : ℕ → ℝ) (s : ℝ) :
    M.r (u.intensityAt n E s) = ∑ j ∈ Finset.range n, M.r (stageRate u j E s) := by
  classical
  change M.r (∑ j ∈ Finset.range n,stageRate u j E s) = _
  by_cases h : ∃ j ∈ Finset.range n, stageRate u j E s ≠ 0
  · obtain ⟨j,hj,hn⟩ := h
    have hz (k : ℕ) (hk : k ∈ Finset.range n) (hkj : k ≠ j) : stageRate u k E s = 0 := by
      by_contra hne
      exact hkj (stageRate_unique u E s k j hne hn)
    rw [Finset.sum_eq_single_of_mem j hj hz,Finset.sum_eq_single_of_mem j hj]
    intro k hk hkj
    rw [hz k hk hkj]
    simp [Model.r]
  · push_neg at h
    rw [Finset.sum_eq_zero (fun j hj => h j hj),Finset.sum_eq_zero (fun j hj => by rw [h j hj]; simp [Model.r])]
    simp [Model.r]
lemma stageRate_joint (j : ℕ) : Measurable (fun p : (ℕ → ℝ) × ℝ => stageRate u j p.1 p.2) := by
  classical
  have he (E : ℕ → ℝ) (s : ℝ) : stageRate u j E s =
      if u.history E j ≠ none ∧ lastTime j (histVec u E j) < s ∧
        (s : WithTop ℝ) ≤ u.saleTime E (j+1) then u.φ j s (histVec u E j) else 0 := by
    cases hh : u.history E j <;> simp [stageRate,histVec,hh]
  simp_rw [he]
  apply Measurable.ite _ _ measurable_const
  · exact ((history_measurable u j).1.preimage measurable_fst).inter
      ((measurableSet_lt (((lastTime_measurable j).comp (history_measurable u j).2).comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd.withTop_coe ((saleTime_measurable u (j+1)).comp measurable_fst)))
  · exact (u.measurable j).comp (measurable_snd.prodMk ((history_measurable u j).2.comp measurable_fst))
lemma stageRevenue_joint (j : ℕ) :
    Measurable (fun p : (ℕ → ℝ) × ℝ => ENNReal.ofReal (M.r (stageRate u j p.1 p.2))) :=
  (revenue_rate_measurable _ (stageRate_joint u j) (fun p => stageRate_mem u j p.1 p.2)).ennreal_ofReal
#print axioms revenueRate_sum
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
open Classical in
def revenueStep (j : ℕ) (t : ℝ) (a : Bool × (Fin j → ℝ)) (e : ℝ) : ℝ≥0∞ :=
  if a.1 = true ∧ nextTime u j a.2 e ≤ (t : WithTop ℝ) then
    ENNReal.ofReal (M.price (u.φ j ((nextTime u j a.2 e).untopD 0) a.2)) else 0
open Classical in
def revenueDensity (j : ℕ) (t : ℝ) (p : ((Bool × (Fin j → ℝ)) × ℝ) × ℝ) : ℝ≥0∞ :=
  if p.1.1.1 = true ∧ lastTime j p.1.1.2 < p.2 ∧ p.2 ≤ t ∧
      (p.2 : WithTop ℝ) ≤ nextTime u j p.1.1.2 p.1.2 then
    ENNReal.ofReal (M.r (u.φ j p.2 p.1.1.2)) else 0
def revenueHazardStep (j : ℕ) (t : ℝ) (a : Bool × (Fin j → ℝ)) (e : ℝ) : ℝ≥0∞ :=
  ∫⁻ s, revenueDensity u j t ((a,e),s)
lemma revenueStep_measurable (j : ℕ) (t : ℝ) :
    Measurable (fun p : (Bool × (Fin j → ℝ)) × ℝ => revenueStep u j t p.1 p.2) := by
  classical
  have hT : Measurable (fun p : (Bool × (Fin j → ℝ)) × ℝ => nextTime u j p.1.2 p.2) :=
    (nextTime_measurable u j).comp (measurable_fst.snd.prodMk measurable_snd)
  apply Measurable.ite ((measurableSet_eq_fun measurable_fst.fst measurable_const).inter
    (measurableSet_le hT measurable_const)) _ measurable_const
  apply Measurable.ennreal_ofReal
  apply price_measurable
  · exact (u.measurable j).comp ((hT.untopD 0).prodMk measurable_fst.snd)
  · intro p; exact u.mem _ _ _
lemma revenueDensity_measurable (j : ℕ) (t : ℝ) : Measurable (revenueDensity u j t) := by
  classical
  apply Measurable.ite _ _ measurable_const
  · exact (measurableSet_eq_fun measurable_fst.fst.fst measurable_const).inter
      ((measurableSet_lt ((lastTime_measurable j).comp measurable_fst.fst.snd) measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_const).inter
      (measurableSet_le measurable_snd.withTop_coe
        ((nextTime_measurable u j).comp (measurable_fst.fst.snd.prodMk measurable_fst.snd)))))
  · apply Measurable.ennreal_ofReal
    apply revenue_rate_measurable
    · exact (u.measurable j).comp (measurable_snd.prodMk measurable_fst.fst.snd)
    · intro p; exact u.mem _ _ _
lemma revenueHazardStep_measurable (j : ℕ) (t : ℝ) :
    Measurable (fun p : (Bool × (Fin j → ℝ)) × ℝ => revenueHazardStep u j t p.1 p.2) :=
  Measurable.lintegral_prod_right (f := fun p s => revenueDensity u j t (p,s))
    (revenueDensity_measurable u j t)
lemma revenueHazardStep_true (j : ℕ) (t : ℝ) (τ : Fin j → ℝ) (e : ℝ) :
    revenueHazardStep u j t (true,τ) e =
      ∫⁻ s in Ioc (lastTime j τ) t,
        if (s : WithTop ℝ) ≤ nextTime u j τ e then ENNReal.ofReal (M.r (u.φ j s τ)) else 0 := by
  classical
  unfold revenueHazardStep
  have he : (fun s => revenueDensity u j t (((true,τ),e),s)) =
      (Ioc (lastTime j τ) t).indicator (fun s =>
        if (s : WithTop ℝ) ≤ nextTime u j τ e then ENNReal.ofReal (M.r (u.φ j s τ)) else 0) := by
    ext s
    by_cases ha : lastTime j τ < s <;> by_cases ht : s ≤ t <;>
      simp [revenueDensity,Set.indicator_apply,ha,ht]
  rw [he,lintegral_indicator measurableSet_Ioc]
lemma conditional_revenue_step (j : ℕ) (t : ℝ) (a : Bool × (Fin j → ℝ)) :
    (∫⁻ e, revenueStep u j t a e ∂expMeasure 1) =
      ∫⁻ e, revenueHazardStep u j t a e ∂expMeasure 1 := by
  classical
  rcases a with ⟨b,τ⟩
  cases b
  · simp [revenueStep,revenueHazardStep,revenueDensity]
  · simp_rw [revenueHazardStep_true]
    have he (e : ℝ) : revenueStep u j t (true,τ) e =
        (u.nextSale j τ e).elim 0 (fun s =>
          if s ≤ t then ENNReal.ofReal (M.price (u.φ j s τ)) else 0) := by
      cases hn : u.nextSale j τ e <;> simp [revenueStep,nextTime,hn]
    simp_rw [he]
    exact conditional_revenue u j τ t
lemma adaptive_revenue_stage (j : ℕ) (t : ℝ) :
    (∫⁻ E, revenueStep u j t (historyData u j E) (E j) ∂clockLaw) =
      ∫⁻ E, revenueHazardStep u j t (historyData u j E) (E j) ∂clockLaw := by
  rw [history_clock_lintegral u j _ (revenueStep_measurable u j t),
      history_clock_lintegral u j _ (revenueHazardStep_measurable u j t)]
  exact lintegral_congr (fun a => conditional_revenue_step u j t a)
lemma revenueStep_history (j : ℕ) (t : ℝ) (E : ℕ → ℝ) :
    revenueStep u j t (historyData u j E) (E j) =
      (u.history E (j+1)).elim 0 (fun τ => if τ (Fin.last j) ≤ t then
        ENNReal.ofReal (M.price (u.φ j (τ (Fin.last j)) (Fin.init (α := fun _ => ℝ) τ))) else 0) := by
  classical
  cases hh : u.history E j with
  | none => simp [revenueStep,historyData,Policy.history,hh]
  | some τ =>
    cases hn : u.nextSale j τ (E j) <;>
      simp [revenueStep,historyData,histVec,Policy.history,hh,nextTime,hn]
lemma revenueHazardStep_history (j : ℕ) (t : ℝ) (E : ℕ → ℝ) :
    revenueHazardStep u j t (historyData u j E) (E j) =
      ∫⁻ s in Ioc 0 t, ENNReal.ofReal (M.r (stageRate u j E s)) := by
  classical
  cases hh : u.history E j with
  | none => simp [revenueHazardStep,revenueDensity,stageRate,historyData,hh,Model.r]
  | some τ =>
    have h0 := history_last_nonneg u E j τ hh
    have hdata : historyData u j E = (true,τ) := by simp [historyData,histVec,hh]
    rw [hdata,revenueHazardStep_true]
    symm
    calc
      _ = ∫⁻ s in Ioc 0 t, (Ioi (lastTime j τ)).indicator (fun s =>
          if (s : WithTop ℝ) ≤ nextTime u j τ (E j) then ENNReal.ofReal (M.r (u.φ j s τ)) else 0) s := by
        apply lintegral_congr
        intro s
        rw [show stageRate u j E s =
          (if lastTime j τ < s ∧ (s : WithTop ℝ) ≤ nextTime u j τ (E j) then u.φ j s τ else 0) by
            simp [stageRate,hh,next_saleTime u E j τ hh]]
        by_cases ha : lastTime j τ < s <;> by_cases hn : (s : WithTop ℝ) ≤ nextTime u j τ (E j) <;>
          simp [Set.indicator_apply,ha,hn,Model.r]
      _ = _ := by
        rw [lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
        have he : Ioi (lastTime j τ) ∩ Ioc 0 t = Ioc (lastTime j τ) t := by
          ext s
          simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
          exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h0.trans_lt h.1,h.2⟩⟩
        rw [he]
#print axioms adaptive_revenue_stage
#print axioms revenueHazardStep_history
end AdaptiveClock

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdaptiveClock
open GVRPricing.FixedPrice
variable {M : Model} (u : Policy M)
lemma revenue_rate_nonneg (x : ℝ) (hx : x ∈ M.Λ) : 0 ≤ M.r x := by
  by_cases h0 : x = 0
  · simp [Model.r,h0]
  · exact mul_nonneg (M.nonneg x hx) (M.price_nonneg x hx h0)
lemma expectedRevenue_sum (n : ℕ) (t : ℝ) :
    u.expectedRevenue n t = ∑ j ∈ Finset.range n,
      ∫⁻ E, revenueStep u j t (historyData u j E) (E j) ∂clockLaw := by
  classical
  unfold Policy.expectedRevenue Policy.revenueOn
  simp_rw [← revenueStep_history]
  apply lintegral_finsetSum
  intro j hj
  exact (revenueStep_measurable u j t).comp
    ((historyData_measurable u j).prodMk (measurable_pi_apply j))
lemma expectedRevenueRate_sum (n : ℕ) (t : ℝ) :
    u.expectedRevenueRate n t = ∑ j ∈ Finset.range n,
      ∫⁻ E, (∫⁻ s in Ioc 0 t, ENNReal.ofReal (M.r (stageRate u j E s))) ∂clockLaw := by
  classical
  have he (E : ℕ → ℝ) : (∫⁻ s in Ioc 0 t, ENNReal.ofReal (M.r (u.intensityAt n E s))) =
      ∑ j ∈ Finset.range n, ∫⁻ s in Ioc 0 t, ENNReal.ofReal (M.r (stageRate u j E s)) := by
    simp_rw [revenueRate_sum,ENNReal.ofReal_sum_of_nonneg (fun j hj =>
      revenue_rate_nonneg _ (stageRate_mem u j E _))]
    apply lintegral_finsetSum
    intro j hj
    exact (stageRevenue_joint u j).comp (measurable_const.prodMk measurable_id)
  unfold Policy.expectedRevenueRate
  simp_rw [he]
  apply lintegral_finsetSum
  intro j hj
  exact Measurable.lintegral_prod_right (f := fun E s => ENNReal.ofReal (M.r (stageRate u j E s)))
    (stageRevenue_joint u j)
theorem revenue_compensator (n : ℕ) (t : ℝ) :
    u.expectedRevenue n t = u.expectedRevenueRate n t := by
  rw [expectedRevenue_sum,expectedRevenueRate_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [adaptive_revenue_stage]
  exact lintegral_congr (fun E => revenueHazardStep_history u j t E)
#print axioms revenue_compensator
end AdaptiveClock

theorem solution (M : GVRPricing.FixedPrice.Model) (u : GVRPricing.FixedPrice.Policy M)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    u.expectedSales n t = u.expectedCumIntensity n t ∧
    u.expectedCumIntensity n t ≤ n ∧
    u.expectedRevenue n t = u.expectedRevenueRate n t := by
  exact ⟨AdaptiveClock.sales_compensator u n t,
    (AdaptiveClock.sales_compensator_and_bound u n t).2,
    AdaptiveClock.revenue_compensator u n t⟩
#print axioms solution
