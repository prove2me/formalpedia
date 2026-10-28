-- Prove2me | solution 1 for ExploreFirst.FundIneq.fundamental_inequality
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T06:09:16.071412+00:00
-- url     : https://prove2.me/submissions/3a77284d-5713-4034-a310-222de83ce4c3

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_FullHistory


section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace ExploreProof
open ExploreFirst.FundIneq
variable {K t : ℕ}
lemma measurable_snoc : Measurable (@fullHistorySnoc t) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [fullHistorySnoc] using (measurable_snd.snd : Measurable (fun p : FullHistory t × (ℝ × unitInterval) => p.2.2))
    · simp only [Fin.snoc_castSucc]
      fun_prop
  · rw [measurable_pi_iff]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [fullHistorySnoc] using (measurable_snd.fst : Measurable (fun p : FullHistory t × (ℝ × unitInterval) => p.2.1))
    · simp only [Fin.snoc_castSucc]
      fun_prop
instance full_step_markov (ν : BanditAlgorithm.StochasticBandit K) (ψ : FullStrategy K) (t : ℕ) :
    IsMarkovKernel (fullStepKernel ν ψ t) := by
  unfold fullStepKernel
  infer_instance
lemma measurable_initial : Measurable
    (fun u : unitInterval => (((fun _ : Fin 1 => u), (fun i : Fin 0 => i.elim0)) : FullHistory 0)) := by
  fun_prop
instance history_probability (ν : BanditAlgorithm.StochasticBandit K) (ψ : FullStrategy K) (T : ℕ) :
    IsProbabilityMeasure (fullHistoryMeasure ν ψ T) := by
  induction T with
  | zero => exact Measure.isProbabilityMeasure_map measurable_initial.aemeasurable
  | succ T ih =>
    rw [fullHistoryMeasure]
    exact Measure.isProbabilityMeasure_map measurable_snoc.aemeasurable

def historyInit (h : FullHistory (t+1)) : FullHistory t :=
  (Fin.init h.1, Fin.init h.2)
lemma measurable_init : Measurable (@historyInit t) := by
  fun_prop [historyInit, Fin.init]
@[simp] lemma init_snoc (p : FullHistory t × (ℝ × unitInterval)) :
    historyInit (fullHistorySnoc p) = p.1 := by
  simp [historyInit, fullHistorySnoc]
lemma history_init_map (ν : BanditAlgorithm.StochasticBandit K) (ψ : FullStrategy K) (t : ℕ) :
    (fullHistoryMeasure ν ψ (t+1)).map historyInit = fullHistoryMeasure ν ψ t := by
  rw [fullHistoryMeasure, Measure.map_map measurable_init measurable_snoc]
  have heq : historyInit ∘ fullHistorySnoc = (Prod.fst : FullHistory t × (ℝ × unitInterval) → FullHistory t) := by
    funext p
    exact init_snoc p
  rw [heq]
  exact Measure.fst_compProd _ _
lemma measurable_prefix {T : ℕ} (i : Fin T) : Measurable (fun h => fullHistoryPrefix h i) := by
  fun_prop [fullHistoryPrefix]
lemma prefix_init {T : ℕ} (h : FullHistory (T+1)) (i : Fin T) :
    fullHistoryPrefix h i.castSucc = fullHistoryPrefix (historyInit h) i := by
  rfl
@[simp] lemma prefix_last {T : ℕ} (h : FullHistory (T+1)) :
    fullHistoryPrefix h (Fin.last T) = historyInit h := by
  rfl
end ExploreProof
end

section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace ExploreProof
open ExploreFirst.FundIneq
variable {K T : ℕ}
lemma count_le (ψ : FullStrategy K) (a : Fin K) (h : FullHistory T) :
    fullPullCount ψ a h ≤ T := by
  unfold fullPullCount
  calc
    _ ≤ ∑ _t : Fin T, 1 := Finset.sum_le_sum fun t _ => by split_ifs <;> omega
    _ = T := by simp
lemma select_event_measurable (ψ : FullStrategy K) (t : ℕ) (a : Fin K) :
    MeasurableSet {h | ψ.select t h = a} :=
  (ψ.measurable_select t) (measurableSet_singleton a)
lemma measurable_count (ψ : FullStrategy K) (a : Fin K) :
    Measurable (fun h : FullHistory T => (fullPullCount ψ a h : ℝ)) := by
  simp only [fullPullCount, Nat.cast_sum]
  apply Finset.measurable_sum
  intro t _
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact measurable_const.ite
    (measurableSet_eq_fun ((ψ.measurable_select t.val).comp (measurable_prefix t)) measurable_const)
    measurable_const
lemma integrable_count (ν : BanditAlgorithm.StochasticBandit K) (ψ : FullStrategy K)
    (T : ℕ) (a : Fin K) :
    Integrable (fun h : FullHistory T => (fullPullCount ψ a h : ℝ)) (fullHistoryMeasure ν ψ T) := by
  apply Integrable.of_bound (measurable_count ψ a).aestronglyMeasurable T
  exact Filter.Eventually.of_forall fun h => by simpa using (Nat.cast_le (α := ℝ)).mpr (count_le ψ a h)
lemma count_succ (ψ : FullStrategy K) (a : Fin K) (h : FullHistory (T+1)) :
    fullPullCount ψ a h = fullPullCount ψ a (historyInit h) +
      if ψ.select T (historyInit h) = a then 1 else 0 := by
  simp only [fullPullCount, Fin.sum_univ_castSucc, prefix_init, prefix_last, Fin.val_castSucc,
    Fin.val_last]
lemma count_nonneg (ν : BanditAlgorithm.StochasticBandit K) (ψ : FullStrategy K)
    (T : ℕ) (a : Fin K) : 0 ≤ fullExpPulls ν ψ T a :=
  integral_nonneg fun _ => Nat.cast_nonneg _
lemma expected_succ (ν : BanditAlgorithm.StochasticBandit K) (ψ : FullStrategy K)
    (T : ℕ) (a : Fin K) :
    fullExpPulls ν ψ (T+1) a = fullExpPulls ν ψ T a +
      (fullHistoryMeasure ν ψ T).real {h | ψ.select T h = a} := by
  classical
  let μ := fullHistoryMeasure ν ψ T
  let E : Set (FullHistory T) := {h | ψ.select T h = a}
  have hE : MeasurableSet E := select_event_measurable ψ T a
  have hi : Integrable (fun h : FullHistory T => if ψ.select T h = a then (1:ℝ) else 0) μ := by
    apply Integrable.of_bound (measurable_const.ite hE measurable_const).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun h => by split_ifs <;> norm_num
  have hm : Measurable (fun h : FullHistory T => (fullPullCount ψ a h : ℝ) +
      if ψ.select T h = a then 1 else 0) :=
    (measurable_count ψ a).add (measurable_const.ite hE measurable_const)
  have heq : fullExpPulls ν ψ (T+1) a =
      ∫ h, (fullPullCount ψ a h : ℝ) + (if ψ.select T h = a then 1 else 0) ∂μ := by
    rw [show μ = (fullHistoryMeasure ν ψ (T+1)).map historyInit from (history_init_map ν ψ T).symm,
      integral_map measurable_init.aemeasurable hm.aestronglyMeasurable]
    unfold fullExpPulls
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun h => by simp [count_succ]
  rw [heq, integral_add (integrable_count ν ψ T a) hi]
  congr 1
  simpa [E, Set.indicator] using (integral_indicator_one hE : ∫ h, E.indicator (fun _ => (1:ℝ)) h ∂μ = μ.real E)
lemma expected_succ_ennreal (ν : BanditAlgorithm.StochasticBandit K) (ψ : FullStrategy K)
    (T : ℕ) (a : Fin K) :
    ENNReal.ofReal (fullExpPulls ν ψ (T+1) a) = ENNReal.ofReal (fullExpPulls ν ψ T a) +
      fullHistoryMeasure ν ψ T {h | ψ.select T h = a} := by
  rw [expected_succ, ENNReal.ofReal_add (count_nonneg ν ψ T a) (measureReal_nonneg)]
  simp
@[simp] lemma expected_zero (ν : BanditAlgorithm.StochasticBandit K) (ψ : FullStrategy K)
    (a : Fin K) : fullExpPulls ν ψ 0 a = 0 := by
  simp [fullExpPulls, fullPullCount]
end ExploreProof
end

section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace ExploreProof

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]
  (μ : Measure α) [IsProbabilityMeasure μ]
  (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]

theorem joint_density (hac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    μ.compProd κ = (μ.compProd η).withDensity (fun p => κ.rnDeriv η p.1 p.2) := by
  rw [← Measure.compProd_withDensity (Kernel.measurable_rnDeriv κ η)]
  apply Measure.compProd_congr
  filter_upwards [hac] with x hx
  exact (Kernel.withDensity_rnDeriv_eq hx).symm

theorem joint_rnDeriv (hac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (μ.compProd κ).rnDeriv (μ.compProd η) =ᵐ[μ.compProd η]
      fun p => κ.rnDeriv η p.1 p.2 := by
  symm
  apply Measure.eq_rnDeriv (Kernel.measurable_rnDeriv κ η)
    (Measure.MutuallySingular.zero_left (μ := μ.compProd η))
  simpa using joint_density μ κ η hac

theorem conditional_kl_integral (hac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    klDiv (μ.compProd κ) (μ.compProd η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
  rw [klDiv_eq_lintegral_klFun_of_ac
    (Measure.absolutelyContinuous_compProd_right_iff.mpr hac)]
  calc
    _ = ∫⁻ p, ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal) ∂μ.compProd η := by
      apply lintegral_congr_ae
      filter_upwards [joint_rnDeriv μ κ η hac] with p hp
      rw [hp]
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (klFun (κ.rnDeriv η x y).toReal) ∂η x ∂μ := by
      apply Measure.lintegral_compProd
      exact ENNReal.measurable_ofReal.comp
        (continuous_klFun.measurable.comp (ENNReal.measurable_toReal.comp
          (Kernel.measurable_rnDeriv κ η)))
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hac] with x hx
      rw [klDiv_eq_lintegral_klFun_of_ac hx]
      apply lintegral_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := x)] with y hy
      rw [hy]

end ExploreProof
end

section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace ExploreProof

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]
  (μ : Measure α) [IsProbabilityMeasure μ]
  (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]

omit [IsProbabilityMeasure μ] in
theorem finite_selector_integral {K : ℕ} (s : α → Fin K) (hs : Measurable s)
    (D : Fin K → ℝ≥0∞) :
    (∫⁻ x, D (s x) ∂μ) = ∑ a, μ {x | s x = a} * D a := by
  classical
  have heq : (fun x => D (s x)) = fun x =>
      ∑ a : Fin K, ({x | s x = a} : Set α).indicator (fun _ => D a) x := by
    funext x
    simp [Set.indicator_apply]
  rw [heq, lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    have hm : MeasurableSet {x | s x = a} := measurableSet_eq_fun hs measurable_const
    rw [lintegral_indicator hm, lintegral_const]
    simp [mul_comm]
  · intro a _
    exact measurable_const.indicator (hs (measurableSet_singleton a))

theorem conditional_kl_le_finite_selector {K : ℕ} (s : α → Fin K)
    (hs : Measurable s) (D : Fin K → ℝ≥0∞)
    (hD : ∀ x, klDiv (κ x) (η x) = D (s x)) :
    klDiv (μ.compProd κ) (μ.compProd η) ≤ ∑ a, μ {x | s x = a} * D a := by
  classical
  by_cases htop : (∑ a, μ {x | s x = a} * D a) = ∞
  · simp [htop]
  have hae : ∀ a, ∀ᵐ x ∂μ, s x = a → D a ≠ ∞ := by
    intro a
    by_cases hDa : D a = ∞
    · have hm : μ {x | s x = a} = 0 := by
        by_contra hne
        have hle : μ {x | s x = a} * D a ≤ ∑ b, μ {x | s x = b} * D b :=
          Finset.single_le_sum (f := fun b : Fin K => μ {x | s x = b} * D b)
            (fun _ _ => bot_le) (Finset.mem_univ a)
        rw [hDa, ENNReal.mul_top hne] at hle
        exact htop (top_le_iff.mp hle)
      have hn : ∀ᵐ x ∂μ, s x ≠ a := by
        apply ae_iff.mpr
        simpa using hm
      filter_upwards [hn] with x hx
      exact fun he => (hx he).elim
    · exact Filter.Eventually.of_forall (fun _ _ => hDa)
  have hac : ∀ᵐ x ∂μ, κ x ≪ η x := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    apply (klDiv_ne_top_iff.mp ?_).1
    rw [hD]
    exact hx (s x) rfl
  rw [conditional_kl_integral μ κ η hac]
  simp_rw [hD]
  exact (finite_selector_integral μ s hs D).le

end ExploreProof
end

section
open MeasureTheory ProbabilityTheory InformationTheory ExploreFirst.FundIneq
open scoped ENNReal
namespace ExploreProof

lemma full_step_at {K t : ℕ} (ν : BanditAlgorithm.StochasticBandit K)
    (ψ : FullStrategy K) (h : FullHistory t) :
    fullStepKernel ν ψ t h = (ν.P (ψ.select t h)).compProd
      (Kernel.const ℝ (volume : Measure unitInterval)) := by
  ext s hs
  rw [fullStepKernel, Kernel.compProd_apply hs, Measure.compProd_apply hs]
  rfl

lemma full_step_kl {K t : ℕ} (ν ν' : BanditAlgorithm.StochasticBandit K)
    (ψ : FullStrategy K) (h : FullHistory t) :
    klDiv (fullStepKernel ν ψ t h) (fullStepKernel ν' ψ t h) =
      klDiv (ν.P (ψ.select t h)) (ν'.P (ψ.select t h)) := by
  rw [full_step_at, full_step_at, klDiv_compProd_left]

theorem conditional_step_kl_le {K t : ℕ} (ν ν' : BanditAlgorithm.StochasticBandit K)
    (ψ : FullStrategy K) (μ : Measure (FullHistory t)) [IsProbabilityMeasure μ] :
    klDiv (μ.compProd (fullStepKernel ν ψ t))
      (μ.compProd (fullStepKernel ν' ψ t)) ≤
      ∑ a, μ {h | ψ.select t h = a} * klDiv (ν.P a) (ν'.P a) := by
  exact conditional_kl_le_finite_selector μ (fullStepKernel ν ψ t)
    (fullStepKernel ν' ψ t) (ψ.select t) (ψ.measurable_select t)
    (fun a => klDiv (ν.P a) (ν'.P a)) (full_step_kl ν ν' ψ)

end ExploreProof
end

section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace ExploreProof
open ExploreFirst.FundIneq
variable {K : ℕ}
theorem history_kl_le (ν ν' : BanditAlgorithm.StochasticBandit K) (ψ : FullStrategy K) (T : ℕ) :
    klDiv (fullHistoryMeasure ν ψ T) (fullHistoryMeasure ν' ψ T) ≤
      ∑ a, ENNReal.ofReal (fullExpPulls ν ψ T a) * klDiv (ν.P a) (ν'.P a) := by
  induction T with
  | zero => simp [fullHistoryMeasure]
  | succ T ih =>
    calc
      _ ≤ klDiv ((fullHistoryMeasure ν ψ T).compProd (fullStepKernel ν ψ T))
          ((fullHistoryMeasure ν' ψ T).compProd (fullStepKernel ν' ψ T)) := by
        exact klDiv_map_le _ _ measurable_snoc
      _ = klDiv (fullHistoryMeasure ν ψ T) (fullHistoryMeasure ν' ψ T) +
          klDiv ((fullHistoryMeasure ν ψ T).compProd (fullStepKernel ν ψ T))
            ((fullHistoryMeasure ν ψ T).compProd (fullStepKernel ν' ψ T)) :=
        klDiv_compProd_eq_add _ _ _ _
      _ ≤ (∑ a, ENNReal.ofReal (fullExpPulls ν ψ T a) * klDiv (ν.P a) (ν'.P a)) +
          ∑ a, fullHistoryMeasure ν ψ T {h | ψ.select T h = a} * klDiv (ν.P a) (ν'.P a) :=
        add_le_add ih (conditional_step_kl_le ν ν' ψ (fullHistoryMeasure ν ψ T))
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [expected_succ_ennreal, add_mul]
end ExploreProof
end

section
open MeasureTheory ProbabilityTheory InformationTheory ExploreFirst.FundIneq
open scoped ENNReal
namespace ExploreProof

variable {α : Type*} [MeasurableSpace α]

noncomputable def statisticKernel (Z : α → ℝ) (hZ : Measurable Z) : Kernel α ℝ where
  toFun x := bernoulliLaw (Z x)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [bernoulliLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    fun_prop

theorem statisticKernel_markov (Z : α → ℝ) (hZ : Measurable Z)
    (h01 : ∀ x, Z x ∈ Set.Icc (0 : ℝ) 1) : IsMarkovKernel (statisticKernel Z hZ) := by
  constructor
  intro x
  constructor
  change bernoulliLaw (Z x) Set.univ = 1
  simp only [bernoulliLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (h01 x).1 (sub_nonneg.mpr (h01 x).2)]
  simp

theorem statistic_integrable (μ : Measure α) [IsProbabilityMeasure μ]
    (Z : α → ℝ) (hZ : Measurable Z) (h01 : ∀ x, Z x ∈ Set.Icc (0 : ℝ) 1) :
    Integrable Z μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) hZ.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa [abs_of_nonneg (h01 x).1] using (h01 x).2)

theorem statistic_comp (μ : Measure α) [IsProbabilityMeasure μ]
    (Z : α → ℝ) (hZ : Measurable Z) (h01 : ∀ x, Z x ∈ Set.Icc (0 : ℝ) 1) :
    (statisticKernel Z hZ) ∘ₘ μ = bernoulliLaw (∫ x, Z x ∂μ) := by
  have hi := statistic_integrable μ Z hZ h01
  have hj : Integrable (fun x => 1 - Z x) μ := (integrable_const 1).sub hi
  have hZi : ∫⁻ x, ENNReal.ofReal (Z x) ∂μ = ENNReal.ofReal (∫ x, Z x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => (h01 x).1)).symm
  have hJi : ∫⁻ x, ENNReal.ofReal (1 - Z x) ∂μ = ENNReal.ofReal (1 - ∫ x, Z x ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hj
      (Filter.Eventually.of_forall fun x => sub_nonneg.mpr (h01 x).2)]
    rw [integral_sub (integrable_const 1) hi]
    simp
  ext s hs
  rw [Measure.bind_apply hs (statisticKernel Z hZ).aemeasurable]
  change (∫⁻ x, bernoulliLaw (Z x) s ∂μ) = _
  simp only [bernoulliLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_left (by fun_prop), lintegral_mul_const _ (by fun_prop),
    lintegral_mul_const _ (by fun_prop), hZi, hJi]

theorem randomized_statistic_le (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (Z : α → ℝ) (hZ : Measurable Z)
    (h01 : ∀ x, Z x ∈ Set.Icc (0 : ℝ) 1) :
    klBer (∫ x, Z x ∂μ) (∫ x, Z x ∂ν) ≤ klDiv μ ν := by
  have := statisticKernel_markov Z hZ h01
  simpa only [statistic_comp μ Z hZ h01, statistic_comp ν Z hZ h01, klBer] using
    klDiv_comp_right_le μ ν (statisticKernel Z hZ)

end ExploreProof
end

section
open MeasureTheory ProbabilityTheory InformationTheory ExploreFirst.FundIneq
open scoped ENNReal
namespace ExploreProof
theorem full_root {K : ℕ} (ν ν' : BanditAlgorithm.StochasticBandit K)
    (hν : ∀ a, Integrable id (ν.P a)) (hν' : ∀ a, Integrable id (ν'.P a))
    (ψ : FullStrategy K) (T : ℕ)
    (Z : FullHistory T → ℝ) (hZ : Measurable Z)
    (hZ01 : ∀ h, Z h ∈ Set.Icc (0 : ℝ) 1) :
    klBer (∫ h, Z h ∂(fullHistoryMeasure ν ψ T))
        (∫ h, Z h ∂(fullHistoryMeasure ν' ψ T))
      ≤ ∑ a, ENNReal.ofReal (fullExpPulls ν ψ T a) * klDiv (ν.P a) (ν'.P a) := by
  have _ := hν
  have _ := hν'
  exact (randomized_statistic_le (fullHistoryMeasure ν ψ T)
    (fullHistoryMeasure ν' ψ T) Z hZ hZ01).trans (history_kl_le ν ν' ψ T)

end ExploreProof
end

open MeasureTheory ProbabilityTheory InformationTheory ExploreFirst.FundIneq
open scoped ENNReal

theorem solution {K : ℕ} (ν ν' : BanditAlgorithm.StochasticBandit K)
    (hν : ∀ a, Integrable id (ν.P a)) (hν' : ∀ a, Integrable id (ν'.P a))
    (ψ : FullStrategy K) (T : ℕ)
    (Z : FullHistory T → ℝ) (hZ : Measurable Z)
    (hZ01 : ∀ h, Z h ∈ Set.Icc (0 : ℝ) 1) :
    klBer (∫ h, Z h ∂(fullHistoryMeasure ν ψ T))
        (∫ h, Z h ∂(fullHistoryMeasure ν' ψ T))
      ≤ ∑ a, ENNReal.ofReal (fullExpPulls ν ψ T a) * klDiv (ν.P a) (ν'.P a) := by
  exact ExploreProof.full_root ν ν' hν hν' ψ T Z hZ hZ01

theorem ExploreFirst.FundIneq.fundamental_inequality {K : ℕ} (ν ν' : BanditAlgorithm.StochasticBandit K)
    (hν : ∀ a, Integrable id (ν.P a)) (hν' : ∀ a, Integrable id (ν'.P a))
    (ψ : FullStrategy K) (T : ℕ)
    (Z : FullHistory T → ℝ) (hZ : Measurable Z)
    (hZ01 : ∀ h, Z h ∈ Set.Icc (0 : ℝ) 1) :
    klBer (∫ h, Z h ∂(fullHistoryMeasure ν ψ T))
        (∫ h, Z h ∂(fullHistoryMeasure ν' ψ T))
      ≤ ∑ a, ENNReal.ofReal (fullExpPulls ν ψ T a) * klDiv (ν.P a) (ν'.P a) := by
  exact _root_.solution ν ν' hν hν' ψ T Z hZ hZ01
