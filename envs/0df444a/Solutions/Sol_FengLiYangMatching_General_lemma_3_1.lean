-- Prove2me | solution 1 for FengLiYangMatching.General.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:10:27.243333+00:00
-- url     : https://prove2.me/submissions/c9a6dc05-d58a-46b5-be38-c105c60aeb95

import Definitions.Def_FengLiYangMatching_General_Process
import Definitions.Def_FengLiYangMatching_General_Local
import Theorems.Thm_FengLiYangMatching_General_survival_recurrence
open MeasureTheory Finset
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma power_integral (k : ℕ) (a b : ℝ) :
    (∫ t in a..b, (1-t)^k) = ((1-a)^(k+1)-(1-b)^(k+1))/(k+1) := by
  have hi : IntervalIntegrable (fun t : ℝ => (1-t)^k) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -(1-t)^(k+1)/(k+1)) ((1-x)^k) x := by
    intro x
    convert! (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).pow (k+1)).neg.div_const ((k:ℝ)+1) using 1 <;>
      norm_num
    field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x) hi
  convert h using 1 <;> ring

lemma finsupp_scalar_transfer (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hL : ∀ k : ℕ, 1 ≤ k → c ≤ L k a b)
    (d : ℕ →₀ ℝ) (hd : ∀ k, 0 ≤ d k) (hs : d.sum (fun _ v => v) = 1) :
    c ≤ 6/11 + (1/2 : ℝ) * (∫ t in a..b, d.sum (fun k v => v*(1-t)^k)) -
      (1-a)/22 * d.sum (fun k v => v*(1-a)^k) -
      (1-b)/10 * d.sum (fun k v => v*(1-b)^k) := by
  have hint : (∫ t in a..b, d.sum (fun k v => v*(1-t)^k)) =
      d.sum (fun k v => v * (((1-a)^(k+1)-(1-b)^(k+1))/(k+1))) := by
    unfold Finsupp.sum
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_const_mul, power_integral]
    · intro k hk
      apply Continuous.intervalIntegrable; fun_prop
  rw [hint]
  have havg : c ≤ d.sum (fun k v => v * L (k+1) a b) := by
    calc
      c = d.sum (fun k v => v*c) := by rw [← Finsupp.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hL (k+1) (by omega)) (hd k)
  convert havg using 1
  unfold Finsupp.sum
  symm
  calc
    (∑ k ∈ d.support, d k * L (k+1) a b) =
        ∑ k ∈ d.support, (6/11 * d k + (1/2 : ℝ) * (d k * (((1-a)^(k+1)-(1-b)^(k+1))/(k+1))) -
          (1-a)/22 * (d k*(1-a)^k) - (1-b)/10 * (d k*(1-b)^k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold L
      push_cast
      rw [pow_succ, pow_succ]
      field_simp
      <;> ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hs' : ∑ k ∈ d.support, d k = 1 := hs
      rw [hs']
      ring

end
end FengLiYangMatching.General
open MeasureTheory Finset
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma sort_fiber_measurable {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    MeasurableSet {f : Fin m → ℝ | Tuple.sort f = σ} := by
  have heq : {f : Fin m → ℝ | Tuple.sort f = σ} =
      {f | (∀ i j, i ≤ j → f (σ i) ≤ f (σ j)) ∧
        ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j} := by
    ext f
    simp only [Set.mem_setOf_eq, eq_comm (a:=Tuple.sort f), Tuple.eq_sort_iff, Monotone, Function.comp_apply]
  rw [heq]
  change MeasurableSet ({f : Fin m → ℝ | ∀ i j, i ≤ j → f (σ i) ≤ f (σ j)} ∩
    {f | ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j})
  apply MeasurableSet.inter
  · simp only [Set.setOf_forall, Set.ofPred_forall]
    apply MeasurableSet.iInter; intro i
    apply MeasurableSet.iInter; intro j
    apply MeasurableSet.iInter; intro hij
    exact measurableSet_le (show Measurable (fun f : Fin m → ℝ => f (σ i)) from measurable_pi_apply _)
      (show Measurable (fun f : Fin m → ℝ => f (σ j)) from measurable_pi_apply _)
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter; intro i
    apply MeasurableSet.iInter; intro j
    apply MeasurableSet.iInter; intro hij
    by_cases hs : σ i < σ j
    · simp only [hs, implies_true, Set.setOf_true, MeasurableSet.univ]
    · simpa only [hs, imp_false, Set.compl_setOf] using
        (measurableSet_eq_fun
          (show Measurable (fun f : Fin m → ℝ => f (σ i)) from measurable_pi_apply _)
          (show Measurable (fun f : Fin m → ℝ => f (σ j)) from measurable_pi_apply _)).compl

instance {n : ℕ} : Fintype (State n) :=
  Fintype.ofInjective (fun S : State n => (S.actual,S.shadow,S.reserved)) (by
    intro S T h; cases S; cases T; cases h; rfl)

instance {n : ℕ} : MeasurableSpace (State n) := ⊤
instance {n : ℕ} : MeasurableSingletonClass (State n) := ⟨fun _ => MeasurableSet.of_discrete⟩

lemma measurable_step {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (a b : ℝ) (e : Edge n)
    {S : Ω → State n} {t : Ω → ℝ} {c : Ω → Bool}
    (hS : Measurable S) (ht : Measurable t) (hc : Measurable c) :
    Measurable (fun w => step a b (S w) e (t w) (c w)) := by
  classical
  let reserve : State n × Bool → State n := fun z =>
    if free z.1.shadow e then
      if z.2 then ⟨z.1.actual, insert e z.1.shadow, z.1.reserved ∪ covered {e}⟩
      else ⟨insert e z.1.actual, insert e z.1.shadow, z.1.reserved⟩
    else z.1
  let retain : State n → State n := fun z =>
    if free z.shadow e then ⟨insert e z.actual, insert e z.shadow, z.reserved⟩ else z
  let recover : State n → State n := fun z =>
    if free z.actual e ∧ ¬ (∀ v, v ∈ e → v ∈ z.reserved) then
      ⟨insert e z.actual, z.shadow, z.reserved⟩ else z
  have h0 := (measurable_of_finite reserve).comp (hS.prodMk hc)
  have h1 := (measurable_of_finite retain).comp hS
  have h2 := (measurable_of_finite recover).comp hS
  exact h0.ite (measurableSet_lt ht measurable_const)
    (h1.ite (measurableSet_lt ht measurable_const) h2)

lemma measurable_fixed_fold {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (l : List G.edgeSet)
    (S : Sample G → State n) (hS : Measurable S) :
    Measurable (fun w => (l.map (fun e => (e.val,w.1 e,w.2 e))).foldl
      (fun S o => step a b S o.1 o.2.1 o.2.2) (S w)) := by
  induction l generalizing S with
  | nil => exact hS
  | cons e l ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    exact measurable_step a b e.val hS ((measurable_pi_apply e).comp measurable_fst)
      ((measurable_pi_apply e).comp measurable_snd)

lemma measurable_execution {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) :
    Measurable (execution G a b) := by
  classical
  letI : MeasurableSpace (Equiv.Perm (Fin (Fintype.card G.edgeSet))) := ⊤
  letI : MeasurableSingletonClass (Equiv.Perm (Fin (Fintype.card G.edgeSet))) := ⟨fun _ => trivial⟩
  let enum := (Fintype.equivFin G.edgeSet).symm
  have hsort : Measurable (fun t : Times G => Tuple.sort (t ∘ enum)) := by
    apply measurable_to_countable'
    intro σ
    exact (sort_fiber_measurable σ).preimage (measurable_pi_iff.mpr fun i => measurable_pi_apply (enum i))
  let exec : Equiv.Perm (Fin (Fintype.card G.edgeSet)) × Sample G → State n := fun z =>
    run a b ((List.ofFn (z.1.trans enum)).map fun e => (e.val,z.2.1 e,z.2.2 e))
  have hexec : Measurable exec := by
    apply measurable_from_prod_countable_right
    intro σ
    exact measurable_fixed_fold G a b (List.ofFn (σ.trans enum)) (fun _ => initial n) measurable_const
  exact hexec.comp ((hsort.comp measurable_fst).prodMk measurable_id)

lemma measurable_ALG {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) : Measurable (ALG G a b) :=
  (measurable_of_finite (fun S : State n => (S.actual.card : ℝ))).comp (measurable_execution G a b)

lemma integrable_ALG {n : ℕ} (G : SimpleGraph (Fin n)) (a b p : ℝ) :
    Integrable (ALG G a b) (sampleLaw G p) := by
  classical
  haveI : IsFiniteMeasure (arrivalLaw G) := by
    unfold arrivalLaw RandomOrderCRS.arrivalTimeLaw
    infer_instance
  haveI : IsFiniteMeasure (coinLaw G p) := by
    unfold coinLaw RandomOrderCRS.survivalLaw
    infer_instance
  haveI : IsFiniteMeasure (sampleLaw G p) := by unfold sampleLaw; infer_instance
  apply Integrable.of_bound (measurable_ALG G a b).aestronglyMeasurable (Fintype.card (Edge n))
  apply Filter.Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold ALG; positivity)]
  change ((execution G a b w).actual.card : ℝ) ≤ _
  exact_mod_cast Finset.card_le_univ (execution G a b w).actual

end
end FengLiYangMatching.General
open MeasureTheory Finset
namespace FengLiYangMatching.General
noncomputable section

lemma arrival_probability {n : ℕ} (G : SimpleGraph (Fin n)) : IsProbabilityMeasure (arrivalLaw G) := by
  classical
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by simp⟩
  unfold arrivalLaw RandomOrderCRS.arrivalTimeLaw
  infer_instance

lemma survival_zero {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : survival G A 0 = 1 := by
  classical
  haveI := arrival_probability G
  have hpos : ∀ᵐ t ∂arrivalLaw G, ∀ e, 0 ≤ t e := by
    unfold arrivalLaw RandomOrderCRS.arrivalTimeLaw
    exact ae_all_iff.mpr fun e => Measure.tendsto_eval_ae_ae.eventually
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using hx.1)
  unfold survival Measure.real
  have he : ∀ᵐ t ∂arrivalLaw G, (t ∈ {t : Times G | ∀ v ∈ A, v ∉ covered (shadowAt G t 0)}) ↔ t ∈ (Set.univ : Set (Times G)) := by
    filter_upwards [hpos] with t ht
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hshadow : shadowAt G t 0 = ∅ := by
      unfold shadowAt
      have : (orderedEdges G t).filter (fun e => t e < 0) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e he
        simpa only [decide_eq_true_eq] using not_lt.mpr (ht e)
      rw [this]
      simp [greedy]
    simp [hshadow,covered]
  rw [measure_congr (s := {t : Times G | ∀ v ∈ A, v ∉ covered (shadowAt G t 0)})
    (t := Set.univ) (by
      filter_upwards [he] with t ht
      exact propext ht)]
  simp

end
end FengLiYangMatching.General
open MeasureTheory Finset
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

private def liftCoeffs (d : ℕ →₀ ℝ) : ℕ →₀ ℝ :=
  ∑ k ∈ d.support, Finsupp.single (k+1) (d k/(k+1))

lemma liftCoeffs_nonneg (d : ℕ →₀ ℝ) (hd : ∀ k, 0 ≤ d k) : ∀ k, 0 ≤ liftCoeffs d k := by
  intro j
  classical
  unfold liftCoeffs
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro k hk
  have hdk := hd k
  simp only [Finsupp.single_apply]
  split_ifs <;> positivity

lemma liftCoeffs_eval (d : ℕ →₀ ℝ) (t : ℝ) :
    (liftCoeffs d).sum (fun k v => v*(1-t)^k) =
      ∫ s in t..(1:ℝ), d.sum (fun k v => v*(1-s)^k) := by
  classical
  unfold liftCoeffs
  change _ = ∫ s in t..(1:ℝ), ∑ k ∈ d.support, d k*(1-s)^k
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, power_integral, sub_self, zero_pow (Nat.succ_ne_zero _), sub_zero]
    rw [← Finsupp.sum_finsetSum_index]
    · apply Finset.sum_congr rfl
      intro k hk
      simp [Finsupp.sum_single_index]
      ring
    · intro k; simp
    · intro k x y; ring
  · intro k hk
    apply Continuous.intervalIntegrable; fun_prop

lemma graphEdges_delete {n : ℕ} (J : SimpleGraph (Fin n)) (e : Edge n) :
    graphEdges (J.deleteEdges {e}) = (graphEdges J).erase e := by
  classical
  ext f
  simp [graphEdges, SimpleGraph.edgeSet_deleteEdges, and_comm]

lemma survival_expansion {n : ℕ} (J : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    ∃ d : ℕ →₀ ℝ, (∀ k, 0 ≤ d k) ∧ d.sum (fun _ v => v) = 1 ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, survival J A t = d.sum (fun k v => v*(1-t)^k) := by
  classical
  generalize hsize : (graphEdges J).card = m
  induction m using Nat.strong_induction_on generalizing J A with
  | h m ih =>
    let E := (graphEdges J).filter fun e => ∃ v ∈ A, v ∈ e
    have hchild : ∀ e : E, ∃ d : ℕ →₀ ℝ, (∀ k, 0 ≤ d k) ∧
        ∀ t ∈ Set.Icc (0:ℝ) 1,
          survival (J.deleteEdges {e.val}) (A ∪ covered {e.val}) t = d.sum (fun k v => v*(1-t)^k) := by
      intro e
      have hlt : (graphEdges (J.deleteEdges {e.val})).card < m := by
        rw [graphEdges_delete, ← hsize]
        exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mp e.property).1
      obtain ⟨d,hd,hs,hr⟩ := ih _ hlt (J.deleteEdges {e.val}) (A ∪ covered {e.val}) rfl
      exact ⟨d,hd,hr⟩
    choose coeff hcoeff hrep using hchild
    let d : ℕ →₀ ℝ := Finsupp.single 0 (survival J A 1) + ∑ e : E, liftCoeffs (coeff e)
    have hd : ∀ k, 0 ≤ d k := by
      intro k
      dsimp [d]
      simp only [Finsupp.add_apply, Finsupp.finsetSum_apply]
      apply add_nonneg
      · simp only [Finsupp.single_apply]
        split_ifs
        · exact ENNReal.toReal_nonneg
        · exact le_refl 0
      · exact Finset.sum_nonneg fun e he => liftCoeffs_nonneg (coeff e) (hcoeff e) k
    have hdrep : ∀ t ∈ Set.Icc (0:ℝ) 1, survival J A t = d.sum (fun k v => v*(1-t)^k) := by
      intro t ht
      rw [survival_recurrence J A t ht]
      dsimp [d]
      rw [Finsupp.sum_add_index' (fun k => zero_mul _) (fun k x y => add_mul _ _ _)]
      simp only [Finsupp.sum_single_index, pow_zero, mul_one]
      congr 1
      rw [← Finsupp.sum_finsetSum_index (fun k => zero_mul _) (fun k x y => add_mul _ _ _)]
      rw [← Finset.sum_coe_sort E]
      apply Finset.sum_congr rfl
      intro e he
      rw [liftCoeffs_eval]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht.2] at hs
      exact hrep e s ⟨le_trans ht.1 hs.1, hs.2⟩
    refine ⟨d,hd,?_,hdrep⟩
    have hh := hdrep 0 ⟨by norm_num,by norm_num⟩
    simpa [survival_zero] using hh.symm

end
end FengLiYangMatching.General
open FengLiYangMatching.General
theorem solution {n : ℕ} (J : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    ∃ c : ℕ →₀ ℝ, (∀ k, 0 ≤ c k) ∧ c.sum (fun _ v => v) = 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        survival J A t = c.sum (fun k v => v * (1-t)^k) := by
  exact survival_expansion J A
