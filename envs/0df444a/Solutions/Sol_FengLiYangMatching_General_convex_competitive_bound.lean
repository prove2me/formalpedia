-- Prove2me | solution 1 for FengLiYangMatching.General.convex_competitive_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:04:33.766248+00:00
-- url     : https://prove2.me/submissions/3cd6564b-5a14-4a41-ae09-57c65f8b897a

import Theorems.Thm_FengLiYangMatching_General_expected_survival_bound
import Theorems.Thm_FengLiYangMatching_General_lemma_3_1
import Definitions.Def_FengLiYangMatching_General_Local
import Definitions.Def_FengLiYangMatching_General_Process
open MeasureTheory Finset
open scoped BigOperators

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


namespace FengLiYangMatching.General
noncomputable section

lemma exists_maximum {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ M : EdgeSet n, M ⊆ graphEdges G ∧ IsMatching M ∧ M.card = OPT G := by
  classical
  let s := (graphEdges G).powerset.filter IsMatching
  have hs : s.Nonempty := ⟨∅, by simp [s,IsMatching]⟩
  obtain ⟨M,hM,hmax⟩ := s.exists_mem_eq_sup hs Finset.card
  exact ⟨M, (Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1),
    (Finset.mem_filter.mp hM).2, hmax.symm⟩

lemma edge_convex_bound {n : ℕ} (G : SimpleGraph (Fin n)) (e : Edge n)
    (a c : ℝ) (ha : 0 ≤ a) (hab : a < 3/8)
    (hc : ∀ k : ℕ, 1 ≤ k → c ≤ L k a (3/8)) :
    c - 6/11 ≤ (1/2 : ℝ) * (∫ t in a..(3/8 : ℝ), edgeSurvival G e t) -
      (1-a)/22 * edgeSurvival G e a - (1-(3/8 : ℝ))/10 * edgeSurvival G e (3/8) := by
  classical
  obtain ⟨d,hd,hs,hrep⟩ := lemma_3_1 (G.deleteEdges {e}) (covered {e})
  have hb : (3/8 : ℝ) ≤ 1 := by norm_num
  have hval_a := hrep a ⟨ha, le_trans (le_of_lt hab) hb⟩
  have hval_b := hrep (3/8) ⟨by norm_num, hb⟩
  have hint : (∫ t in a..(3/8 : ℝ), edgeSurvival G e t) =
      ∫ t in a..(3/8 : ℝ), d.sum (fun k v => v*(1-t)^k) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hab)] at ht
    exact hrep t ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  have h := finsupp_scalar_transfer a (3/8) c ha (le_of_lt hab) hb hc d hd hs
  rw [hint]
  change _ ≤ _ - (1-a)/22 * survival (G.deleteEdges {e}) (covered {e}) a -
    (1-(3/8 : ℝ))/10 * survival (G.deleteEdges {e}) (covered {e}) (3/8)
  rw [hval_a,hval_b]
  linarith

 theorem convex_bound (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8)
    (c : ℝ) (hc : ∀ k : ℕ, 1 ≤ k → c ≤ L k a (3/8)) :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      Integrable (ALG G a (3/8)) (sampleLaw G (5/11)) ∧
      (∫ w, ALG G a (3/8) w ∂sampleLaw G (5/11)) ≥ c * (OPT G : ℝ) := by
  classical
  intro n G
  refine ⟨integrable_ALG G a (3/8) (5/11), ?_⟩
  obtain ⟨M,hMG,hM,hmax⟩ := exists_maximum G
  have hexp := expected_survival_bound G M hMG hM hmax a ha hab
  have hsum := Finset.sum_le_sum (s:=M) (fun e he => edge_convex_bound G e a c ha hab hc)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  rw [hmax] at hsum
  nlinarith

end
end FengLiYangMatching.General
open FengLiYangMatching.General
theorem solution (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8)
    (c : ℝ) (hc : ∀ k : ℕ, 1 ≤ k → c ≤ L k a (3/8)) :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      Integrable (ALG G a (3/8)) (sampleLaw G (5/11)) ∧
      (∫ w, ALG G a (3/8) w ∂sampleLaw G (5/11)) ≥ c * (OPT G : ℝ) :=
  convex_bound a ha hab c hc
