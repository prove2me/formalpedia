-- Prove2me | solution 1 for FengLiYangMatching.General.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T20:31:45.854198+00:00
-- url     : https://prove2.me/submissions/fab3fa9b-757a-4fc0-8b04-47f1c388f565

import Definitions.Def_FengLiYangMatching_General_Local
import Definitions.Def_FengLiYangMatching_General_Process
import Theorems.Thm_FengLiYangMatching_General_local_recovery_bound
import Theorems.Thm_FengLiYangMatching_General_conditional_local_experiment
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
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma integrable_finite_function {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) : Integrable f μ := by
  apply Integrable.of_bound (measurable_of_finite f).aestronglyMeasurable (∑ x : Ω, ‖f x‖)
  exact Filter.Eventually.of_forall (fun x => Finset.single_le_sum (fun y hy => norm_nonneg _) (Finset.mem_univ x))

lemma integrable_finite_comp {Ω β : Type*} [MeasurableSpace Ω] [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → β) (hf : Measurable f) (g : β → ℝ) : Integrable (fun x => g (f x)) μ := by
  apply Integrable.of_bound ((measurable_of_finite g).comp hf).aestronglyMeasurable (∑ y : β, ‖g y‖)
  exact Filter.Eventually.of_forall (fun x => Finset.single_le_sum (fun y hy => norm_nonneg _) (Finset.mem_univ (f x)))

lemma coin_probability {n : ℕ} (G : SimpleGraph (Fin n)) : IsProbabilityMeasure (coinLaw G (5/11)) := by
  haveI : IsProbabilityMeasure (RandomOrderCRS.survivalLaw (5/11)) := ⟨by
    norm_num [RandomOrderCRS.survivalLaw]
    rw [← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj]
    apply NNReal.eq
    norm_num⟩
  unfold coinLaw
  infer_instance

lemma coin_scalar_mean : (∫ c : Bool, (if c = true then (1:ℝ) else 0) ∂(RandomOrderCRS.survivalLaw (5/11))) = (5/11:ℝ) := by
  haveI : IsFiniteMeasure (RandomOrderCRS.survivalLaw (5/11)) := by unfold RandomOrderCRS.survivalLaw; infer_instance
  rw [integral_fintype (integrable_finite_function _ _)]
  norm_num [Measure.real,RandomOrderCRS.survivalLaw]

lemma coin_coordinate_mean {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) :
    (∫ c : Coins G, (if c e = true then (1:ℝ) else 0) ∂coinLaw G (5/11)) = (5/11:ℝ) := by
  haveI : IsProbabilityMeasure (RandomOrderCRS.survivalLaw (5/11)) := ⟨by
    norm_num [RandomOrderCRS.survivalLaw]
    rw [← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj]
    apply NNReal.eq
    norm_num⟩
  have hp : MeasurePreserving (fun c : Coins G => c e) (coinLaw G (5/11)) (RandomOrderCRS.survivalLaw (5/11)) := by
    exact measurePreserving_eval (fun _ : G.edgeSet => RandomOrderCRS.survivalLaw (5/11)) e
  have hm : Measurable (fun c : Bool => if c = true then (1:ℝ) else 0) := measurable_of_finite _
  have hh := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (fun c : Bool => if c = true then (1:ℝ) else 0)
      ((coinLaw G (5/11)).map (fun c => c e)) by rw [hp.map_eq]; exact hm.aestronglyMeasurable)
  rw [hp.map_eq] at hh
  exact hh.symm.trans coin_scalar_mean

lemma coin_subset_mean {n : ℕ} (G : SimpleGraph (Fin n)) (F : EdgeSet n) (hF : F ⊆ graphEdges G) :
    (∫ c : Coins G, ((F.filter (fun e => ∃ he : e ∈ G.edgeSet, c ⟨e,he⟩ = true)).card : ℝ) ∂coinLaw G (5/11)) =
      (5/11:ℝ)*F.card := by
  haveI := coin_probability G
  have hfun : (fun c : Coins G => ((F.filter (fun e => ∃ he : e ∈ G.edgeSet, c ⟨e,he⟩ = true)).card : ℝ)) =
      (fun c => ∑ e ∈ F, if (∃ he : e ∈ G.edgeSet, c ⟨e,he⟩ = true) then (1:ℝ) else 0) := by
    funext c
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hfun,integral_finsetSum F (fun e he => integrable_finite_function _ _)]
  have hterm (e : Edge n) (he : e ∈ F) :
      (∫ c : Coins G, (if (∃ h : e ∈ G.edgeSet, c ⟨e,h⟩ = true) then (1:ℝ) else 0) ∂coinLaw G (5/11)) = (5/11:ℝ) := by
    have heG : e ∈ G.edgeSet := by simpa [graphEdges] using hF he
    have hh : (fun c : Coins G => if (∃ h : e ∈ G.edgeSet, c ⟨e,h⟩ = true) then (1:ℝ) else 0) =
        (fun c => if c ⟨e,heG⟩ = true then (1:ℝ) else 0) := by
      funext c
      congr 1
      apply propext
      constructor
      · rintro ⟨h,hc⟩; exact hc
      · intro hc; exact ⟨heG,hc⟩
    rw [hh]
    exact coin_coordinate_mean G ⟨e,heG⟩
  calc
    _ = ∑ e ∈ F, (5/11:ℝ) := Finset.sum_congr rfl hterm
    _ = _ := by simp; ring

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma foldl_filter_eq {α β : Type*} (l : List α) (p : α → Bool) (f : β → α → β) (s : β) :
    (l.filter p).foldl f s = l.foldl (fun s e => if p e then f s e else s) s := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih =>
    by_cases h : p e
    · simp [h,ih]
    · simp [h,ih]

lemma shadowAt_fold {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (u : ℝ) :
    shadowAt G t u = (orderedEdges G t).foldl (fun F e =>
      if t e < u then (if free F e.val then insert e.val F else F) else F) ∅ := by
  unfold shadowAt greedy
  rw [List.foldl_map,foldl_filter_eq]
  simp only [decide_eq_true_eq]

lemma measurable_shadow_fold {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (G : SimpleGraph (Fin n)) (l : List G.edgeSet) (t : Ω → Times G) (u : Ω → ℝ)
    (ht : Measurable t) (hu : Measurable u) (S : Ω → EdgeSet n) (hS : Measurable S) :
    Measurable (fun w => l.foldl (fun F e =>
      if t w e < u w then (if free F e.val then insert e.val F else F) else F) (S w)) := by
  induction l generalizing S with
  | nil => exact hS
  | cons e l ih =>
    simp only [List.foldl_cons]
    apply ih
    exact ((measurable_of_finite (fun F : EdgeSet n => if free F e.val then insert e.val F else F)).comp hS).ite
      (measurableSet_lt ((measurable_pi_apply e).comp ht) hu) hS

lemma measurable_shadowAt_joint {n : ℕ} (G : SimpleGraph (Fin n)) :
    Measurable (fun z : Times G × ℝ => shadowAt G z.1 z.2) := by
  letI : MeasurableSpace (Equiv.Perm (Fin (Fintype.card G.edgeSet))) := ⊤
  letI : MeasurableSingletonClass (Equiv.Perm (Fin (Fintype.card G.edgeSet))) := ⟨fun _ => trivial⟩
  let enum := (Fintype.equivFin G.edgeSet).symm
  have hsort : Measurable (fun t : Times G => Tuple.sort (t ∘ enum)) := by
    apply measurable_to_countable'
    intro σ
    exact (sort_fiber_measurable σ).preimage (measurable_pi_iff.mpr fun i => measurable_pi_apply (enum i))
  let exec : Equiv.Perm (Fin (Fintype.card G.edgeSet)) × (Times G × ℝ) → EdgeSet n := fun z =>
    (List.ofFn (z.1.trans enum)).foldl (fun F e =>
      if z.2.1 e < z.2.2 then (if free F e.val then insert e.val F else F) else F) ∅
  have hexec : Measurable exec := by
    apply measurable_from_prod_countable_right
    intro σ
    exact measurable_shadow_fold G (List.ofFn (σ.trans enum)) Prod.fst Prod.snd
      measurable_fst measurable_snd (fun _ => ∅) measurable_const
  have hh := hexec.comp ((hsort.comp measurable_fst).prodMk measurable_id)
  change Measurable (fun z : Times G × ℝ => (orderedEdges G z.1).foldl (fun F e =>
      if z.1 e < z.2 then (if free F e.val then insert e.val F else F) else F) ∅) at hh
  simpa only [←shadowAt_fold] using hh

lemma measurable_survival_event {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    MeasurableSet {z : Times G × ℝ | ∀ v ∈ A, v ∉ covered (shadowAt G z.1 z.2)} := by
  have h : MeasurableSet {F : EdgeSet n | ∀ v ∈ A, v ∉ covered F} := MeasurableSet.of_discrete
  exact h.preimage (measurable_shadowAt_joint G)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section
lemma sample_probability {n : ℕ} (G : SimpleGraph (Fin n)) : IsProbabilityMeasure (sampleLaw G (5/11)) := by
  haveI := arrival_probability G
  haveI := coin_probability G
  unfold sampleLaw
  infer_instance

lemma measurable_shadow_fixed {n : ℕ} (G : SimpleGraph (Fin n)) (u : ℝ) :
    Measurable (fun t : Times G => shadowAt G t u) := by
  have hm : Measurable (fun t : Times G => (t,u)) := measurable_id.prodMk measurable_const
  exact (measurable_shadowAt_joint G).comp hm

lemma integrable_shadow_card {n : ℕ} (G : SimpleGraph (Fin n)) (u : ℝ) :
    Integrable (fun t => ((shadowAt G t u).card : ℝ)) (arrivalLaw G) := by
  haveI := arrival_probability G
  exact integrable_finite_comp (arrivalLaw G) (fun t => shadowAt G t u) (measurable_shadow_fixed G u) (fun F : EdgeSet n => (F.card:ℝ))

lemma integrable_shadow_sample {n : ℕ} (G : SimpleGraph (Fin n)) (u : ℝ) :
    Integrable (fun w : Sample G => ((shadowAt G w.1 u).card : ℝ)) (sampleLaw G (5/11)) := by
  haveI := sample_probability G
  exact integrable_finite_comp (sampleLaw G (5/11)) (fun w => shadowAt G w.1 u)
    ((measurable_shadow_fixed G u).comp measurable_fst) (fun F : EdgeSet n => (F.card:ℝ))


end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma measurable_recovery {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) :
    Measurable (recovery G a b) := by
  rw [measurable_finset_iff]
  intro e
  apply measurableSet_setOfPred.mp
  by_cases he : e ∈ G.edgeSet
  · have heq : {w : Sample G | e ∈ recovery G a b w} =
        {w | e ∈ (execution G a b w).actual} ∩ {w | b ≤ w.1 ⟨e,he⟩} := by
      ext w
      simp only [recovery,Finset.mem_filter,Set.mem_inter_iff,Set.mem_setOf_eq]
      constructor
      · rintro ⟨ha,⟨h,hb⟩⟩; exact ⟨ha,hb⟩
      · rintro ⟨ha,hb⟩; exact ⟨ha,⟨he,hb⟩⟩
    rw [heq]
    have hact : Measurable (fun w : Sample G => (execution G a b w).actual) :=
      (measurable_of_finite (fun S : State n => S.actual)).comp (measurable_execution G a b)
    exact ((measurableSet_mem_finset e).preimage hact).inter
      (measurableSet_le measurable_const ((measurable_pi_apply (⟨e,he⟩ : G.edgeSet)).comp measurable_fst))
  · have heq : {w : Sample G | e ∈ recovery G a b w} = ∅ := by
      ext w
      simp only [recovery,Finset.mem_filter,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false,not_and]
      intro ha
      rintro ⟨h,hb⟩
      exact he h
    rw [heq]
    exact MeasurableSet.empty

def recoveryData {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) :
    EdgeSet n × Finset (Fin n) × EdgeSet n :=
  (recovery G a b w,(execution G a b w).reserved,shadowAt G w.1 b)

def xyDataCount {n : ℕ} (z : EdgeSet n × Finset (Fin n) × EdgeSet n) : ℝ :=
  ((z.1.filter (fun e => ∃ x y, e = s(x,y) ∧ x ∈ z.2.1 ∧ y ∈ univ \ covered z.2.2)).card:ℝ)

def yyDataCount {n : ℕ} (z : EdgeSet n × Finset (Fin n) × EdgeSet n) : ℝ :=
  ((z.1.filter (fun e => ∀ v, v ∈ e → v ∈ univ \ covered z.2.2)).card:ℝ)

lemma measurable_recoveryData {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) :
    Measurable (recoveryData G a b) := by
  have hr : Measurable (fun w : Sample G => (execution G a b w).reserved) :=
    (measurable_of_finite (fun S : State n => S.reserved)).comp (measurable_execution G a b)
  exact (measurable_recovery G a b).prodMk (hr.prodMk ((measurable_shadow_fixed G b).comp measurable_fst))

lemma ZXY_data {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) :
    ZXY G a b w = xyDataCount (recoveryData G a b w) := rfl

lemma ZYY_data {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) :
    ZYY G a b w = yyDataCount (recoveryData G a b w) := rfl

lemma integrable_recovery_counts {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ)
    (μ : Measure (Sample G)) [IsFiniteMeasure μ] : Integrable (ZXY G a b) μ ∧ Integrable (ZYY G a b) μ := by
  constructor
  · convert! integrable_finite_comp μ (recoveryData G a b) (measurable_recoveryData G a b) xyDataCount using 1
  · convert! integrable_finite_comp μ (recoveryData G a b) (measurable_recoveryData G a b) yyDataCount using 1

lemma integrable_Nhat {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (e : Edge n)
    (μ : Measure (Sample G)) [IsFiniteMeasure μ] : Integrable (Nhat G a b e) μ :=
  integrable_finite_comp μ (recovery G a b) (measurable_recovery G a b)
    (fun F => (((covered {e}) ∩ covered F).card:ℝ))

lemma integrable_Rhat {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (a b : ℝ) (h : History n) (e : Edge n)
    (μ : Measure (Sample G)) [IsFiniteMeasure μ] : Integrable (Rhat G M a b h e) μ :=
  integrable_finite_comp μ (recovery G a b) (measurable_recovery G a b)
    (fun F => (((references M h e) ∩ covered F).card:ℝ))

end
end FengLiYangMatching.General
open MeasureTheory Finset
namespace FengLiYangMatching.General
noncomputable section

lemma actual_step_mono {n : ℕ} (a b : ℝ) (S : State n) (e : Edge n) (t : ℝ) (coin : Bool) :
    S.actual ⊆ (step a b S e t coin).actual := by
  classical
  unfold step
  split_ifs <;> simp_all

lemma fold_actual_mono {n : ℕ} (a b : ℝ) (l : List (Edge n × ℝ × Bool)) (S : State n) :
    S.actual ⊆ (l.foldl (fun S o => step a b S o.1 o.2.1 o.2.2) S).actual := by
  induction l generalizing S with
  | nil => exact Subset.rfl
  | cons o l ih => exact (actual_step_mono a b S o.1 o.2.1 o.2.2).trans (ih _)

lemma run_append {n : ℕ} (a b : ℝ) (l k : List (Edge n × ℝ × Bool)) :
    run a b (l ++ k) = k.foldl (fun S o => step a b S o.1 o.2.1 o.2.2) (run a b l) := by
  simp [run, List.foldl_append]

lemma run_take_mono {n : ℕ} (a b : ℝ) (l : List (Edge n × ℝ × Bool)) (j k : ℕ) (hjk : j ≤ k) :
    (run a b (l.take j)).actual ⊆ (run a b (l.take k)).actual := by
  have h : l.take k = l.take j ++ (l.take k).drop j := by
    calc
      l.take k = (l.take k).take j ++ (l.take k).drop j := (List.take_append_drop j (l.take k)).symm
      _ = l.take j ++ (l.take k).drop j := by rw [List.take_take, min_eq_left hjk]
  rw [h, run_append]
  exact fold_actual_mono _ _ _ _

lemma step_actual_seen {n : ℕ} (a b : ℝ) (S : State n) (e : Edge n) (t : ℝ) (c : Bool) :
    (step a b S e t c).actual ⊆ insert e S.actual := by
  classical
  unfold step
  split_ifs <;> simp_all

lemma run_seen_aux {n : ℕ} (a b : ℝ) (S : State n) (l : List (Edge n × ℝ × Bool)) :
    (l.foldl (fun S o => step a b S o.1 o.2.1 o.2.2) S).actual ⊆ S.actual ∪ (l.map Prod.fst).toFinset := by
  classical
  induction l generalizing S with
  | nil => simp
  | cons o l ih =>
    exact (ih _).trans (by
      intro e he
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at *
      rcases he with he | he
      · have := step_actual_seen a b S o.1 o.2.1 o.2.2 he
        simp only [Finset.mem_insert] at this
        tauto
      · tauto)

lemma run_seen {n : ℕ} (a b : ℝ) (l : List (Edge n × ℝ × Bool)) :
    (run a b l).actual ⊆ (l.map Prod.fst).toFinset := by
  simpa [run, initial] using run_seen_aux a b (initial n) l

lemma covered_mono {n : ℕ} {F H : EdgeSet n} (h : F ⊆ H) : covered F ⊆ covered H := by
  classical
  intro v hv
  simp only [covered, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rcases hv with ⟨e,he,hv⟩
  exact ⟨e,h he,hv⟩

lemma free_of_subset {n : ℕ} {F H : EdgeSet n} {e : Edge n} (h : F ⊆ H) (hf : free H e) : free F e := by
  intro v hv hm
  exact hf v hv (covered_mono h hm)

lemma matching_insert {n : ℕ} {F : EdgeSet n} {e : Edge n} (hF : IsMatching F)
    (he : ¬ e.IsDiag) (hf : free F e) : IsMatching (insert e F) := by
  classical
  constructor
  · intro f h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact he
    · exact hF.1 f h
  · intro f hfs g hgs hfg v hv hvg
    rcases Finset.mem_insert.mp hfs with rfl | hfF
    · rcases Finset.mem_insert.mp hgs with rfl | hgF
      · exact hfg rfl
      · exact hf v hv (by simp only [covered, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨g,hgF,hvg⟩)
    · rcases Finset.mem_insert.mp hgs with rfl | hgF
      · exact hf v hvg (by simp only [covered, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨f,hfF,hv⟩)
      · exact hF.2 f hfF g hgF hfg v hv hvg

lemma step_subset_shadow {n : ℕ} (a b : ℝ) (S : State n) (e : Edge n) (t : ℝ) (c : Bool)
    (ht : t < b) (hS : S.actual ⊆ S.shadow) :
    (step a b S e t c).actual ⊆ (step a b S e t c).shadow := by
  classical
  unfold step
  split_ifs <;> simp_all [Finset.insert_subset_insert]
  exact hS.trans (Finset.subset_insert _ _)

lemma step_matching {n : ℕ} (a b : ℝ) (hab : a ≤ b) (S : State n)
    (e : Edge n) (t : ℝ) (c : Bool)
    (hS : IsMatching S.actual) (he : ¬ e.IsDiag) (hsub : t < b → S.actual ⊆ S.shadow) :
    IsMatching (step a b S e t c).actual := by
  classical
  unfold step
  split_ifs
  all_goals first
    | exact hS
    | apply matching_insert hS he
      first
      | exact free_of_subset (hsub (by linarith)) (by assumption)
      | exact (by aesop)

lemma safe_fold {n : ℕ} (a b : ℝ) (hab : a ≤ b) (l : List (Edge n × ℝ × Bool))
    (hl : (l.map (fun o => o.2.1)).Pairwise (· ≤ ·))
    (he : ∀ o ∈ l, ¬ o.1.IsDiag) (S : State n) (hS : IsMatching S.actual)
    (hsub : (∃ o ∈ l, o.2.1 < b) → S.actual ⊆ S.shadow) :
    IsMatching (l.foldl (fun S o => step a b S o.1 o.2.1 o.2.2) S).actual := by
  induction l generalizing S with
  | nil => exact hS
  | cons o l ih =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hl
    apply ih hl.2 (fun x hx => he x (List.mem_cons_of_mem _ hx))
    · exact step_matching a b hab S o.1 o.2.1 o.2.2 hS (he o (by simp))
        (fun ht => hsub ⟨o,by simp,ht⟩)
    · rintro ⟨x,hx,hxb⟩
      have ht : o.2.1 < b := lt_of_le_of_lt (hl.1 x hx) hxb
      exact step_subset_shadow a b S o.1 o.2.1 o.2.2 ht (hsub ⟨o,by simp,ht⟩)

lemma run_matching {n : ℕ} (a b : ℝ) (hab : a ≤ b) (l : List (Edge n × ℝ × Bool))
    (hl : (l.map (fun o => o.2.1)).Pairwise (· ≤ ·))
    (he : ∀ o ∈ l, ¬ o.1.IsDiag) : IsMatching (run a b l).actual := by
  apply safe_fold a b hab l hl he (initial n)
  · simp [IsMatching,initial]
  · simp [initial]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma covered_insert {n : ℕ} (A : EdgeSet n) (e : Edge n) :
    covered (insert e A) = covered A ∪ e.toFinset := by
  ext v
  simp only [covered, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_union, Sym2.mem_toFinset]
  aesop

lemma free_insert_iff {n : ℕ} (A : EdgeSet n) (e f : Edge n) :
    free (insert f A) e ↔ free A e ∧ ∀ v, v ∈ e → v ∉ f := by
  simp only [free, covered_insert, Finset.mem_union, Sym2.mem_toFinset, not_or]
  aesop

lemma matching_meeting_bound {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (f : Edge n)
    (S : EdgeSet n) (hSM : S ⊆ M) (hS : ∀ e ∈ S, ∃ v, v ∈ e ∧ v ∈ f) :
    S.card ≤ 2 := by
  choose vert hvert using fun e : S => hS e.val e.property
  let v : S → f.toFinset := fun e => ⟨vert e, Sym2.mem_toFinset.mpr (hvert e).2⟩
  have hinj : Function.Injective v := by
    intro e g heg
    apply Subtype.ext
    by_contra hne
    exact hM.2 e.val (hSM e.property) g.val (hSM g.property) hne (vert e)
      (hvert e).1 (by have heq := congrArg Subtype.val heg; change vert e = vert g at heq; exact heq.symm ▸ (hvert g).1)
  have hh : S.card ≤ f.toFinset.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective v hinj
  exact hh.trans (by rw [Sym2.card_toFinset]; split_ifs <;> omega)

lemma unmatched_step_bound {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (A : EdgeSet n) (f : Edge n) :
    (M.filter (free A)).card + (if f ∈ M then 1 else 0) ≤
      (M.filter (free (insert f A))).card + 2 := by
  let X := M.filter (free A)
  let Y := M.filter (free (insert f A))
  have hYX : Y ⊆ X := by
    intro e he
    obtain ⟨he,hfree⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨he,(free_insert_iff A e f).mp hfree |>.1⟩
  let S := X \ Y
  have hSM : S ⊆ M := (Finset.sdiff_subset.trans (Finset.filter_subset _ _))
  have hS : ∀ e ∈ S, ∃ v, v ∈ e ∧ v ∈ f := by
    intro e he
    obtain ⟨hx,hy⟩ := Finset.mem_sdiff.mp he
    have hx' := Finset.mem_filter.mp hx
    have hnot : ¬ free (insert f A) e := by
      intro hh; exact hy (Finset.mem_filter.mpr ⟨hx'.1,hh⟩)
    rw [free_insert_iff] at hnot
    push_neg at hnot
    exact hnot hx'.2
  have hcard : X.card = Y.card + S.card := by
    have : S.card + Y.card = X.card := Finset.card_sdiff_add_card_eq_card hYX
    omega
  by_cases hf : f ∈ M
  · have hsub : S ⊆ {f} := by
      intro e he
      have heM := hSM he
      obtain ⟨v,hve,hvf⟩ := hS e he
      by_cases heq : e = f
      · simp [heq]
      · exact False.elim (hM.2 e heM f hf heq v hve hvf)
    have hs1 : S.card ≤ 1 := by simpa using Finset.card_le_card hsub
    simp only [hf,↓reduceIte]
    change X.card + 1 ≤ Y.card + 2
    omega
  · have hs2 := matching_meeting_bound M hM f S hSM hS
    simp only [hf,↓reduceIte,add_zero]
    change X.card ≤ Y.card + 2
    omega

lemma unmatched_extension_bound {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (A F : EdgeSet n) :
    (M.filter (free A)).card + (M ∩ F).card ≤
      (M.filter (free (A ∪ F))).card + 2*F.card := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert f F hf ih =>
    have hstep := unmatched_step_bound M hM (A ∪ F) f
    have hu : A ∪ insert f F = insert f (A ∪ F) := by ext e; simp
    rw [hu, Finset.card_insert_of_notMem hf]
    by_cases hfM : f ∈ M
    · have hnot : f ∉ M ∩ F := by simp [hf]
      have hi : M ∩ insert f F = insert f (M ∩ F) := by ext e; simp [hfM]
      rw [hi,Finset.card_insert_of_notMem hnot]
      simp only [hfM,↓reduceIte] at hstep
      omega
    · have hi : M ∩ insert f F = M ∩ F := by ext e; simp; aesop
      rw [hi]
      simp only [hfM,↓reduceIte,add_zero] at hstep
      omega

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

/-- Covered vertices of a greedy state either agree, or differ by the new vertex and
one moving endpoint. The moving endpoint can be present on either side. -/
def CoverCoupling {n : ℕ} (z : Fin n) (C D : Finset (Fin n)) : Prop :=
  C = D ∨ ∃ u, (C = insert z (insert u D) ∧ u ∉ D) ∨ (C = insert z (D.erase u) ∧ u ∈ D)

lemma cover_coupling_step {n : ℕ} (z x y : Fin n) (hxy : x ≠ y)
    (C D : Finset (Fin n)) (hz : z ∉ D) (h : CoverCoupling z C D) :
    CoverCoupling z (if x ∉ C ∧ y ∉ C then insert x (insert y C) else C)
      (if z ≠ x ∧ z ≠ y ∧ x ∉ D ∧ y ∉ D then insert x (insert y D) else D) := by
  rcases h with hCD | ⟨u,(⟨rfl,hu⟩ | ⟨rfl,hu⟩)⟩
  · subst C
    by_cases hf : x ∉ D ∧ y ∉ D
    · rw [if_pos hf]
      by_cases hzx : z = x
      · subst x
        simp only [ne_self_iff_false,false_and,↓reduceIte]
        right
        exact ⟨y,Or.inl ⟨rfl,hf.2⟩⟩
      · by_cases hzy : z = y
        · subst y
          simp only [ne_self_iff_false,false_and,and_false,↓reduceIte]
          right
          refine ⟨x,Or.inl ⟨?_,hf.1⟩⟩
          ext v; simp only [Finset.mem_insert]; tauto
        · rw [if_pos ⟨hzx,hzy,hf⟩]
          exact Or.inl rfl
    · have hn : ¬ (z ≠ x ∧ z ≠ y ∧ x ∉ D ∧ y ∉ D) := fun hh => hf hh.2.2
      rw [if_neg hf,if_neg hn]
      exact Or.inl rfl
  · by_cases hf : x ∉ insert z (insert u D) ∧ y ∉ insert z (insert u D)
    · have hx : x ≠ z ∧ x ≠ u ∧ x ∉ D := by simpa only [Finset.mem_insert,not_or] using hf.1
      have hy : y ≠ z ∧ y ≠ u ∧ y ∉ D := by simpa only [Finset.mem_insert,not_or] using hf.2
      have hg : z ≠ x ∧ z ≠ y ∧ x ∉ D ∧ y ∉ D := ⟨hx.1.symm,hy.1.symm,hx.2.2,hy.2.2⟩
      rw [if_pos hf,if_pos hg]
      right
      refine ⟨u,Or.inl ⟨?_,?_⟩⟩
      · ext v; simp only [Finset.mem_insert]; tauto
      · simp only [Finset.mem_insert,not_or]
        exact ⟨hx.2.1.symm,hy.2.1.symm,hu⟩
    · by_cases hg : z ≠ x ∧ z ≠ y ∧ x ∉ D ∧ y ∉ D
      · rw [if_neg hf,if_pos hg]
        have hxu : x = u ∨ y = u := by
          by_contra hn
          push_neg at hn
          apply hf
          simp only [Finset.mem_insert,not_or]
          exact ⟨⟨hg.1.symm,hn.1,hg.2.2.1⟩,⟨hg.2.1.symm,hn.2,hg.2.2.2⟩⟩
        rcases hxu with rfl | rfl
        · right
          refine ⟨y,Or.inr ⟨?_,by simp⟩⟩
          ext v
          simp only [Finset.mem_insert,Finset.mem_erase]
          grind
        · right
          refine ⟨x,Or.inr ⟨?_,by simp⟩⟩
          ext v
          simp only [Finset.mem_insert,Finset.mem_erase]
          grind
      · rw [if_neg hf,if_neg hg]
        exact Or.inr ⟨u,Or.inl ⟨rfl,hu⟩⟩
  · by_cases hf : x ∉ insert z (D.erase u) ∧ y ∉ insert z (D.erase u)
    · by_cases hg : z ≠ x ∧ z ≠ y ∧ x ∉ D ∧ y ∉ D
      · rw [if_pos hf,if_pos hg]
        right
        refine ⟨u,Or.inr ⟨?_,by simp [hu]⟩⟩
        ext v
        simp only [Finset.mem_insert,Finset.mem_erase]
        grind
      · rw [if_pos hf,if_neg hg]
        have hxz : x ≠ z := fun hh => hf.1 (by simp [hh])
        have hyz : y ≠ z := fun hh => hf.2 (by simp [hh])
        have hxu : x = u ∨ y = u := by
          by_contra hn
          push_neg at hn
          apply hg
          refine ⟨hxz.symm,hyz.symm,?_,?_⟩
          · intro hxD
            exact hf.1 (by simp [hxD,hn.1])
          · intro hyD
            exact hf.2 (by simp [hyD,hn.2])
        rcases hxu with rfl | rfl
        · right
          refine ⟨y,Or.inl ⟨?_,?_⟩⟩
          · ext v; simp only [Finset.mem_insert,Finset.mem_erase]; grind
          · intro hyD
            exact hf.2 (by simp [hyD,hxy.symm])
        · right
          refine ⟨x,Or.inl ⟨?_,?_⟩⟩
          · ext v; simp only [Finset.mem_insert,Finset.mem_erase]; grind
          · intro hxD
            exact hf.1 (by simp [hxD,hxy])
    · have hn : ¬ (z ≠ x ∧ z ≠ y ∧ x ∉ D ∧ y ∉ D) := by
        intro hg
        apply hf
        constructor
        · simp only [Finset.mem_insert,Finset.mem_erase,not_or,not_and]
          exact ⟨hg.1.symm,fun _ => hg.2.2.1⟩
        · simp only [Finset.mem_insert,Finset.mem_erase,not_or,not_and]
          exact ⟨hg.2.1.symm,fun _ => hg.2.2.2⟩
      rw [if_neg hf,if_neg hn]
      exact Or.inr ⟨u,Or.inr ⟨rfl,hu⟩⟩

lemma covered_greedy_pair {n : ℕ} (F : EdgeSet n) (x y : Fin n) :
    covered (if free F s(x,y) then insert s(x,y) F else F) =
      if x ∉ covered F ∧ y ∉ covered F then insert x (insert y (covered F)) else covered F := by
  have hf : free F s(x,y) ↔ x ∉ covered F ∧ y ∉ covered F := by
    simp only [free,Sym2.mem_iff]
    aesop
  by_cases h : free F s(x,y)
  · rw [if_pos h,if_pos (hf.mp h),covered_insert,Sym2.toFinset_mk_eq]
    ext v; simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]; tauto
  · rw [if_neg h,if_neg (fun hh => h (hf.mpr hh))]

lemma covered_deleted_pair {n : ℕ} (F : EdgeSet n) (z x y : Fin n) :
    covered (if z ∉ s(x,y) then (if free F s(x,y) then insert s(x,y) F else F) else F) =
      if z ≠ x ∧ z ≠ y ∧ x ∉ covered F ∧ y ∉ covered F then insert x (insert y (covered F)) else covered F := by
  by_cases hz : z ∉ s(x,y)
  · rw [if_pos hz,covered_greedy_pair]
    have hzx : z ≠ x ∧ z ≠ y := by simpa only [Sym2.mem_iff,not_or] using hz
    simp [hzx.1,hzx.2]
  · rw [if_neg hz]
    have hn : ¬ (z ≠ x ∧ z ≠ y ∧ x ∉ covered F ∧ y ∉ covered F) := by
      intro hh
      exact hz (by simpa only [Sym2.mem_iff,not_or] using And.intro hh.1 hh.2.1)
    rw [if_neg hn]

lemma greedy_fold_coupling {n : ℕ} (z : Fin n) (l : List (Edge n))
    (hl : ∀ e ∈ l, ¬ e.IsDiag) (F H : EdgeSet n) (hz : z ∉ covered H)
    (hc : CoverCoupling z (covered F) (covered H)) :
    CoverCoupling z
      (covered (l.foldl (fun F e => if free F e then insert e F else F) F))
      (covered ((l.filter (fun e => z ∉ e)).foldl (fun H e => if free H e then insert e H else H) H)) := by
  induction l generalizing F H with
  | nil => exact hc
  | cons e l ih =>
    let F' := if free F e then insert e F else F
    let H' := if z ∉ e then (if free H e then insert e H else H) else H
    have hz' : z ∉ covered H' := by
      dsimp only [H']
      by_cases hze : z ∉ e
      · rw [if_pos hze]
        by_cases hfree : free H e
        · rw [if_pos hfree,covered_insert]
          simpa only [Finset.mem_union,Sym2.mem_toFinset,not_or] using And.intro hz hze
        · rw [if_neg hfree]; exact hz
      · rw [if_neg hze]; exact hz
    have hc' : CoverCoupling z (covered F') (covered H') := by
      induction e using Sym2.inductionOn with
      | hf x y =>
        have hxy : x ≠ y := by simpa only [Sym2.isDiag_iff_proj_eq] using hl s(x,y) (by simp)
        dsimp [F',H']
        rw [covered_greedy_pair,covered_deleted_pair]
        exact cover_coupling_step z x y hxy (covered F) (covered H) hz hc
    have ht := ih (fun f hf => hl f (List.mem_cons_of_mem _ hf)) F' H' hz' hc'
    by_cases hze : z ∉ e
    · simpa [List.filter_cons,F',H',hze] using ht
    · have hmem : z ∈ e := not_not.mp hze
      simpa [List.filter_cons,F',H',hmem] using ht

lemma greedy_coupling {n : ℕ} (z : Fin n) (l : List (Edge n)) (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    CoverCoupling z (covered (greedy l)) (covered (greedy (l.filter (fun e => z ∉ e)))) := by
  exact greedy_fold_coupling z l hl ∅ ∅ (by simp [covered]) (Or.inl rfl)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma greedy_fold_avoids {n : ℕ} (z : Fin n) (l : List (Edge n))
    (hl : ∀ e ∈ l, z ∉ e) (F : EdgeSet n) (hz : z ∉ covered F) :
    z ∉ covered (l.foldl (fun F e => if free F e then insert e F else F) F) := by
  induction l generalizing F with
  | nil => exact hz
  | cons e l ih =>
    simp only [List.foldl_cons]
    apply ih (fun f hf => hl f (List.mem_cons_of_mem _ hf))
    by_cases he : free F e
    · rw [if_pos he,covered_insert]
      simpa only [Finset.mem_union,Sym2.mem_toFinset,not_or] using And.intro hz (hl e (by simp))
    · rw [if_neg he]; exact hz

lemma greedy_avoids_deleted {n : ℕ} (z : Fin n) (l : List (Edge n)) :
    z ∉ covered (greedy (l.filter (fun e => z ∉ e))) := by
  apply greedy_fold_avoids z (l.filter (fun e => z ∉ e)) _ ∅ (by simp [covered])
  intro e he
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2

lemma coupling_weight_monotone {n : ℕ} (z : Fin n) (C D : Finset (Fin n))
    (hz : z ∉ D) (hc : CoverCoupling z C D) (ω : Fin n → ℝ)
    (hω : ∀ v, 0 ≤ ω v) (hmax : ∀ v, ω v ≤ ω z) :
    (∑ v ∈ D, ω v) ≤ ∑ v ∈ C, ω v := by
  rcases hc with rfl | ⟨u,(⟨rfl,hu⟩ | ⟨rfl,hu⟩)⟩
  · exact le_rfl
  · by_cases hzu : z = u
    · subst z
      rw [Finset.insert_idem,Finset.sum_insert hu]
      linarith [hω u]
    · rw [Finset.sum_insert (by simp [hzu,hz]),Finset.sum_insert hu]
      linarith [hω u,hω z]
  · rw [Finset.sum_insert (by simpa only [Finset.mem_erase,not_and] using (fun _ => hz))]
    have hh := Finset.sum_erase_add (f:=ω) D hu
    linarith [hmax u]

lemma greedy_weight_monotone {n : ℕ} (z : Fin n) (l : List (Edge n))
    (hl : ∀ e ∈ l, ¬ e.IsDiag) (ω : Fin n → ℝ)
    (hω : ∀ v, 0 ≤ ω v) (hmax : ∀ v, ω v ≤ ω z) :
    (∑ v ∈ covered (greedy (l.filter (fun e => z ∉ e))), ω v) ≤
      ∑ v ∈ covered (greedy l), ω v :=
  coupling_weight_monotone z _ _ (greedy_avoids_deleted z l) (greedy_coupling z l hl) ω hω hmax

lemma weighted_cover_count {n : ℕ} (A B C : Finset (Fin n)) :
    (∑ v ∈ C, ((3:ℝ)*(if v ∈ A then 1 else 0) + 2*(if v ∈ B then 1 else 0))) =
      3*((A ∩ C).card:ℝ)+2*((B ∩ C).card:ℝ) := by
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  have hsum (F : Finset (Fin n)) : (∑ v ∈ C, (if v ∈ F then (1:ℝ) else 0)) = ((F ∩ C).card:ℝ) := by
    have hn : (∑ v ∈ C, if v ∈ F then (1:ℕ) else 0) = (F ∩ C).card := by
      rw [←Finset.card_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter,Finset.mem_inter]
      tauto
    exact_mod_cast hn
  rw [hsum,hsum]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma local_edges_loopless {n : ℕ} (d : Local n) (hd : d.Valid) (r : EdgeSet n) (hr : r ⊆ d.potential)
    (e : Edge n) (he : e ∈ d.base ∨ e ∈ r) : ¬ e.IsDiag := by
  rcases hd with ⟨hx,hbase,hx1Y,hx2Y,hmarks,hcard,hpot⟩
  rcases he with he | he
  · exact (hbase e he).1
  · obtain ⟨x,hx,y,hy,rfl⟩ := hpot e (hr he)
    rw [Sym2.mk_isDiag_iff]
    intro hxy
    rcases Finset.mem_insert.mp hx with hxeq | hxeq
    · exact hx1Y (hxeq ▸ (hxy.symm ▸ hy))
    · have hxeq' : x = d.x2 := Finset.mem_singleton.mp hxeq
      exact hx2Y (hxeq' ▸ (hxy.symm ▸ hy))

lemma local_delete_run {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n) :
    oneRun d σ r = greedy ((σ.filter (fun e => e ∈ d.base ∨ e ∈ r)).filter (fun e => d.x2 ∉ e)) := by
  unfold oneRun
  congr 1
  rw [List.filter_filter]
  congr 1
  funext e
  by_cases he : e ∈ d.base ∨ e ∈ r <;> by_cases hz : d.x2 ∈ e <;> simp [he,hz]

lemma local_comparison {n : ℕ} (d : Local n) (hd : d.Valid)
    (σ : List (Edge n)) (r : EdgeSet n) (hr : r ⊆ d.potential) :
    3*N d σ r+2*R d σ r ≥ 3*N1 d σ r+2*R1 d σ r := by
  let l := σ.filter (fun e => e ∈ d.base ∨ e ∈ r)
  let A : Finset (Fin n) := {d.x1,d.x2}
  let ω : Fin n → ℝ := fun v => 3*(if v ∈ A then 1 else 0)+2*(if v ∈ d.marked then 1 else 0)
  have hdis : Disjoint A d.marked := by
    rw [Finset.disjoint_left]
    intro v hv hvm
    have hvY := hd.2.2.2.2.1 hvm
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hd.2.2.1 hvY
    · exact hd.2.2.2.1 (Finset.mem_singleton.mp hv ▸ hvY)
  have hbound (v : Fin n) : 0 ≤ ω v ∧ ω v ≤ 3 := by
    dsimp only [ω]
    by_cases hA : v ∈ A
    · have hB : v ∉ d.marked := fun h => Finset.disjoint_left.mp hdis hA h
      norm_num [hA,hB]
    · by_cases hB : v ∈ d.marked <;> norm_num [hA,hB]
  have hwz : ω d.x2 = 3 := by
    have hn : d.x2 ∉ d.marked := fun h => Finset.disjoint_left.mp hdis (by simp [A]) h
    simp [ω,A,hn]
  have hweight := greedy_weight_monotone d.x2 l
    (fun e he => local_edges_loopless d hd r hr e (of_decide_eq_true (List.mem_filter.mp he).2)) ω
    (fun v => (hbound v).1) (fun v => by rw [hwz]; exact (hbound v).2)
  rw [weighted_cover_count A d.marked,weighted_cover_count A d.marked] at hweight
  have hsmall : greedy (l.filter (fun e => d.x2 ∉ e)) = oneRun d σ r := (local_delete_run d σ r).symm
  have hbig : greedy l = localRun d σ r := rfl
  rw [hsmall,hbig] at hweight
  have hz : d.x2 ∉ covered (oneRun d σ r) := by
    rw [←hsmall]
    exact greedy_avoids_deleted d.x2 l
  have hpair : A ∩ covered (oneRun d σ r) = {d.x1} ∩ covered (oneRun d σ r) := by
    ext v
    simp only [A,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hv,hvc⟩
      rcases hv with hv | rfl
      · exact ⟨hv,hvc⟩
      · exact (hz hvc).elim
    · rintro ⟨rfl,hvc⟩
      exact ⟨Or.inl rfl,hvc⟩
  rw [hpair] at hweight
  exact hweight

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

def lateGraph {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (w : Sample G) : EdgeSet n :=
  (graphEdges G).filter (fun e => ∃ he : e ∈ G.edgeSet, b ≤ w.1 ⟨e,he⟩)

lemma measurable_lateGraph {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) : Measurable (lateGraph G b) := by
  rw [measurable_finset_iff]
  intro e
  apply measurableSet_setOfPred.mp
  by_cases he : e ∈ G.edgeSet
  · have heq : {w : Sample G | e ∈ lateGraph G b w} = {w | b ≤ w.1 ⟨e,he⟩} := by
      ext w
      simp only [lateGraph,graphEdges,Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_setOf_eq]
      constructor
      · rintro ⟨_,⟨h,hb⟩⟩; exact hb
      · intro hb; exact ⟨he,he,hb⟩
    rw [heq]
    exact measurableSet_le measurable_const ((measurable_pi_apply (⟨e,he⟩ : G.edgeSet)).comp measurable_fst)
  · have heq : {w : Sample G | e ∈ lateGraph G b w} = ∅ := by
      ext w
      simp [lateGraph,graphEdges,he]
    rw [heq]
    exact MeasurableSet.empty

lemma measurable_otherX {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℝ) (h : History n) (e : Edge n) :
    Measurable (otherX G a h e) := by
  let f : Coins G → Finset (Fin n) := fun c => covered ((early a h).filter fun f => f ≠ e ∧ ∃ hf : f ∈ G.edgeSet, c ⟨f,hf⟩ = true)
  convert! (measurable_of_finite f).comp (measurable_snd : Measurable (Prod.snd : Sample G → Coins G)) using 1

def backgroundData {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (h : History n) (e : Edge n)
    (w : Sample G) : EdgeSet n × Finset (Fin n) := (lateGraph G b w,otherX G a h e w)

def backgroundFromData {n : ℕ} (h : History n) (e : Edge n) (z : EdgeSet n × Finset (Fin n)) : EdgeSet n :=
  z.1.filter (fun f => (∀ v, v ∈ e → v ∉ f) ∧ ((∀ v, v ∈ f → v ∈ Yset h) ∨
    ∃ x y, f = s(x,y) ∧ x ∈ z.2 ∧ y ∈ Yset h))

def augmentedFromData {n : ℕ} (h : History n) (e : Edge n) (z : EdgeSet n × Finset (Fin n)) : EdgeSet n :=
  backgroundFromData h e z ∪ (z.1.filter (fun f => ∃ x y, f = s(x,y) ∧ x ∈ e ∧ y ∈ Yset h))

lemma background_data_eq {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (h : History n) (e : Edge n) (w : Sample G) :
    background G a b h e w = backgroundFromData h e (backgroundData G a b h e w) := by
  ext f
  change (f ∈ (graphEdges G).filter (fun f => (∀ v, v ∈ e → v ∉ f) ∧
    (∃ hf : f ∈ G.edgeSet, b ≤ w.1 ⟨f,hf⟩) ∧ ((∀ v, v ∈ f → v ∈ Yset h) ∨
    ∃ x y, f = s(x,y) ∧ x ∈ otherX G a h e w ∧ y ∈ Yset h))) ↔
    f ∈ (lateGraph G b w).filter (fun f => (∀ v, v ∈ e → v ∉ f) ∧
      ((∀ v, v ∈ f → v ∈ Yset h) ∨ ∃ x y, f = s(x,y) ∧ x ∈ otherX G a h e w ∧ y ∈ Yset h))
  have hl : f ∈ lateGraph G b w ↔ f ∈ graphEdges G ∧ ∃ hf : f ∈ G.edgeSet, b ≤ w.1 ⟨f,hf⟩ := Finset.mem_filter
  simp only [Finset.mem_filter,hl]
  tauto

lemma augmented_data_eq {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (h : History n) (e : Edge n) (w : Sample G) :
    augmented G a b h e w = augmentedFromData h e (backgroundData G a b h e w) := by
  rw [augmented,augmentedFromData,background_data_eq]
  congr 1
  ext f
  simp only [backgroundData,lateGraph,Finset.mem_filter]
  tauto

lemma measurable_backgroundData {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (h : History n) (e : Edge n) :
    Measurable (backgroundData G a b h e) := (measurable_lateGraph G b).prodMk (measurable_otherX G a h e)

lemma measurable_background {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (h : History n) (e : Edge n) :
    Measurable (background G a b h e) := by
  have hh := (measurable_of_finite (backgroundFromData h e)).comp (measurable_backgroundData G a b h e)
  convert! hh using 1
  funext w
  exact background_data_eq G a b h e w

lemma measurable_augmented {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (h : History n) (e : Edge n) :
    Measurable (augmented G a b h e) := by
  have hh := (measurable_of_finite (augmentedFromData h e)).comp (measurable_backgroundData G a b h e)
  convert! hh using 1
  funext w
  exact augmented_data_eq G a b h e w

lemma measurable_coupledRun {n : ℕ} (G : SimpleGraph (Fin n)) (F : Sample G → EdgeSet n) (hF : Measurable F) :
    Measurable (fun w => coupledRun G (F w) w) := by
  letI : MeasurableSpace (Equiv.Perm (Fin (Fintype.card G.edgeSet))) := ⊤
  letI : MeasurableSingletonClass (Equiv.Perm (Fin (Fintype.card G.edgeSet))) := ⟨fun _ => trivial⟩
  let enum := (Fintype.equivFin G.edgeSet).symm
  have hsort : Measurable (fun t : Times G => Tuple.sort (t ∘ enum)) := by
    apply measurable_to_countable'
    intro σ
    exact (sort_fiber_measurable σ).preimage (measurable_pi_iff.mpr fun i => measurable_pi_apply (enum i))
  let f : Equiv.Perm (Fin (Fintype.card G.edgeSet)) × EdgeSet n → EdgeSet n := fun z =>
    greedy (((List.ofFn (z.1.trans enum)).map Subtype.val).filter (fun e => e ∈ z.2))
  have hh := (measurable_of_finite f).comp ((hsort.comp measurable_fst).prodMk hF)
  convert! hh using 1

lemma integrable_coupledScore {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (a b : ℝ) (h : History n) (e : Edge n)
    (μ : Measure (Sample G)) [IsFiniteMeasure μ] : Integrable (coupledScore G M a b h e) μ := by
  have hMB := measurable_coupledRun G (background G a b h e) (measurable_background G a b h e)
  have hME := measurable_coupledRun G (augmented G a b h e) (measurable_augmented G a b h e)
  let f : EdgeSet n × EdgeSet n → ℝ := fun z => 3*count (covered {e}) z.2+2*count (references M h e) z.2+count (references M h e) z.1
  convert! integrable_finite_comp μ _ (hMB.prodMk hME) f using 1

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical ProbabilityTheory
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma fold_min_le {α : Type*} (l : List α) (f : α → ℝ) (s : ℝ) :
    l.foldl (fun r x => min r (f x)) s ≤ s := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons x l ih => exact (ih _).trans (min_le_left _ _)

lemma lowerTime_le {n : ℕ} (b : ℝ) (h : History n) (e : Edge n) : lowerTime b h e ≤ b :=
  fold_min_le _ _ _

lemma residual_probability {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : b < 1)
    (h : History n) : IsProbabilityMeasure (residualLaw G b h) := by
  have hc (e : G.edgeSet) : IsProbabilityMeasure
      (if e.val ∈ h.accepted then Measure.dirac (h.time e.val)
       else (ENNReal.ofReal (1-lowerTime b h e.val))⁻¹ • volume.restrict (Set.Ioo (lowerTime b h e.val) 1)) := by
    split_ifs
    · infer_instance
    · have hl : lowerTime b h e.val < 1 := (lowerTime_le b h e.val).trans_lt hb
      constructor
      simp only [Measure.smul_apply,Measure.restrict_apply_univ,Real.volume_Ioo,smul_eq_mul]
      exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hl))) ENNReal.ofReal_ne_top
  unfold residualLaw
  letI (e : G.edgeSet) := hc e
  infer_instance

lemma conditional_integral_disintegration {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : b < 1)
    (hres : ∀ A : Set (Times G), MeasurableSet A → Measurable (fun h : History n => residualLaw G b h A))
    (hdis : ∀ A : Set (Times G), MeasurableSet A →
      arrivalLaw G A = ∫⁻ h, residualLaw G b h A ∂historyLaw G b)
    (f : Sample G → ℝ) (hf : Integrable f (sampleLaw G (5/11))) :
    Integrable (fun h => ∫ w, f w ∂conditionalLaw G b (5/11) h) (historyLaw G b) ∧
    (∫ w, f w ∂sampleLaw G (5/11)) =
      ∫ h, ∫ w, f w ∂conditionalLaw G b (5/11) h ∂historyLaw G b := by
  let κ : Kernel (History n) (Times G) := ⟨residualLaw G b,Measure.measurable_of_measurable_coe _ hres⟩
  haveI : IsMarkovKernel κ := ⟨fun h => residual_probability G b hb h⟩
  haveI := coin_probability G
  haveI := arrival_probability G
  haveI : IsFiniteMeasure (historyLaw G b) := by unfold historyLaw; infer_instance
  have hmarg : κ ∘ₘ historyLaw G b = arrivalLaw G := by
    ext A hA
    rw [Measure.bind_apply hA κ.aemeasurable]
    exact (hdis A hA).symm
  let η := κ ×ₖ Kernel.const (History n) (coinLaw G (5/11))
  have heq : η ∘ₘ historyLaw G b = sampleLaw G (5/11) := by
    have hh := Kernel.prod_const_comp (Kernel.const Unit (historyLaw G b)) κ (coinLaw G (5/11))
    have hh' := congrArg (fun K : Kernel Unit (Sample G) => K ()) hh
    simpa only [Kernel.comp_apply,Kernel.const_apply,Kernel.prod_apply,hmarg,sampleLaw,η] using hh'
  have hi : Integrable f (η ∘ₘ historyLaw G b) := heq.symm ▸ hf
  have hint := ProbabilityTheory.Kernel.integral_comp (κ:=Kernel.const Unit (historyLaw G b)) (η:=η) (a:=()) hi
  have hcomp : Integrable f ((η ∘ₖ Kernel.const Unit (historyLaw G b)) ()) := hi
  have hins := hcomp.integral_comp
  constructor
  · simpa only [η,Kernel.prod_apply,Kernel.const_apply,κ,Kernel.coe_mk,conditionalLaw] using hins
  · change (∫ w, f w ∂(η ∘ₘ historyLaw G b)) = (∫ h, ∫ w, f w ∂η h ∂historyLaw G b) at hint
    rw [heq] at hint
    simpa only [η,Kernel.prod_apply,Kernel.const_apply,κ,Kernel.coe_mk,conditionalLaw] using hint

end
end FengLiYangMatching.General
open MeasureTheory Classical
namespace FengLiYangMatching.General
noncomputable section

lemma coin_probability_interval {n : ℕ} (G : SimpleGraph (Fin n)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (coinLaw G p) := by
  have hm : p.toNNReal+(1-p).toNNReal = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal p hp0,Real.coe_toNNReal (1-p) (sub_nonneg.mpr hp1),NNReal.coe_one]
    ring
  haveI : IsProbabilityMeasure (RandomOrderCRS.survivalLaw p) := by
    constructor
    simp only [RandomOrderCRS.survivalLaw,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply_of_mem,
      Set.mem_univ,ENNReal.smul_one]
    rw [←ENNReal.coe_add,hm]
    rfl
  unfold coinLaw
  infer_instance

lemma conditional_probability {n : ℕ} (G : SimpleGraph (Fin n)) (b p : ℝ) (hb : b < 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : History n) : IsProbabilityMeasure (conditionalLaw G b p h) := by
  haveI := residual_probability G b hb h
  haveI := coin_probability_interval G p hp0 hp1
  unfold conditionalLaw
  infer_instance

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical FengLiYangMatching.General
open scoped BigOperators

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3) :
    ∀ᵐ h ∂historyLaw G b, ∀ e ∈ early a h, ∀ B : EdgeSet n,
      0 < conditionalLaw G b p h {w | background G a b h e w = B} →
      Integrable (coupledScore G M a b h e) (backgroundLaw G a b p h e B) ∧
      (∫ w, coupledScore G M a b h e w ∂backgroundLaw G a b p h e B)
        ≥ 3 * (references M h e).card := by
  have hb1 : b < 1 := hb.trans_lt (by norm_num)
  have hp1 : p ≤ 1 := hp2.trans (by norm_num)
  filter_upwards [conditional_local_experiment G M hMG hM hmax a b p ha hab hb hp0 hp2] with h hh
  intro e he B hB
  haveI := conditional_probability G b p hb1 hp0 hp1 h
  haveI : IsProbabilityMeasure (backgroundLaw G a b p h e B) := by
    constructor
    simp only [backgroundLaw,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ne_of_gt hB) (measure_ne_top _ _)
  obtain ⟨hd,hpartners,hq,hq1,hEq⟩ := hh e he B hB
  refine ⟨integrable_coupledScore G M a b h e (backgroundLaw G a b p h e B),?_⟩
  have hbound := local_recovery_bound _ hd hpartners _ hq hq1
  rw [←hEq] at hbound
  exact hbound

