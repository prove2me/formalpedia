-- Prove2me | solution 1 for FengLiYangMatching.General.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T22:22:57.819148+00:00
-- url     : https://prove2.me/submissions/8ef52435-3dd6-4d57-b3b1-4a785614ac1a

import Definitions.Def_FengLiYangMatching_General_Local
import Mathlib
import Definitions.Def_FengLiYangMatching_General_Process
import Theorems.Thm_FengLiYangMatching_General_lemma_4_1
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
open MeasureTheory Finset Classical ProbabilityTheory
namespace FengLiYangMatching.General
noncomputable section

lemma arrival_injective {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ᵐ t ∂arrivalLaw G, Function.Injective t := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  haveI : IsProbabilityMeasure μ := ⟨by dsimp [μ]; simp⟩
  haveI : NullSingletonClass μ := by dsimp [μ]; infer_instance
  have hd : (μ.prod μ) {z : ℝ × ℝ | z.1 = z.2} = 0 := by
    rw [Measure.prod_apply (measurableSet_eq_fun (show Measurable (fun z : ℝ × ℝ => z.1) from measurable_fst) (show Measurable (fun z : ℝ × ℝ => z.2) from measurable_snd))]
    simp
  have hpair : ∀ e f : G.edgeSet, e ≠ f → ∀ᵐ t ∂arrivalLaw G, t e ≠ t f := by
    intro e f hef
    have hind := (iIndepFun_pi (μ := fun _ : G.edgeSet => μ) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hef
    have hm : (arrivalLaw G).map (fun t => (t e,t f)) = μ.prod μ := by
      have hh := (indepFun_iff_map_prod_eq_prod_map_map
        (measurable_pi_apply e).aemeasurable (measurable_pi_apply f).aemeasurable).mp hind
      rw [(measurePreserving_eval (fun _ : G.edgeSet => μ) e).map_eq,
        (measurePreserving_eval (fun _ : G.edgeSet => μ) f).map_eq] at hh
      exact hh
    apply (ae_iff).mpr
    have hh : ((arrivalLaw G).map (fun t : Times G => (t e,t f))) {z : ℝ × ℝ | z.1 = z.2} =
        (arrivalLaw G) ((fun t : Times G => (t e,t f)) ⁻¹' {z : ℝ × ℝ | z.1 = z.2}) :=
      Measure.map_apply ((measurable_pi_apply e).prodMk (measurable_pi_apply f))
        (measurableSet_eq_fun measurable_fst measurable_snd)
    rw [hm,hd] at hh
    simpa using hh.symm
  have hh : ∀ᵐ t ∂arrivalLaw G, ∀ e f : G.edgeSet, e ≠ f → t e ≠ t f :=
    ae_all_iff.mpr fun e => ae_all_iff.mpr fun f => by
      by_cases hef : e = f
      · simp [hef]
      · exact (hpair e f hef).mono fun t ht h => ht
  filter_upwards [hh] with t ht
  intro e f hef
  by_contra hne
  exact ht e f hne hef

lemma arrival_lt_one {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ᵐ t ∂arrivalLaw G, ∀ e, t e < 1 := by
  unfold arrivalLaw RandomOrderCRS.arrivalTimeLaw
  apply ae_all_iff.mpr
  intro e
  have hbase : ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), x < 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (show ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), x ≠ 1 from by simp only [ae_iff,not_not,Set.setOf_eq_eq_singleton,measure_singleton])] with x hx hne
    exact lt_of_le_of_ne hx.2 hne
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : G.edgeSet => volume.restrict (Set.Icc (0:ℝ) 1)) (i := e)).eventually hbase

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
open MeasureTheory Finset Classical ProbabilityTheory
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma tuple_sort_comp_perm {m : ℕ} (x : Fin m → ℝ) (hx : Function.Injective x)
    (π : Equiv.Perm (Fin m)) : Tuple.sort (x ∘ π) = (Tuple.sort x).trans π.symm := by
  apply Equiv.ext
  intro i
  apply π.injective
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
  apply hx
  exact congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f:=x) (σ:=π)) i

lemma sum_tuple_sort_comp {m : ℕ} (x : Fin m → ℝ) (hx : Function.Injective x)
    (F : Equiv.Perm (Fin m) → ℝ) :
    (∑ π : Equiv.Perm (Fin m), F (Tuple.sort (x ∘ π))) = ∑ π : Equiv.Perm (Fin m), F π := by
  simp_rw [tuple_sort_comp_perm x hx]
  have hh := ((Equiv.mulRight (Tuple.sort x)).bijective.comp (inv_bijective :
    Function.Bijective (Inv.inv : Equiv.Perm (Fin m) → Equiv.Perm (Fin m)))).sum_comp F
  exact hh

lemma iid_real_injective {ι : Type*} [Fintype ι] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∀ᵐ t ∂Measure.pi (fun _ : ι => μ), Function.Injective t := by
  have hd : (μ.prod μ) {z : ℝ × ℝ | z.1 = z.2} = 0 := by
    rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
    simp
  have hpair : ∀ e f : ι, e ≠ f → ∀ᵐ t ∂Measure.pi (fun _ : ι => μ), t e ≠ t f := by
    intro e f hef
    have hind := (iIndepFun_pi (μ:=fun _ : ι => μ) (X:=fun _ => id) (fun _ => aemeasurable_id)).indepFun hef
    have hm : (Measure.pi (fun _ : ι => μ)).map (fun t => (t e,t f)) = μ.prod μ := by
      have hh := (indepFun_iff_map_prod_eq_prod_map_map
        (measurable_pi_apply e).aemeasurable (measurable_pi_apply f).aemeasurable).mp hind
      rw [(measurePreserving_eval (fun _ : ι => μ) e).map_eq,
        (measurePreserving_eval (fun _ : ι => μ) f).map_eq] at hh
      exact hh
    apply ae_iff.mpr
    have hh : ((Measure.pi (fun _ : ι => μ)).map (fun t : ι → ℝ => (t e,t f))) {z : ℝ × ℝ | z.1 = z.2} =
        (Measure.pi (fun _ : ι => μ)) ((fun t : ι → ℝ => (t e,t f)) ⁻¹' {z : ℝ × ℝ | z.1 = z.2}) :=
      Measure.map_apply ((measurable_pi_apply e).prodMk (measurable_pi_apply f))
        (measurableSet_eq_fun measurable_fst measurable_snd)
    rw [hm,hd] at hh
    simpa using hh.symm
  have hall : ∀ᵐ t ∂Measure.pi (fun _ : ι => μ), ∀ e f : ι, e ≠ f → t e ≠ t f :=
    ae_all_iff.mpr fun e => ae_all_iff.mpr fun f => by
      by_cases hef : e = f
      · simp [hef]
      · exact (hpair e f hef).mono fun t ht h => ht
  filter_upwards [hall] with t ht
  intro e f hef
  by_contra hne
  exact ht e f hne hef

lemma iid_sort_uniform {m : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (F : Equiv.Perm (Fin m) → ℝ) :
    (∫ x : Fin m → ℝ, F (Tuple.sort x) ∂Measure.pi (fun _ : Fin m => μ)) =
      (∑ π : Equiv.Perm (Fin m), F π)/(Fintype.card (Equiv.Perm (Fin m)) : ℝ) := by
  letI : MeasurableSpace (Equiv.Perm (Fin m)) := ⊤
  letI : MeasurableSingletonClass (Equiv.Perm (Fin m)) := ⟨fun _ => trivial⟩
  have hs : Measurable (Tuple.sort : (Fin m → ℝ) → Equiv.Perm (Fin m)) := by
    apply measurable_to_countable'
    intro π
    exact sort_fiber_measurable π
  have hi := integrable_finite_comp (Measure.pi (fun _ : Fin m => μ)) Tuple.sort hs F
  have hperm (π : Equiv.Perm (Fin m)) :
      (∫ x : Fin m → ℝ, F (Tuple.sort (x ∘ π)) ∂Measure.pi (fun _ : Fin m => μ)) =
        ∫ x : Fin m → ℝ, F (Tuple.sort x) ∂Measure.pi (fun _ : Fin m => μ) := by
    have hp := measurePreserving_piCongrLeft (fun _ : Fin m => μ) π.symm
    convert! hp.integral_comp' (fun x => F (Tuple.sort x)) using 1
    congr 1
    funext x
    apply congrArg (fun y => F (Tuple.sort y))
    funext i
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have hiπ (π : Equiv.Perm (Fin m)) : Integrable (fun x : Fin m → ℝ => F (Tuple.sort (x ∘ π)))
      (Measure.pi (fun _ : Fin m => μ)) := by
    apply integrable_finite_comp _ (fun x => Tuple.sort (x ∘ π)) _ F
    apply hs.comp
    exact measurable_pi_iff.mpr (fun i => measurable_pi_apply (π i))
  have hsum := integral_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin m))) (fun π hπ => hiπ π)
  simp only [hperm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have heq : (∫ x : Fin m → ℝ, ∑ π : Equiv.Perm (Fin m), F (Tuple.sort (x ∘ π)) ∂Measure.pi (fun _ : Fin m => μ)) =
      ∑ π : Equiv.Perm (Fin m), F π := by
    calc
      _ = ∫ _ : Fin m → ℝ, ∑ π : Equiv.Perm (Fin m), F π ∂Measure.pi (fun _ : Fin m => μ) := by
        apply integral_congr_ae
        filter_upwards [iid_real_injective (ι:=Fin m) μ] with x hx
        exact sum_tuple_sort_comp x hx F
      _ = _ := by simp
  rw [heq] at hsum
  have hc : (Fintype.card (Equiv.Perm (Fin m)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (eq_div_iff hc).mpr
  simpa only [mul_comm] using hsum.symm

end
end FengLiYangMatching.General
open Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

def permLists {α : Type*} [DecidableEq α] (E : Finset α) : Finset (List α) := E.toList.permutations.toFinset

lemma mem_permLists {α : Type*} [DecidableEq α] (E : Finset α) (σ : List α) :
    σ ∈ permLists E ↔ σ.Nodup ∧ σ.toFinset = E := by
  simp only [permLists,List.mem_toFinset,List.mem_permutations]
  constructor
  · intro h
    exact ⟨h.nodup_iff.mpr (Finset.nodup_toList E),by simpa only [Finset.toList_toFinset] using List.toFinset_eq_of_perm _ _ h⟩
  · rintro ⟨hn,he⟩
    apply List.perm_of_nodup_nodup_toFinset_eq hn (Finset.nodup_toList E)
    simpa only [Finset.toList_toFinset] using he

lemma cons_mem_permLists {α : Type*} [DecidableEq α] (E : Finset α) (e : α) (σ : List α) :
    e::σ ∈ permLists E ↔ e ∈ E ∧ σ ∈ permLists (E.erase e) := by
  rw [mem_permLists,mem_permLists,List.nodup_cons,List.toFinset_cons]
  constructor
  · rintro ⟨⟨he,hn⟩,hs⟩
    have hf := congrArg (fun A : Finset α => A.erase e) hs
    have he' : e ∉ σ.toFinset := by simpa only [List.mem_toFinset] using he
    rw [Finset.erase_insert he'] at hf
    exact ⟨hs ▸ Finset.mem_insert_self _ _,hn,hf⟩
  · rintro ⟨he,hn,hs⟩
    have hnot : e ∉ σ := by
      intro hh
      have hh' : e ∈ σ.toFinset := List.mem_toFinset.mpr hh
      rw [hs] at hh'
      exact Finset.notMem_erase e E hh'
    exact ⟨⟨hnot,hn⟩,by rw [hs,Finset.insert_erase he]⟩

lemma permLists_first {α : Type*} [DecidableEq α] (E : Finset α) (hE : E.Nonempty) :
    permLists E = E.biUnion (fun e => (permLists (E.erase e)).image (List.cons e)) := by
  ext σ
  simp only [Finset.mem_biUnion,Finset.mem_image]
  constructor
  · intro hσ
    cases σ with
    | nil =>
      have hh := (mem_permLists E []).mp hσ
      have he : E = ∅ := by simpa using hh.2.symm
      exact (Finset.not_nonempty_empty (he ▸ hE)).elim
    | cons e σ =>
      obtain ⟨he,hs⟩ := (cons_mem_permLists E e σ).mp hσ
      exact ⟨e,he,σ,hs,rfl⟩
  · rintro ⟨e,he,σ,hs,rfl⟩
    exact (cons_mem_permLists E e σ).mpr ⟨he,hs⟩

lemma permLists_sum_first {α : Type*} [DecidableEq α] (E : Finset α) (hE : E.Nonempty)
    (f : List α → ℝ) :
    (∑ σ ∈ permLists E, f σ) = ∑ e ∈ E, ∑ σ ∈ permLists (E.erase e), f (e::σ) := by
  rw [permLists_first E hE,Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro e he
    exact Finset.sum_image (by intro σ hσ τ hτ hh; exact (List.cons.inj hh).2)
  · intro e he g hg hne
    change Disjoint ((permLists (E.erase e)).image (List.cons e)) ((permLists (E.erase g)).image (List.cons g))
    rw [Finset.disjoint_left]
    intro σ hσ hτ
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨t,ht,heq⟩ := Finset.mem_image.mp hτ
    exact hne (List.cons.inj heq).1.symm

lemma permLists_card {α : Type*} [DecidableEq α] (E : Finset α) :
    (permLists E).card = E.card.factorial := by
  unfold permLists
  rw [List.toFinset_card_of_nodup (List.nodup_permutations _ (Finset.nodup_toList E)),List.length_permutations,Finset.length_toList]

end
end FengLiYangMatching.General
open Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

def orderMean {α : Type*} [DecidableEq α] (E : Finset α) (f : List α → ℝ) : ℝ :=
  (∑ σ ∈ permLists E, f σ)/(permLists E).card

lemma orderMean_congr {α : Type*} [DecidableEq α] (E : Finset α) (f g : List α → ℝ)
    (h : ∀ σ ∈ permLists E, f σ = g σ) : orderMean E f = orderMean E g := by
  unfold orderMean
  congr 1
  exact Finset.sum_congr rfl h

lemma orderMean_const {α : Type*} [DecidableEq α] (E : Finset α) (C : ℝ) :
    orderMean E (fun _ => C) = C := by
  unfold orderMean
  rw [Finset.sum_const,nsmul_eq_mul]
  have hp : ((permLists E).card:ℝ) ≠ 0 := by
    rw [permLists_card]
    exact_mod_cast (Nat.factorial_ne_zero E.card)
  exact mul_div_cancel_left₀ C hp

lemma orderMean_empty {α : Type*} [DecidableEq α] (f : List α → ℝ) : orderMean ∅ f = f [] := by
  simp [orderMean,permLists]

lemma orderMean_first {α : Type*} [DecidableEq α] (E : Finset α) (hE : E.Nonempty)
    (f : List α → ℝ) :
    orderMean E f = (∑ e ∈ E, orderMean (E.erase e) (fun σ => f (e::σ)))/E.card := by
  have hpos : 0 < E.card := Finset.card_pos.mpr hE
  have hecard (e : α) (he : e ∈ E) : (E.erase e).card = E.card-1 := Finset.card_erase_of_mem he
  have hden : (E.card.factorial:ℝ) = (E.card:ℝ)*((E.card-1).factorial:ℝ) := by
    have hfac := Nat.factorial_succ (E.card-1)
    have hn : E.card-1+1 = E.card := by omega
    rw [hn] at hfac
    exact_mod_cast hfac
  unfold orderMean
  rw [permLists_sum_first E hE,permLists_card]
  have hinner : (∑ e ∈ E, (∑ σ ∈ permLists (E.erase e), f (e::σ))/((permLists (E.erase e)).card:ℝ)) =
      (∑ e ∈ E, ∑ σ ∈ permLists (E.erase e), f (e::σ))/((E.card-1).factorial:ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e he
    rw [permLists_card,hecard e he]
  rw [hinner,hden,div_div,mul_comm (E.card:ℝ)]

end
end FengLiYangMatching.General
open Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

def enumerationOrder {α : Type*} [DecidableEq α] (E : Finset α) {m : ℕ} (enum : Fin m ≃ E)
    (π : Equiv.Perm (Fin m)) : List α := List.ofFn (fun i => (enum (π i)).val)

lemma enumerationOrder_mem {α : Type*} [DecidableEq α] (E : Finset α) {m : ℕ} (enum : Fin m ≃ E)
    (π : Equiv.Perm (Fin m)) : enumerationOrder E enum π ∈ permLists E := by
  apply (mem_permLists E _).mpr
  refine ⟨List.nodup_ofFn.mpr (Subtype.val_injective.comp (enum.injective.comp π.injective)),?_⟩
  ext a
  constructor
  · intro ha
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp ha)
    rw [←hi]
    exact (enum (π i)).property
  · intro ha
    apply List.mem_toFinset.mpr
    exact List.mem_ofFn.mpr ⟨π.symm (enum.symm ⟨a,ha⟩),by simp⟩

lemma enumerationOrder_bijective {α : Type*} [DecidableEq α] (E : Finset α) {m : ℕ} (enum : Fin m ≃ E) :
    Function.Bijective (fun π : Equiv.Perm (Fin m) =>
      (⟨enumerationOrder E enum π,enumerationOrder_mem E enum π⟩ : permLists E)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro π ρ h
    have hlist := congrArg Subtype.val h
    have hfn := List.ofFn_injective hlist
    apply Equiv.ext
    intro i
    apply enum.injective
    apply Subtype.ext
    exact congrFun hfn i
  · have hm := Fintype.card_congr enum
    simp only [Fintype.card_fin,Fintype.card_coe] at hm
    simp only [Fintype.card_perm,Fintype.card_fin,Fintype.card_coe,permLists_card,hm]

lemma enumerationOrder_mean {α : Type*} [DecidableEq α] (E : Finset α) {m : ℕ} (enum : Fin m ≃ E)
    (f : List α → ℝ) :
    (∑ π : Equiv.Perm (Fin m), f (enumerationOrder E enum π))/(Fintype.card (Equiv.Perm (Fin m)):ℝ) =
      orderMean E f := by
  have hb := enumerationOrder_bijective E enum
  have hs := hb.sum_comp (fun σ : permLists E => f σ.val)
  have hcard := Fintype.card_of_bijective hb
  rw [Fintype.card_coe] at hcard
  unfold orderMean
  rw [hcard]
  congr 1
  exact hs.trans (Finset.sum_coe_sort (permLists E) f)

lemma orderMean_map {α β : Type*} [DecidableEq α] [DecidableEq β] (E : Finset α)
    (g : α ↪ β) (f : List β → ℝ) : orderMean E (fun σ => f (σ.map g)) = orderMean (E.map g) f := by
  let enum := (Fintype.equivFin E).symm
  let enum' := enum.trans (Finset.equivMap g E)
  rw [←enumerationOrder_mean E enum,←enumerationOrder_mean (E.map g) enum']
  congr 1
  apply Finset.sum_congr rfl
  intro π hπ
  apply congrArg f
  unfold enumerationOrder
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  rfl

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma iid_enumeration_order {α : Type*} [DecidableEq α] (E : Finset α) {m : ℕ} (enum : Fin m ≃ E)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] (f : List α → ℝ) :
    (∫ x : Fin m → ℝ, f (enumerationOrder E enum (Tuple.sort x)) ∂Measure.pi (fun _ : Fin m => μ)) =
      orderMean E f := by
  rw [iid_sort_uniform μ (fun π => f (enumerationOrder E enum π)),enumerationOrder_mean]

def orderFor {α : Type*} [DecidableEq α] (E : Finset α) (t : E → ℝ) : List α :=
  enumerationOrder E (Fintype.equivFin E).symm (Tuple.sort (t ∘ (Fintype.equivFin E).symm))

lemma iid_orderFor {α : Type*} [DecidableEq α] (E : Finset α) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (f : List α → ℝ) :
    (∫ t : E → ℝ, f (orderFor E t) ∂Measure.pi (fun _ : E => μ)) = orderMean E f := by
  let enum := (Fintype.equivFin E).symm
  have hp := measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card E) => μ) enum.symm
  have hi := hp.integral_comp' (fun x => f (enumerationOrder E enum (Tuple.sort x)))
  have hchange : (∫ t : E → ℝ, f (orderFor E t) ∂Measure.pi (fun _ : E => μ)) =
      ∫ x : Fin (Fintype.card E) → ℝ, f (enumerationOrder E enum (Tuple.sort x)) ∂Measure.pi (fun _ : Fin (Fintype.card E) => μ) := by
    convert! hi using 1
    congr 1
    funext t
    apply congrArg (fun x => f (enumerationOrder E enum (Tuple.sort x)))
    funext i
    simp [enum,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  exact hchange.trans (iid_enumeration_order E enum μ f)

lemma orderFor_mem {α : Type*} [DecidableEq α] (E : Finset α) (t : E → ℝ) :
    orderFor E t ∈ permLists E := enumerationOrder_mem E _ _

lemma orderFor_pairwise {α : Type*} [DecidableEq α] (E : Finset α) (T : α → ℝ) :
    (orderFor E (fun e => T e.val)).Pairwise (fun e f => T e ≤ T f) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact Tuple.monotone_sort (fun k => T (((Fintype.equivFin E).symm k).val)) hij.le

end
end FengLiYangMatching.General
open Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma orderMean_restrict {α : Type*} [DecidableEq α] (E F : Finset α) (hFE : F ⊆ E)
    (f : List α → ℝ) : orderMean E (fun σ => f (σ.filter (fun e => e ∈ F))) = orderMean F f := by
  induction E using Finset.strongInductionOn generalizing F f with | _ E ih =>
    by_cases hF : F = ∅
    · subst F
      simp only [Finset.notMem_empty,decide_false,List.filter_false]
      rw [orderMean_const,orderMean_empty]
    have hFn : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
    have hEn : E.Nonempty := hFn.mono hFE
    have hinner (e : α) (he : e ∈ E) :
        orderMean (E.erase e) (fun σ => f ((e::σ).filter (fun x => x ∈ F))) =
          if e ∈ F then orderMean (F.erase e) (fun σ => f (e::σ)) else orderMean F f := by
      by_cases heF : e ∈ F
      · rw [if_pos heF]
        have hsub : F.erase e ⊆ E.erase e := Finset.erase_subset_erase e hFE
        have hi := ih (E.erase e) (Finset.erase_ssubset he) (F.erase e) hsub (fun σ => f (e::σ))
        calc
          _ = orderMean (E.erase e) (fun σ => f (e::σ.filter (fun x => x ∈ F.erase e))) := by
            apply orderMean_congr
            intro σ hσ
            simp only [List.filter_cons,decide_eq_true_eq,heF,↓reduceIte]
            apply congrArg (fun τ => f (e::τ))
            apply List.filter_congr
            intro x hx
            have hxe : x ≠ e := by
              intro hxe
              have hxE : x ∈ E.erase e := by
                rw [←(mem_permLists (E.erase e) σ).mp hσ |>.2]
                exact List.mem_toFinset.mpr hx
              exact (Finset.mem_erase.mp hxE).1 hxe
            apply Bool.decide_congr
            exact ⟨fun hh => Finset.mem_erase.mpr ⟨hxe,hh⟩,fun hh => (Finset.mem_erase.mp hh).2⟩
          _ = _ := hi
      · rw [if_neg heF]
        have hsub : F ⊆ E.erase e := by
          intro x hx
          exact Finset.mem_erase.mpr ⟨fun hxe => heF (hxe ▸ hx),hFE hx⟩
        have hi := ih (E.erase e) (Finset.erase_ssubset he) F hsub f
        simpa only [List.filter_cons,decide_eq_true_eq,heF,↓reduceIte] using hi
    rw [orderMean_first E hEn]
    rw [show (∑ e ∈ E, orderMean (E.erase e) (fun σ => f ((e::σ).filter (fun x => x ∈ F)))) =
      (∑ e ∈ E, if e ∈ F then orderMean (F.erase e) (fun σ => f (e::σ)) else orderMean F f) from
      Finset.sum_congr rfl hinner]
    have hsplit : (∑ e ∈ E, if e ∈ F then orderMean (F.erase e) (fun σ => f (e::σ)) else orderMean F f) =
        (∑ e ∈ F, orderMean (F.erase e) (fun σ => f (e::σ)))+(E \ F).card*orderMean F f := by
      have hU : F ∪ (E \ F) = E := Finset.union_sdiff_of_subset hFE
      have hU_sum := Finset.sum_union (f:=fun e => if e ∈ F then orderMean (F.erase e) (fun σ => f (e::σ)) else orderMean F f) (show Disjoint F (E \ F) from by
        rw [Finset.disjoint_left]
        intro e he hf
        exact (Finset.mem_sdiff.mp hf).2 he)
      rw [hU] at hU_sum
      rw [hU_sum]
      have hleft : (∑ e ∈ F, if e ∈ F then orderMean (F.erase e) (fun σ => f (e::σ)) else orderMean F f) =
          ∑ e ∈ F, orderMean (F.erase e) (fun σ => f (e::σ)) :=
        Finset.sum_congr rfl (fun e he => if_pos he)
      have hright : (∑ e ∈ E \ F, if e ∈ F then orderMean (F.erase e) (fun σ => f (e::σ)) else orderMean F f) =
          (E \ F).card*orderMean F f := by
        simp only [Finset.sum_ite_of_false (fun e he => (Finset.mem_sdiff.mp he).2),Finset.sum_const,nsmul_eq_mul]
      rw [hleft,hright]
    rw [hsplit]
    have hFfirst := orderMean_first F hFn f
    have hFpos : (F.card:ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hFn
    have hEpos : (E.card:ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hEn
    have hsum : (∑ e ∈ F, orderMean (F.erase e) (fun σ => f (e::σ))) = orderMean F f*F.card :=
      (div_eq_iff hFpos).mp hFfirst.symm
    rw [hsum]
    have hc : ((E \ F).card:ℝ)+(F.card:ℝ) = E.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hFE
    apply (div_eq_iff hEpos).mpr
    rw [←hc]
    ring

lemma filter_filter_subset {α : Type*} [DecidableEq α] (E F : Finset α) (hFE : F ⊆ E) (σ : List α) :
    (σ.filter (fun e => e ∈ E)).filter (fun e => e ∈ F) = σ.filter (fun e => e ∈ F) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  by_cases heF : e ∈ F
  · simp [heF,hFE heF]
  · simp [heF]


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
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma greedy_snoc {n : ℕ} (l : List (Edge n)) (e : Edge n) :
    greedy (l ++ [e]) = if free (greedy l) e then insert e (greedy l) else greedy l := by
  classical
  unfold greedy
  rw [List.foldl_append]
  rfl

lemma greedy_fold_mono {n : ℕ} (l : List (Edge n)) (F : EdgeSet n) :
    F ⊆ l.foldl (fun F e => if free F e then insert e F else F) F := by
  classical
  induction l generalizing F with
  | nil => exact Subset.rfl
  | cons e l ih =>
    simp only [List.foldl_cons]
    exact (show F ⊆ (if free F e then insert e F else F) by split_ifs <;> simp).trans (ih _)

lemma greedy_prefix_mono {n : ℕ} {l k : List (Edge n)} (h : l.IsPrefix k) : greedy l ⊆ greedy k := by
  obtain ⟨r,rfl⟩ := h
  simpa only [greedy,List.foldl_append] using greedy_fold_mono r (greedy l)

lemma filter_lt_prefix {α : Type*} (l : List α) (f : α → ℝ)
    (hl : l.Pairwise (fun x y => f x ≤ f y)) (a b : ℝ) (hab : a ≤ b) :
    (l.filter fun e => f e < a).IsPrefix (l.filter fun e => f e < b) := by
  classical
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    by_cases hx : f x < a
    · have hxb : f x < b := lt_of_lt_of_le hx hab
      simp only [List.filter_cons, decide_eq_true_eq, hx, hxb, ↓reduceIte]
      obtain ⟨r,hr⟩ := ih hl.2
      exact ⟨r, by simpa only [List.cons_append] using congrArg (List.cons x) hr⟩
    · have hall : (x::l).filter (fun e => f e < a) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact not_lt.mpr (le_trans (not_lt.mp hx) (hl.1 y hy))
      rw [hall]
      exact List.nil_prefix

lemma ordered_monotone {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) :
    (orderedEdges G t).Pairwise (fun e f => t e ≤ t f) := by
  classical
  have hm : Monotone (fun i => t (RandomOrderCRS.arrivalOrder G t i)) :=
    Tuple.monotone_sort (t ∘ (Fintype.equivFin G.edgeSet).symm)
  have hh : ((orderedEdges G t).map t).Pairwise (· ≤ ·) := by
    simpa only [orderedEdges,List.map_ofFn,Function.comp_def] using hm.sortedLE_ofFn.pairwise
  exact List.pairwise_map.mp hh

lemma shadowAt_mono {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (a b : ℝ) (hab : a ≤ b) :
    shadowAt G t a ⊆ shadowAt G t b := by
  classical
  apply greedy_prefix_mono
  exact (filter_lt_prefix (orderedEdges G t) t (ordered_monotone G t) a b hab).map Subtype.val

lemma filter_lt_index {α : Type*} (l : List α) (f : α → ℝ)
    (hl : l.Pairwise (fun x y => f x < f y)) (i : ℕ) (hi : i < l.length) :
    (l.filter fun x => f x < f l[i]) = l.take i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero,List.take_zero]
      apply List.filter_eq_nil_iff.mpr
      intro y hy
      simp only [decide_eq_true_eq]
      rcases List.mem_cons.mp hy with rfl | hy
      · exact lt_irrefl _
      · exact not_lt.mpr (le_of_lt (hl.1 y hy))
    | succ i =>
      have hi' : i < l.length := by simpa using hi
      have hx : f x < f l[i] := hl.1 _ (List.getElem_mem hi')
      simp only [List.getElem_cons_succ,List.filter_cons,decide_eq_true_eq,hx,↓reduceIte,List.take_succ_cons]
      rw [ih hl.2 i hi']

lemma index_mem_take_iff {α : Type*} (l : List α) (hn : l.Nodup) (i : Fin l.length) (j : ℕ) :
    l[i.val] ∈ l.take j ↔ i.val < j := by
  constructor
  · intro hm
    obtain ⟨k,hk,hke⟩ := List.mem_iff_getElem.mp hm
    rw [List.getElem_take] at hke
    have hh := hn.getElem_inj_iff.mp hke
    have hkj : k < j := lt_of_lt_of_le hk (List.length_take_le j l)
    omega
  · intro hij
    have hh : i.val < (l.take j).length := by simp only [List.length_take]; omega
    have hm := List.getElem_mem hh
    simpa only [List.getElem_take] using hm

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma survival_antitone {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    Antitone (survival G A) := by
  haveI := arrival_probability G
  intro a b hab
  apply measureReal_mono (h₂ := by finiteness)
  intro t ht v hv hcovered
  exact ht v hv (covered_mono (shadowAt_mono G t a b hab) hcovered)

lemma measurable_survival {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    Measurable (survival G A) := (survival_antitone G A).measurable

lemma survival_bounds {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (t : ℝ) :
    0 ≤ survival G A t ∧ survival G A t ≤ 1 := by
  haveI := arrival_probability G
  exact ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩

lemma intervalIntegrable_survival {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a b : ℝ) :
    IntervalIntegrable (survival G A) volume a b :=
  (survival_antitone G A).intervalIntegrable

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma mem_orderedEdges {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (e : G.edgeSet) :
    e ∈ orderedEdges G t := by
  exact List.mem_ofFn.mpr ((RandomOrderCRS.arrivalOrder G t).surjective e)

lemma orderedEdges_nodup {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) :
    (orderedEdges G t).Nodup :=
  List.nodup_ofFn.mpr (RandomOrderCRS.arrivalOrder G t).injective

lemma prefix_mem {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ) (u : ℝ) (e : Edge n) :
    e ∈ (((orderedEdges G (fun f => T f.val)).filter (fun f => T f.val < u)).map Subtype.val) ↔
      e ∈ G.edgeSet ∧ T e < u := by
  constructor
  · rintro h
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp h
    exact ⟨f.property, (List.mem_filter.mp hf).2 |> of_decide_eq_true⟩
  · rintro ⟨he,ht⟩
    apply List.mem_map.mpr
    exact ⟨⟨e,he⟩, List.mem_filter.mpr ⟨mem_orderedEdges G _ _, by simpa using ht⟩, rfl⟩

lemma prefix_pairwise {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ) (u : ℝ) :
    (((orderedEdges G (fun f => T f.val)).filter (fun f => T f.val < u)).map Subtype.val).Pairwise
      (fun e f => T e ≤ T f) := by
  exact List.pairwise_map.mpr ((ordered_monotone G (fun f => T f.val)).filter _)

lemma shadowAt_eq_of_prefix {n : ℕ} (G H : SimpleGraph (Fin n)) (T : Edge n → ℝ) (u : ℝ)
    (hT : Set.InjOn T (G.edgeSet ∪ H.edgeSet))
    (hp : ∀ e, (e ∈ G.edgeSet ∧ T e < u) ↔ (e ∈ H.edgeSet ∧ T e < u)) :
    shadowAt G (fun e => T e.val) u = shadowAt H (fun e => T e.val) u := by
  unfold shadowAt
  congr 1
  let lG := (((orderedEdges G (fun f => T f.val)).filter (fun f => T f.val < u)).map Subtype.val)
  let lH := (((orderedEdges H (fun f => T f.val)).filter (fun f => T f.val < u)).map Subtype.val)
  have hnodupG : lG.Nodup := ((orderedEdges_nodup G _).filter _).map Subtype.val_injective
  have hnodupH : lH.Nodup := ((orderedEdges_nodup H _).filter _).map Subtype.val_injective
  have hperm : lG.Perm lH := (List.perm_ext_iff_of_nodup hnodupG hnodupH).mpr (by
    intro e
    rw [prefix_mem,prefix_mem]
    exact hp e)
  apply List.Perm.eq_of_pairwise (le := fun e f => T e ≤ T f) ?_
    (prefix_pairwise G T u) (prefix_pairwise H T u) hperm
  intro e f he hf hef hfe
  exact hT (Or.inl ((prefix_mem G T u e).mp he).1)
    (Or.inr ((prefix_mem H T u f).mp hf).1) (le_antisymm hef hfe)

lemma shadowAt_delete_prefix {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ) (e : Edge n)
    (hT : Set.InjOn T G.edgeSet) (u : ℝ) (hu : u ≤ T e) :
    shadowAt G (fun f => T f.val) u = shadowAt (G.deleteEdges {e}) (fun f => T f.val) u := by
  apply shadowAt_eq_of_prefix
  · apply hT.mono
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact Set.union_subset (Set.Subset.refl _) Set.sdiff_subset
  · intro f
    rw [SimpleGraph.edgeSet_deleteEdges]
    simp only [Set.mem_sdiff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨hf,ht⟩
      refine ⟨⟨hf,?_⟩,ht⟩
      intro hfe
      subst f
      linarith
    · tauto

lemma ordered_values_strict {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (hT : Set.InjOn T G.edgeSet) :
    ((orderedEdges G (fun e => T e.val)).map Subtype.val).Pairwise (fun e f => T e < T f) := by
  let l := (orderedEdges G (fun e => T e.val)).map Subtype.val
  have hn : l.Nodup := (orderedEdges_nodup G _).map Subtype.val_injective
  have hm : l.Pairwise (fun e f => T e ≤ T f) := List.pairwise_map.mpr (ordered_monotone G _)
  apply List.Pairwise.imp_of_mem ?_ (hm.and (List.nodup_iff_pairwise_ne.mp hn))
  intro e f he hf hh
  apply lt_of_le_of_ne hh.1
  intro heq
  obtain ⟨ee,hee,rfl⟩ := List.mem_map.mp he
  obtain ⟨ff,hff,rfl⟩ := List.mem_map.mp hf
  exact hh.2 (hT ee.property ff.property heq)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def vacant {n : ℕ} (A : Finset (Fin n)) (F : EdgeSet n) : Prop :=
  ∀ v ∈ A, v ∉ covered F

lemma vacant_insert_iff {n : ℕ} (A : Finset (Fin n)) (F : EdgeSet n) (e : Edge n) :
    vacant A (insert e F) ↔ vacant A F ∧ ¬ (∃ v ∈ A, v ∈ e) := by
  simp only [vacant,covered_insert,Finset.mem_union,Sym2.mem_toFinset]
  aesop

lemma vacant_drop {n : ℕ} (A : Finset (Fin n)) (F : EdgeSet n) (e : Edge n) :
    (if vacant A F then (1:ℝ) else 0) -
      (if vacant A (if free F e then insert e F else F) then (1:ℝ) else 0) =
    if vacant A F ∧ free F e ∧ (∃ v ∈ A, v ∈ e) then (1:ℝ) else 0 := by
  by_cases hf : free F e <;> by_cases hv : vacant A F <;> by_cases he : ∃ v ∈ A, v ∈ e <;>
    simp [hf,hv,he,vacant_insert_iff]

lemma vacant_telescope {n : ℕ} (A : Finset (Fin n)) (l : List (Edge n)) :
    (if vacant A (greedy []) then (1:ℝ) else 0) =
      (if vacant A (greedy l) then (1:ℝ) else 0) +
        ∑ i ∈ Finset.range l.length,
          ((if vacant A (greedy (l.take i)) then (1:ℝ) else 0) -
            (if vacant A (greedy (l.take (i+1))) then (1:ℝ) else 0)) := by
  rw [Finset.sum_range_sub']
  simp only [List.take_zero,List.take_length]
  ring
  rfl

lemma covered_singleton {n : ℕ} (e : Edge n) : covered {e} = e.toFinset := by
  ext v
  simp [covered]

lemma vacant_union_edge {n : ℕ} (A : Finset (Fin n)) (F : EdgeSet n) (e : Edge n) :
    vacant (A ∪ covered {e}) F ↔ vacant A F ∧ free F e := by
  simp only [vacant,free,covered_singleton,Finset.mem_union,Sym2.mem_toFinset]
  aesop

lemma vacant_index_drop {n : ℕ} (A : Finset (Fin n)) (l : List (Edge n)) (i : Fin l.length) :
    (if vacant A (greedy (l.take i.val)) then (1:ℝ) else 0) -
      (if vacant A (greedy (l.take (i.val+1))) then (1:ℝ) else 0) =
    if (∃ v ∈ A, v ∈ l[i.val]) ∧ vacant (A ∪ covered {l[i.val]}) (greedy (l.take i.val))
      then (1:ℝ) else 0 := by
  rw [List.take_succ_eq_append_getElem i.isLt,greedy_snoc,vacant_drop,vacant_union_edge]
  congr 1
  apply propext
  tauto

lemma vacant_first_hit {n : ℕ} (A : Finset (Fin n)) (l : List (Edge n)) (j : ℕ) (hj : j ≤ l.length) :
    (if vacant A (greedy (l.take j)) then (1:ℝ) else 0) =
      (if vacant A (greedy l) then (1:ℝ) else 0) + ∑ i : Fin l.length,
        if j ≤ i.val then
          (if (∃ v ∈ A, v ∈ l[i.val]) ∧ vacant (A ∪ covered {l[i.val]}) (greedy (l.take i.val))
            then (1:ℝ) else 0) else 0 := by
  let f : ℕ → ℝ := fun i => if vacant A (greedy (l.take (max i j))) then 1 else 0
  have ht := Finset.sum_range_sub' f l.length
  have hfin : (∑ i : Fin l.length, (f i.val - f (i.val+1))) =
      (∑ i ∈ Finset.range l.length, (f i - f (i+1))) := by
    exact Fin.sum_univ_eq_sum_range (fun z : ℕ => f z - f (z+1)) l.length
  have hterms : (∑ i : Fin l.length, (f i.val - f (i.val+1))) =
      ∑ i : Fin l.length,
        if j ≤ i.val then
          (if (∃ v ∈ A, v ∈ l[i.val]) ∧ vacant (A ∪ covered {l[i.val]}) (greedy (l.take i.val))
            then (1:ℝ) else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hji : j ≤ i.val
    · simp only [f,max_eq_left hji,max_eq_left (show j ≤ i.val+1 by omega),hji,↓reduceIte]
      exact vacant_index_drop A l i
    · simp only [f,max_eq_right (show i.val ≤ j by omega),max_eq_right (show i.val+1 ≤ j by omega),hji,↓reduceIte,sub_self]
  rw [hfin] at hterms
  rw [←hterms,ht]
  simp only [f,Nat.zero_max,max_eq_left hj,List.take_length]
  ring

lemma shadowAt_values {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ) (u : ℝ) :
    shadowAt G (fun e => T e.val) u =
      greedy (((orderedEdges G (fun e => T e.val)).map Subtype.val).filter fun e => T e < u) := by
  simp only [shadowAt,List.filter_map,Function.comp_def]

set_option maxHeartbeats 1200000 in
lemma first_hit_graph {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (hT : Set.InjOn T G.edgeSet) (h1 : ∀ e ∈ G.edgeSet, T e < 1)
    (A : Finset (Fin n)) (u : ℝ) (hu : u ≤ 1) :
    (if vacant A (shadowAt G (fun e => T e.val) u) then (1:ℝ) else 0) =
      (if vacant A (shadowAt G (fun e => T e.val) 1) then (1:ℝ) else 0) +
        ∑ e : G.edgeSet, if u ≤ T e.val ∧ (∃ v ∈ A, v ∈ e.val) ∧
          vacant (A ∪ covered {e.val}) (shadowAt (G.deleteEdges {e.val}) (fun f => T f.val) (T e.val))
          then (1:ℝ) else 0 := by
  let l := (orderedEdges G (fun e => T e.val)).map Subtype.val
  have hnd : l.Nodup := (orderedEdges_nodup G _).map Subtype.val_injective
  have hmono : l.Pairwise (fun e f => T e ≤ T f) := by
    exact List.pairwise_map.mpr (ordered_monotone G _)
  have hlt : l.Pairwise (fun e f => T e < T f) := by
    apply List.Pairwise.imp_of_mem ?_ (hmono.and (List.nodup_iff_pairwise_ne.mp hnd))
    intro e f he hf hh
    apply lt_of_le_of_ne hh.1
    intro heq
    obtain ⟨ee,hee,rfl⟩ := List.mem_map.mp he
    obtain ⟨ff,hff,rfl⟩ := List.mem_map.mp hf
    exact hh.2 (hT ee.property ff.property heq)
  have hall : l.filter (fun e => T e < 1) = l := by
    apply List.filter_eq_self.mpr
    intro e he
    obtain ⟨ee,hee,rfl⟩ := List.mem_map.mp he
    simpa only [decide_eq_true_eq] using h1 _ ee.property
  have hpref := filter_lt_prefix l T hmono u 1 hu
  rw [hall] at hpref
  let j := (l.filter (fun e => T e < u)).length
  have hj : j ≤ l.length := List.length_filter_le _ _
  have hp : l.filter (fun e => T e < u) = l.take j := by
    obtain ⟨r,hr⟩ := hpref
    calc
      l.filter (fun e => T e < u) = ((l.filter (fun e => T e < u)) ++ r).take j := by dsimp [j]; simp
      _ = l.take j := congrArg (List.take j) hr
  have hjiff (i : Fin l.length) : j ≤ i.val ↔ u ≤ T l[i.val] := by
    have hm : T l[i.val] < u ↔ l[i.val] ∈ l.take j := by
      rw [←hp]
      simp only [List.mem_filter,decide_eq_true_eq,List.getElem_mem,true_and]
    rw [index_mem_take_iff l hnd i j] at hm
    simpa only [not_lt] using (not_congr hm).symm
  have hindex (i : Fin l.length) :
      greedy (l.take i.val) = shadowAt G (fun e => T e.val) (T l[i.val]) := by
    rw [shadowAt_values,filter_lt_index l T hlt i.val i.isLt]
  have ht := vacant_first_hit A l j hj
  have hv1 : greedy l = shadowAt G (fun e => T e.val) 1 := by rw [shadowAt_values,hall]
  rw [←hp,←shadowAt_values,hv1] at ht
  have hsum : (∑ i : Fin l.length, if j ≤ i.val then
      (if (∃ v ∈ A, v ∈ l[i.val]) ∧ vacant (A ∪ covered {l[i.val]}) (greedy (l.take i.val))
        then (1:ℝ) else 0) else 0) =
      ∑ i : Fin l.length, if u ≤ T l[i.val] ∧ (∃ v ∈ A, v ∈ l[i.val]) ∧
        vacant (A ∪ covered {l[i.val]}) (shadowAt (G.deleteEdges {l[i.val]}) (fun f => T f.val) (T l[i.val]))
        then (1:ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [hjiff,hindex,shadowAt_delete_prefix G T l[i.val] hT _ (le_refl _)]
    by_cases hc : u ≤ T l[i.val] <;> simp only [hc,↓reduceIte,true_and,false_and] <;> rfl
  rw [hsum] at ht
  convert ht using 1
  symm
  congr 1
  let score : Edge n → ℝ := fun e => if u ≤ T e ∧ (∃ v ∈ A, v ∈ e) ∧
      vacant (A ∪ covered {e}) (shadowAt (G.deleteEdges {e}) (fun f => T f.val) (T e)) then 1 else 0
  change (∑ i : Fin l.length, score l[i.val]) = ∑ e : G.edgeSet, score e.val
  have hlen : l.length = Fintype.card G.edgeSet := by simp [l,orderedEdges]
  let q : Fin l.length ≃ G.edgeSet := (finCongr hlen).trans (RandomOrderCRS.arrivalOrder G (fun e => T e.val))
  have hq (i : Fin l.length) : l[i.val] = (q i).val := by
    simp [q,l,orderedEdges]
    rfl
  calc
    (∑ i : Fin l.length, score l[i.val]) = ∑ i : Fin l.length, score (q i).val := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hq]
    _ = _ := q.sum_comp (fun e : G.edgeSet => score e.val)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

private def remainingEdgeEquiv {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) :
    (G.deleteEdges {e.val}).edgeSet ≃ {f : G.edgeSet // f ≠ e} where
  toFun f := ⟨⟨f.val, by
    have h := f.property
    simp only [SimpleGraph.edgeSet_deleteEdges,Set.mem_sdiff,Set.mem_singleton_iff] at h
    exact h.1⟩, by
      intro hfe
      have hv := congrArg Subtype.val hfe
      have h := f.property
      simp only [SimpleGraph.edgeSet_deleteEdges,Set.mem_sdiff,Set.mem_singleton_iff] at h
      exact h.2 (by simpa using hv)⟩
  invFun f := ⟨f.val.val, by
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨f.val.property,?_⟩
    simpa only [Set.mem_singleton_iff] using (show f.val.val ≠ e.val from fun h => f.property (Subtype.ext h))⟩
  left_inv f := rfl
  right_inv f := rfl

def restrictTimes {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (t : Times G) :
    Times (G.deleteEdges {e.val}) := fun f => t ((remainingEdgeEquiv G e f).val)

lemma edge_product_preserving {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) :
    MeasurePreserving (fun t : Times G => (t e, restrictTimes G e t)) (arrivalLaw G)
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (arrivalLaw (G.deleteEdges {e.val}))) := by
  letI : Fintype {f : G.edgeSet // f = e} := Subtype.fintype _
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  haveI : IsProbabilityMeasure μ := ⟨by dsimp [μ]; simp⟩
  have hs := measurePreserving_piEquivPiSubtypeProd (fun _ : G.edgeSet => μ) (fun f => f = e)
  have hfirst := measurePreserving_eval (fun _ : {f : G.edgeSet // f = e} => μ) (⟨e,rfl⟩ : {f : G.edgeSet // f = e})
  have hrest := measurePreserving_piCongrLeft (fun _ : (G.deleteEdges {e.val}).edgeSet => μ) (remainingEdgeEquiv G e).symm
  convert! (hfirst.prod hrest).comp hs using 1
  all_goals first
    | (ext t; rfl)
    | (unfold arrivalLaw RandomOrderCRS.arrivalTimeLaw; congr 2; exact Subsingleton.elim _ _)

lemma vacancy_integral {n : ℕ} (J : SimpleGraph (Fin n)) (A : Finset (Fin n)) (s : ℝ) :
    (∫ t, (if vacant A (shadowAt J t s) then (1:ℝ) else 0) ∂arrivalLaw J) = survival J A s := by
  have hmap : Measurable (fun t : Times J => (t,s)) := measurable_id.prodMk measurable_const
  have hset0 := (measurable_survival_event J A).preimage hmap
  have hset : MeasurableSet {t : Times J | vacant A (shadowAt J t s)} := by
    simpa only [Set.preimage_setOf_eq,vacant] using hset0
  change _ = (arrivalLaw J).real {t : Times J | vacant A (shadowAt J t s)}
  simpa only [Set.indicator_apply,Pi.one_apply,Set.mem_ofPred_eq] using integral_indicator_one hset

set_option maxHeartbeats 200000 in

lemma edge_vacancy_integral {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet)
    (A : Finset (Fin n)) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫ t, (if u ≤ t e ∧ vacant (A ∪ covered {e.val})
      (shadowAt (G.deleteEdges {e.val}) (restrictTimes G e t) (t e)) then (1:ℝ) else 0) ∂arrivalLaw G) =
      ∫ s in u..(1:ℝ), survival (G.deleteEdges {e.val}) (A ∪ covered {e.val}) s := by
  let J := G.deleteEdges {e.val}
  let D := A ∪ covered {e.val}
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  haveI : IsProbabilityMeasure μ := ⟨by dsimp [μ]; simp⟩
  haveI := arrival_probability J
  let H : ℝ × Times J → ℝ := fun z => if u ≤ z.1 ∧ vacant D (shadowAt J z.2 z.1) then 1 else 0
  have hle : MeasurableSet {z : ℝ × Times J | u ≤ z.1} :=
    measurableSet_le (show Measurable (fun _ : ℝ × Times J => u) from measurable_const) measurable_fst
  have hswap : Measurable (fun z : ℝ × Times J => (z.2,z.1)) := measurable_swap
  have hevent0 := (measurable_survival_event J D).preimage hswap
  have hevent : MeasurableSet {z : ℝ × Times J | vacant D (shadowAt J z.2 z.1)} := by
    simpa only [Set.preimage_setOf_eq,vacant] using hevent0
  have hset : MeasurableSet {z : ℝ × Times J | u ≤ z.1 ∧ vacant D (shadowAt J z.2 z.1)} := hle.inter hevent
  have hm : Measurable H := measurable_const.ite hset measurable_const
  have hi : Integrable H (μ.prod (arrivalLaw J)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun z => by dsimp [H]; split_ifs <;> norm_num
  have hp := edge_product_preserving G e
  have hmap := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable H ((arrivalLaw G).map (fun t => (t e,restrictTimes G e t))) by
      rw [hp.map_eq]; exact hm.aestronglyMeasurable)
  rw [hp.map_eq] at hmap
  calc
    _ = ∫ z, H z ∂μ.prod (arrivalLaw J) := hmap.symm
    _ = ∫ s, ∫ r, H (s,r) ∂arrivalLaw J ∂μ := integral_prod H hi
    _ = ∫ s, (if u ≤ s then survival J D s else 0) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro s
      by_cases hs : u ≤ s
      · simp only [H,hs,true_and,↓reduceIte]
        exact vacancy_integral J D s
      · simp [H,hs]
    _ = _ := by
      change (∫ s, (Set.Ici u).indicator (survival J D) s ∂μ) = _
      rw [integral_indicator measurableSet_Ici]
      change (∫ s in Set.Ici u, survival J D s ∂volume.restrict (Set.Icc (0:ℝ) 1)) = _
      rw [Measure.restrict_restrict measurableSet_Ici]
      have he : Set.Ici u ∩ Set.Icc (0:ℝ) 1 = Set.Icc u 1 := by
        ext s
        simp only [Set.mem_inter_iff,Set.mem_Ici,Set.mem_Icc]
        constructor
        · intro h; exact ⟨h.1,h.2.2⟩
        · intro h; exact ⟨h.1,le_trans hu0 h.1,h.2⟩
      rw [he,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hu1]

lemma restrictTimes_from_global {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (T : Edge n → ℝ) :
    restrictTimes G e (fun f => T f.val) = (fun f => T f.val) := rfl

lemma integrable_vacancy {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : ℝ) :
    Integrable (fun t => if vacant A (shadowAt G t u) then (1:ℝ) else 0) (arrivalLaw G) := by
  haveI := arrival_probability G
  have hm : Measurable (fun t : Times G => (t,u)) := measurable_id.prodMk measurable_const
  have hs0 := (measurable_survival_event G A).preimage hm
  have hs : MeasurableSet {t : Times G | vacant A (shadowAt G t u)} := by
    simpa only [Set.preimage_setOf_eq,vacant] using hs0
  convert! (integrable_const (μ := arrivalLaw G) (1:ℝ)).indicator hs using 1 <;>
    (ext t; simp only [Set.indicator_apply,Set.mem_ofPred_eq])

lemma integrable_edge_vacancy {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet)
    (A : Finset (Fin n)) (u : ℝ) :
    Integrable (fun t => if u ≤ t e ∧ vacant (A ∪ covered {e.val})
      (shadowAt (G.deleteEdges {e.val}) (restrictTimes G e t) (t e)) then (1:ℝ) else 0) (arrivalLaw G) := by
  haveI := arrival_probability G
  have hp := (edge_product_preserving G e).measurable
  have hm : Measurable (fun t : Times G => (restrictTimes G e t,t e)) := hp.snd.prodMk hp.fst
  have hs0 := (measurable_survival_event (G.deleteEdges {e.val}) (A ∪ covered {e.val})).preimage hm
  have hv : MeasurableSet {t : Times G | vacant (A ∪ covered {e.val})
      (shadowAt (G.deleteEdges {e.val}) (restrictTimes G e t) (t e))} := by
    simpa only [Set.preimage_setOf_eq,vacant] using hs0
  have hl : MeasurableSet {t : Times G | u ≤ t e} :=
    measurableSet_le (show Measurable (fun _ : Times G => u) from measurable_const) hp.fst
  have hs : MeasurableSet {t : Times G | u ≤ t e ∧ vacant (A ∪ covered {e.val})
      (shadowAt (G.deleteEdges {e.val}) (restrictTimes G e t) (t e))} := hl.inter hv
  convert! (integrable_const (μ := arrivalLaw G) (1:ℝ)).indicator hs using 1 <;>
    (ext t; simp only [Set.indicator_apply,Set.mem_ofPred_eq])

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma not_free_insert_self {n : ℕ} (F : EdgeSet n) (e : Edge n) : ¬ free (insert e F) e := by
  intro hf
  have hv := Sym2.out_fst_mem e
  exact hf _ hv (by rw [covered_insert]; exact Finset.mem_union_right _ (Sym2.mem_toFinset.mpr hv))

lemma greedy_fold_blocks {n : ℕ} (l : List (Edge n)) (F : EdgeSet n) (e : Edge n) (he : e ∈ l) :
    ¬ free (l.foldl (fun F e => if free F e then insert e F else F) F) e := by
  induction l generalizing F with
  | nil => simp at he
  | cons f l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp he with rfl | he
    · intro hfree
      have hh := free_of_subset (greedy_fold_mono l (if free F e then insert e F else F)) hfree
      by_cases hf : free F e
      · exact not_free_insert_self F e (by simpa only [hf,↓reduceIte] using hh)
      · exact hf (by simpa only [hf,↓reduceIte] using hh)
    · exact ih _ he

lemma greedy_blocks_seen {n : ℕ} (l : List (Edge n)) (e : Edge n) (he : e ∈ l) :
    ¬ free (greedy l) e := greedy_fold_blocks l ∅ e he

lemma free_shadow_implies_time {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (u : ℝ)
    (e : G.edgeSet) (he : free (shadowAt G t u) e.val) : u ≤ t e := by
  by_contra h
  have ht : t e < u := lt_of_not_ge h
  have hmem : e.val ∈ ((orderedEdges G t).filter (fun f => t f < u)).map Subtype.val := by
    exact List.mem_map.mpr ⟨e,List.mem_filter.mpr ⟨mem_orderedEdges G t e,by simpa using ht⟩,rfl⟩
  exact greedy_blocks_seen _ _ hmem he

lemma free_shadow_delete_iff {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (hT : Set.InjOn T G.edgeSet) (u : ℝ) (e : G.edgeSet) :
    free (shadowAt G (fun f => T f.val) u) e.val ↔
      u ≤ T e.val ∧ free (shadowAt (G.deleteEdges {e.val}) (fun f => T f.val) u) e.val := by
  constructor
  · intro hf
    have ht := free_shadow_implies_time G (fun f => T f.val) u e hf
    refine ⟨ht,?_⟩
    rwa [←shadowAt_delete_prefix G T e.val hT u ht]
  · rintro ⟨ht,hf⟩
    rwa [shadowAt_delete_prefix G T e.val hT u ht]

lemma vacant_endpoints_iff {n : ℕ} (F : EdgeSet n) (e : Edge n) :
    vacant (covered {e}) F ↔ free F e := by
  simp only [vacant,free,covered_singleton,Sym2.mem_toFinset]

lemma greedy_fold_seen {n : ℕ} (l : List (Edge n)) (F : EdgeSet n) :
    l.foldl (fun F e => if free F e then insert e F else F) F ⊆ F ∪ l.toFinset := by
  induction l generalizing F with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldl_cons]
    apply (ih (if free F e then insert e F else F)).trans
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · by_cases he : free F e
      · simp only [he,↓reduceIte,Finset.mem_insert] at hg
        rcases hg with rfl | hg
        · simp
        · simp [hg]
      · simp only [he,↓reduceIte] at hg
        simp [hg]
    · simp only [List.toFinset_cons,Finset.mem_union,Finset.mem_insert]
      exact Or.inr (Or.inr hg)

lemma greedy_seen {n : ℕ} (l : List (Edge n)) : greedy l ⊆ l.toFinset := by
  simpa only [greedy,Finset.empty_union] using greedy_fold_seen l ∅

lemma greedy_mem_split {n : ℕ} (before after : List (Edge n)) (e : Edge n)
    (hpre : e ∉ before) (hpost : e ∉ after) :
    e ∈ greedy (before ++ e::after) ↔ free (greedy before) e := by
  have heq : greedy (before ++ e::after) =
      after.foldl (fun F f => if free F f then insert f F else F)
        (if free (greedy before) e then insert e (greedy before) else greedy before) := by
    unfold greedy
    rw [List.foldl_append]
    rfl
  rw [heq]
  by_cases hf : free (greedy before) e
  · simp only [hf,↓reduceIte,iff_true]
    exact greedy_fold_mono after (insert e (greedy before)) (Finset.mem_insert_self _ _)
  · simp only [hf,↓reduceIte,iff_false]
    intro hm
    rcases Finset.mem_union.mp (greedy_fold_seen after (greedy before) hm) with hm | hm
    · exact hpre (List.mem_toFinset.mp (greedy_seen before hm))
    · exact hpost (List.mem_toFinset.mp hm)

lemma greedy_mem_index {n : ℕ} (l : List (Edge n)) (hn : l.Nodup) (i : Fin l.length) :
    l[i.val] ∈ greedy l ↔ free (greedy (l.take i.val)) l[i.val] := by
  have hs : l.take i.val ++ l[i.val] :: l.drop (i.val+1) = l := by
    rw [←List.singleton_append,←List.append_assoc,←List.take_succ_eq_append_getElem i.isLt,List.take_append_drop]
  have hn' : (l.take i.val ++ l[i.val] :: l.drop (i.val+1)).Nodup := by rw [hs]; exact hn
  have hpre : l[i.val] ∉ l.take i.val := by
    intro hm
    exact (List.nodup_append.mp hn').2.2 _ hm _ (List.mem_cons_self) rfl
  have hpost : l[i.val] ∉ l.drop (i.val+1) := (List.nodup_cons.mp (List.nodup_append.mp hn').2.1).1
  have hh := greedy_mem_split (l.take i.val) (l.drop (i.val+1)) l[i.val] hpre hpost
  rwa [hs] at hh

set_option maxHeartbeats 500000 in
lemma shadow_member_iff {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (hT : Set.InjOn T G.edgeSet) (u : ℝ) (e : G.edgeSet) :
    e.val ∈ shadowAt G (fun f => T f.val) u ↔
      T e.val < u ∧ free (shadowAt (G.deleteEdges {e.val}) (fun f => T f.val) (T e.val)) e.val := by
  let full := (orderedEdges G (fun f => T f.val)).map Subtype.val
  let l := full.filter (fun f => T f < u)
  have hshadow : shadowAt G (fun f => T f.val) u = greedy l := shadowAt_values G T u
  have hnd : l.Nodup := ((orderedEdges_nodup G _).map Subtype.val_injective).filter _
  have hstrict : l.Pairwise (fun f g => T f < T g) := (ordered_values_strict G T hT).filter _
  by_cases ht : T e.val < u
  · have heMem : e.val ∈ l := by
      apply List.mem_filter.mpr
      refine ⟨?_, by simpa using ht⟩
      exact List.mem_map.mpr ⟨e,mem_orderedEdges G _ e,rfl⟩
    obtain ⟨i,hi,hie⟩ := List.mem_iff_getElem.mp heMem
    have hprefix : greedy (l.take i) = shadowAt G (fun f => T f.val) (T e.val) := by
      have htime : T l[i] = T e.val := congrArg T hie
      rw [shadowAt_values,←filter_lt_index l T hstrict i hi,htime]
      have hfilter : l.filter (fun f => T f < T e.val) = full.filter (fun f => T f < T e.val) := by
        dsimp [l]
        rw [List.filter_filter]
        congr 1
        funext f
        by_cases hf : T f < T e.val
        · have hfu : T f < u := lt_trans hf ht
          simp [hf,hfu]
        · simp [hf]
      rw [hfilter]
    rw [hshadow]
    have hh := greedy_mem_index l hnd ⟨i,hi⟩
    simp only [hie,hprefix] at hh
    rw [shadowAt_delete_prefix G T e.val hT (T e.val) (le_refl _)] at hh
    simpa only [ht,true_and] using hh
  · rw [hshadow]
    simp only [ht,false_and,iff_false]
    intro hm
    have heInput := List.mem_toFinset.mp (greedy_seen l hm)
    exact ht (of_decide_eq_true (List.mem_filter.mp heInput).2)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma filter_lt_initial_prefix {α : Type*} (l : List α) (T : α → ℝ)
    (hl : l.Pairwise (fun x y => T x ≤ T y)) (a : ℝ) :
    (l.filter fun e => T e < a).IsPrefix l := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    by_cases hx : T x < a
    · simp only [List.filter_cons,decide_eq_true_eq,hx,↓reduceIte]
      obtain ⟨r,hr⟩ := ih hl.2
      exact ⟨r,by simpa only [List.cons_append] using congrArg (List.cons x) hr⟩
    · have hn : (x::l).filter (fun e => T e < a) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact not_lt.mpr (le_trans (not_lt.mp hx) (hl.1 y hy))
      rw [hn]
      exact List.nil_prefix

lemma greedy_filter_time {n : ℕ} (l : List (Edge n)) (T : Edge n → ℝ)
    (hl : l.Pairwise (fun x y => T x ≤ T y)) (a : ℝ) :
    greedy (l.filter fun e => T e < a) = (greedy l).filter (fun e => T e < a) := by
  let before := l.filter (fun e => T e < a)
  obtain ⟨after,hs⟩ := filter_lt_initial_prefix l T hl a
  have hb : before.filter (fun e => T e < a) = before := by dsimp [before]; simp
  have hfilter := congrArg (List.filter (fun e => T e < a)) hs
  change (before ++ after).filter (fun e => T e < a) = before at hfilter
  rw [List.filter_append,hb] at hfilter
  have hn : after.filter (fun e => T e < a) = [] := List.append_cancel_left (as := before) (by simpa only [List.append_nil] using hfilter)
  have ha : ∀ e ∈ after, ¬ T e < a := by
    intro e he
    simpa only [decide_eq_true_eq] using List.filter_eq_nil_iff.mp hn e he
  have hprefix : before.IsPrefix l := ⟨after,hs⟩
  have hfold : greedy l = after.foldl (fun F e => if free F e then insert e F else F) (greedy before) := by
    calc
      greedy l = greedy (before ++ after) := congrArg greedy hs.symm
      _ = _ := by unfold greedy; rw [List.foldl_append]
  ext e
  rw [Finset.mem_filter]
  constructor
  · intro he
    refine ⟨greedy_prefix_mono hprefix he,?_⟩
    have hm := List.mem_toFinset.mp (greedy_seen before he)
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  · rintro ⟨he,ht⟩
    rw [hfold] at he
    rcases Finset.mem_union.mp (greedy_fold_seen after (greedy before) he) with he | he
    · exact he
    · exact False.elim (ha e (List.mem_toFinset.mp he) ht)

lemma shadowAt_filter_time {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    shadowAt G (fun e => T e.val) a =
      (shadowAt G (fun e => T e.val) b).filter (fun e => T e < a) := by
  let full := (orderedEdges G (fun e => T e.val)).map Subtype.val
  have hm : full.Pairwise (fun e f => T e ≤ T f) := List.pairwise_map.mpr (ordered_monotone G _)
  have hh := greedy_filter_time (full.filter (fun e => T e < b)) T (hm.filter _) a
  have hf : (full.filter (fun e => T e < b)).filter (fun e => T e < a) = full.filter (fun e => T e < a) := by
    rw [List.filter_filter]
    congr 1
    funext e
    by_cases he : T e < a
    · have hb : T e < b := lt_of_lt_of_le he hab
      simp [he,hb]
    · simp [he]
  rw [hf] at hh
  simpa only [shadowAt_values] using hh

lemma shadowAt_subset_graph {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (u : ℝ) :
    shadowAt G t u ⊆ graphEdges G := by
  intro e he
  have hm := List.mem_toFinset.mp (greedy_seen _ he)
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hm
  simpa [graphEdges] using f.property

lemma early_history_eq {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (a b : ℝ) (hab : a ≤ b) :
    early a (history G b t) = shadowAt G t a := by
  let T : Edge n → ℝ := fun e => if h : e ∈ G.edgeSet then t ⟨e,h⟩ else 0
  have hcoords (e : G.edgeSet) : T e.val = t e := by simp [T,e.property]
  have hTG : (fun e : G.edgeSet => T e.val) = t := funext hcoords
  have htime (e : Edge n) (he : e ∈ shadowAt G t b) : (history G b t).time e = T e := by
    have heG : e ∈ G.edgeSet := by simpa [graphEdges] using shadowAt_subset_graph G t b he
    simp [history,History.time,heG,he,T]
  have hearly : early a (history G b t) = (shadowAt G t b).filter (fun e => T e < a) := by
    change ((shadowAt G t b).filter (fun e => (history G b t).time e < a)) = _
    apply Finset.filter_congr
    intro e he
    rw [htime e he]
  rw [hearly]
  have hh := shadowAt_filter_time G T a b hab
  rw [hTG] at hh
  exact hh.symm

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma step_shadow_rule {n : ℕ} (a b : ℝ) (hab : a ≤ b) (S : State n)
    (e : Edge n) (t : ℝ) (c : Bool) :
    (step a b S e t c).shadow = if t < b then (if free S.shadow e then insert e S.shadow else S.shadow) else S.shadow := by
  unfold step
  split_ifs <;> first | rfl | linarith

lemma step_actual_filter {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (S : State n) (e : Edge n)
    (hS : S.actual.filter (fun f => T f < b) =
      S.shadow.filter (fun f => T f < b ∧ ¬ (T f < a ∧ C f = true))) :
    (step a b S e (T e) (C e)).actual.filter (fun f => T f < b) =
      (step a b S e (T e) (C e)).shadow.filter (fun f => T f < b ∧ ¬ (T f < a ∧ C f = true)) := by
  have ht : T e < a → T e < b := fun h => lt_of_lt_of_le h hab
  unfold step
  split_ifs <;> simp_all [Finset.filter_insert] <;> linarith

lemma step_reserved_filter {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (S : State n) (e : Edge n)
    (hS : S.reserved = covered (S.shadow.filter (fun f => T f < a ∧ C f = true))) :
    (step a b S e (T e) (C e)).reserved =
      covered ((step a b S e (T e) (C e)).shadow.filter (fun f => T f < a ∧ C f = true)) := by
  by_cases hta : T e < a
  · by_cases hf : free S.shadow e <;> by_cases hc : C e = true
    all_goals simp [step,hta,hf,hc,Finset.filter_insert,covered_insert,covered_singleton,hS]
  · by_cases htb : T e < b
    · have hk : ¬ (T e < a ∧ C e = true) := fun h => hta h.1
      by_cases hf : free S.shadow e
      · simp only [step,hta,htb,hf,↓reduceIte,Finset.filter_insert,hk]
        exact hS
      · simpa only [step,hta,htb,hf,↓reduceIte] using hS
    · unfold step
      simp only [hta,htb,↓reduceIte]
      split_ifs <;> exact hS

lemma fold_shadow_rule {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (S : State n) :
    (l.foldl (fun S e => step a b S e (T e) (C e)) S).shadow =
      (l.filter (fun e => T e < b)).foldl (fun F e => if free F e then insert e F else F) S.shadow := by
  induction l generalizing S with
  | nil => rfl
  | cons e l ih =>
    simp only [List.foldl_cons]
    rw [ih,step_shadow_rule a b hab]
    by_cases ht : T e < b <;> simp [ht]

lemma fold_actual_filter {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (S : State n)
    (hS : S.actual.filter (fun f => T f < b) =
      S.shadow.filter (fun f => T f < b ∧ ¬ (T f < a ∧ C f = true))) :
    (l.foldl (fun S e => step a b S e (T e) (C e)) S).actual.filter (fun f => T f < b) =
      (l.foldl (fun S e => step a b S e (T e) (C e)) S).shadow.filter
        (fun f => T f < b ∧ ¬ (T f < a ∧ C f = true)) := by
  induction l generalizing S with
  | nil => exact hS
  | cons e l ih =>
    simp only [List.foldl_cons]
    exact ih _ (step_actual_filter a b hab T C S e hS)

lemma fold_reserved_filter {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (S : State n)
    (hS : S.reserved = covered (S.shadow.filter (fun f => T f < a ∧ C f = true))) :
    (l.foldl (fun S e => step a b S e (T e) (C e)) S).reserved =
      covered ((l.foldl (fun S e => step a b S e (T e) (C e)) S).shadow.filter (fun f => T f < a ∧ C f = true)) := by
  induction l generalizing S with
  | nil => exact hS
  | cons e l ih =>
    simp only [List.foldl_cons]
    exact ih _ (step_reserved_filter a b hab T C S e hS)

def runEdges {n : ℕ} (a b : ℝ) (T : Edge n → ℝ) (C : Edge n → Bool) (l : List (Edge n)) : State n :=
  l.foldl (fun S e => step a b S e (T e) (C e)) (initial n)

lemma runEdges_shadow {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) : (runEdges a b T C l).shadow = greedy (l.filter fun e => T e < b) := by
  exact fold_shadow_rule a b hab T C l (initial n)

lemma runEdges_before {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) :
    (runEdges a b T C l).actual.filter (fun f => T f < b) =
      (runEdges a b T C l).shadow.filter (fun f => T f < b ∧ ¬ (T f < a ∧ C f = true)) := by
  apply fold_actual_filter a b hab T C l (initial n)
  simp [initial]

lemma runEdges_reserved {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) :
    (runEdges a b T C l).reserved = covered ((runEdges a b T C l).shadow.filter (fun f => T f < a ∧ C f = true)) := by
  apply fold_reserved_filter a b hab T C l (initial n)
  simp [initial,covered]

lemma runEdges_seen {n : ℕ} (a b : ℝ) (T : Edge n → ℝ) (C : Edge n → Bool) (l : List (Edge n)) :
    (runEdges a b T C l).actual ⊆ l.toFinset := by
  simpa [runEdges,run,List.foldl_map,Function.comp_def] using run_seen a b (l.map (fun e => (e,T e,C e)))

lemma execution_runEdges {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G)
    (T : Edge n → ℝ) (C : Edge n → Bool) (hT : ∀ e : G.edgeSet, T e.val = w.1 e)
    (hC : ∀ e : G.edgeSet, C e.val = w.2 e) :
    execution G a b w = runEdges a b T C ((orderedEdges G w.1).map Subtype.val) := by
  simp only [execution,run,stream,runEdges,List.foldl_map,hT,hC]

lemma step_late_rule {n : ℕ} (a b : ℝ) (hab : a ≤ b) (S : State n) (e : Edge n) (t : ℝ) (c : Bool)
    (ht : b ≤ t) :
    (step a b S e t c).reserved = S.reserved ∧
    (step a b S e t c).actual = if free S.actual e ∧ ¬ (∀ v, v ∈ e → v ∈ S.reserved)
      then insert e S.actual else S.actual := by
  have hta : ¬t < a := not_lt.mpr (le_trans hab ht)
  have htb : ¬t < b := not_lt.mpr ht
  unfold step
  simp only [hta,htb,↓reduceIte]
  split_ifs <;> simp

lemma fold_late_property {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (hl : ∀ e ∈ l, b ≤ T e) (R : Finset (Fin n)) (S : State n)
    (hSR : S.reserved = R) (hS : ∀ e ∈ S.actual, b ≤ T e → ¬(∀ v, v ∈ e → v ∈ R)) :
    (l.foldl (fun S e => step a b S e (T e) (C e)) S).reserved = R ∧
      ∀ e ∈ (l.foldl (fun S e => step a b S e (T e) (C e)) S).actual,
        b ≤ T e → ¬(∀ v, v ∈ e → v ∈ R) := by
  induction l generalizing S with
  | nil => exact ⟨hSR,hS⟩
  | cons e l ih =>
    simp only [List.foldl_cons]
    have hrule := step_late_rule a b hab S e (T e) (C e) (hl e (by simp))
    apply ih (fun f hf => hl f (List.mem_cons_of_mem _ hf)) _ (hrule.1.trans hSR)
    intro f hf htf
    rw [hrule.2] at hf
    split_ifs at hf with hacc
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · simpa only [hSR] using hacc.2
      · exact hS f hf htf
    · exact hS f hf htf

lemma threshold_split {α : Type*} (l : List α) (T : α → ℝ)
    (hl : l.Pairwise (fun x y => T x ≤ T y)) (b : ℝ) :
    ∃ r, (l.filter (fun e => T e < b)) ++ r = l ∧ ∀ e ∈ r, b ≤ T e := by
  obtain ⟨r,hr⟩ := filter_lt_initial_prefix l T hl b
  refine ⟨r,hr,?_⟩
  have hf := congrArg (List.filter (fun e => T e < b)) hr
  rw [List.filter_append,List.filter_filter] at hf
  simp only [Bool.and_self] at hf
  have hn : r.filter (fun e => T e < b) = [] := List.append_cancel_left
    (as := l.filter (fun e => T e < b)) (by simpa only [List.append_nil] using hf)
  intro e he
  exact not_lt.mp (by simpa only [decide_eq_true_eq] using List.filter_eq_nil_iff.mp hn e he)

lemma runEdges_late_property {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (hl : l.Pairwise (fun e f => T e ≤ T f)) :
    ∀ e ∈ (runEdges a b T C l).actual, b ≤ T e →
      ¬(∀ v, v ∈ e → v ∈ (runEdges a b T C l).reserved) := by
  obtain ⟨r,hs,hr⟩ := threshold_split l T hl b
  let before := l.filter (fun e => T e < b)
  let S := runEdges a b T C before
  have hstart : ∀ e ∈ S.actual, b ≤ T e → ¬(∀ v, v ∈ e → v ∈ S.reserved) := by
    intro e he ht
    have hm := List.mem_toFinset.mp (runEdges_seen a b T C before he)
    have hlt : T e < b := of_decide_eq_true (List.mem_filter.mp hm).2
    linarith
  have hh := fold_late_property a b hab T C r hr S.reserved S rfl hstart
  have heq : runEdges a b T C l = r.foldl (fun S e => step a b S e (T e) (C e)) S := by
    calc
      runEdges a b T C l = runEdges a b T C (before ++ r) := congrArg (runEdges a b T C) hs.symm
      _ = _ := by simp only [runEdges,List.foldl_append]; rfl
  rw [heq]
  rw [hh.1]
  exact hh.2

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma runEdges_matching {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (hl : l.Pairwise (fun e f => T e ≤ T f))
    (hloop : ∀ e ∈ l, ¬ e.IsDiag) : IsMatching (runEdges a b T C l).actual := by
  have hm : ((l.map (fun e => (e,T e,C e))).map (fun o => o.2.1)).Pairwise (· ≤ ·) := by
    simpa only [List.map_map,Function.comp_def,List.pairwise_map] using hl
  have he : ∀ o ∈ l.map (fun e => (e,T e,C e)), ¬ o.1.IsDiag := by
    intro o ho
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ho
    exact hloop e he
  simpa only [runEdges,run,List.foldl_map] using run_matching a b hab (l.map (fun e => (e,T e,C e))) hm he

lemma covered_union {n : ℕ} (A B : EdgeSet n) : covered (A ∪ B) = covered A ∪ covered B := by
  ext v
  simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  aesop

lemma runEdges_early_partition {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) :
    ((runEdges a b T C l).shadow.filter (fun e => T e < a ∧ C e = true)) ∪
      ((runEdges a b T C l).actual.filter (fun e => T e < b)) = (runEdges a b T C l).shadow := by
  have ht : ∀ e ∈ (runEdges a b T C l).shadow, T e < b := by
    intro e he
    rw [runEdges_shadow a b hab] at he
    have hm := List.mem_toFinset.mp (greedy_seen _ he)
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  have hf : (runEdges a b T C l).actual.filter (fun e => T e < b) =
      (runEdges a b T C l).shadow.filter (fun e => ¬ (T e < a ∧ C e = true)) := by
    rw [runEdges_before a b hab]
    apply Finset.filter_congr
    intro e he
    simp only [ht e he,true_and]
  rw [hf]
  exact Finset.filter_union_filter_not_eq _ _

lemma runEdges_cover_partition {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) :
    covered (runEdges a b T C l).shadow =
      covered ((runEdges a b T C l).actual.filter (fun e => T e < b)) ∪ (runEdges a b T C l).reserved := by
  have hh := congrArg covered (runEdges_early_partition a b hab T C l)
  rw [covered_union,←runEdges_reserved a b hab] at hh
  exact hh.symm.trans (Finset.union_comm _ _)

lemma runEdges_recovery_endpoints {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (hl : l.Pairwise (fun e f => T e ≤ T f)) (hloop : ∀ e ∈ l, ¬ e.IsDiag)
    (e : Edge n) (he : e ∈ (runEdges a b T C l).actual) (hte : b ≤ T e) :
    ∀ v, v ∈ e → v ∈ (runEdges a b T C l).reserved ∨ v ∉ covered (runEdges a b T C l).shadow := by
  have hM := runEdges_matching a b hab T C l hl hloop
  intro v hve
  have hnot : v ∉ covered ((runEdges a b T C l).actual.filter (fun e => T e < b)) := by
    intro hv
    obtain ⟨f,hf,hvf⟩ := (show ∃ f ∈ ((runEdges a b T C l).actual.filter (fun e => T e < b)), v ∈ f from by simpa [covered] using hv)
    obtain ⟨hf,htf⟩ := Finset.mem_filter.mp hf
    have hne : e ≠ f := by intro h; subst f; linarith
    exact hM.2 e he f hf hne v hve hvf
  by_cases hv : v ∈ covered (runEdges a b T C l).shadow
  · rw [runEdges_cover_partition a b hab] at hv
    exact Or.inl ((Finset.mem_union.mp hv).resolve_left hnot)
  · exact Or.inr hv

lemma runEdges_recovery_types {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (hl : l.Pairwise (fun e f => T e ≤ T f)) (hloop : ∀ e ∈ l, ¬ e.IsDiag)
    (e : Edge n) (he : e ∈ (runEdges a b T C l).actual) (hte : b ≤ T e) :
    (∃ x y, e = s(x,y) ∧ x ∈ (runEdges a b T C l).reserved ∧ y ∉ covered (runEdges a b T C l).shadow) ∨
      (∀ v, v ∈ e → v ∉ covered (runEdges a b T C l).shadow) := by
  have hend := runEdges_recovery_endpoints a b hab T C l hl hloop e he hte
  have hban := runEdges_late_property a b hab T C l hl e he hte
  induction e using Sym2.inductionOn with | hf x y =>
    rcases hend x (by simp) with hx | hx <;> rcases hend y (by simp) with hy | hy
    · exact False.elim (hban (by intro v hv; rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption))
    · exact Or.inl ⟨x,y,rfl,hx,hy⟩
    · exact Or.inl ⟨y,x,Sym2.eq_swap,hy,hx⟩
    · exact Or.inr (by intro v hv; rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption)

lemma runEdges_reserved_subset {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) : (runEdges a b T C l).reserved ⊆ covered (runEdges a b T C l).shadow := by
  rw [runEdges_reserved a b hab]
  exact covered_mono (Finset.filter_subset _ _)

lemma runEdges_recovery_card {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (hl : l.Pairwise (fun e f => T e ≤ T f)) (hloop : ∀ e ∈ l, ¬ e.IsDiag) :
    (((runEdges a b T C l).actual.filter (fun e => b ≤ T e)).filter (fun e => ∃ x y,
      e = s(x,y) ∧ x ∈ (runEdges a b T C l).reserved ∧ y ∉ covered (runEdges a b T C l).shadow)).card +
    (((runEdges a b T C l).actual.filter (fun e => b ≤ T e)).filter
      (fun e => ∀ v, v ∈ e → v ∉ covered (runEdges a b T C l).shadow)).card =
      ((runEdges a b T C l).actual.filter (fun e => b ≤ T e)).card := by
  let late := (runEdges a b T C l).actual.filter (fun e => b ≤ T e)
  let XY := late.filter (fun e => ∃ x y, e = s(x,y) ∧ x ∈ (runEdges a b T C l).reserved ∧ y ∉ covered (runEdges a b T C l).shadow)
  let YY := late.filter (fun e => ∀ v, v ∈ e → v ∉ covered (runEdges a b T C l).shadow)
  have hunion : XY ∪ YY = late := by
    ext e
    simp only [XY,YY,Finset.mem_union,Finset.mem_filter]
    constructor
    · tauto
    · intro he
      have hm := Finset.mem_filter.mp he
      have hh := runEdges_recovery_types a b hab T C l hl hloop e hm.1 hm.2
      rcases hh with h | h
      · exact Or.inl ⟨he,h⟩
      · exact Or.inr ⟨he,h⟩
  have hd : Disjoint XY YY := by
    rw [Finset.disjoint_left]
    intro e heXY heYY
    obtain ⟨he, x,y,hxy,hx,hy⟩ := Finset.mem_filter.mp heXY
    have hv := (Finset.mem_filter.mp heYY).2 x (by rw [hxy]; simp)
    exact hv (runEdges_reserved_subset a b hab T C l hx)
  have hc := Finset.card_union_of_disjoint hd
  rw [hunion] at hc
  exact hc.symm

lemma runEdges_count_identity {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) :
    (runEdges a b T C l).actual.card +
      ((runEdges a b T C l).shadow.filter (fun e => T e < a ∧ C e = true)).card =
      (runEdges a b T C l).shadow.card + ((runEdges a b T C l).actual.filter (fun e => b ≤ T e)).card := by
  have ht : ∀ e ∈ (runEdges a b T C l).shadow, T e < b := by
    intro e he
    rw [runEdges_shadow a b hab] at he
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp (greedy_seen _ he))).2
  have hf : (runEdges a b T C l).actual.filter (fun e => T e < b) =
      (runEdges a b T C l).shadow.filter (fun e => ¬ (T e < a ∧ C e = true)) := by
    rw [runEdges_before a b hab]
    apply Finset.filter_congr
    intro e he
    simp only [ht e he,true_and]
  have hs := Finset.card_filter_add_card_filter_not (s := (runEdges a b T C l).shadow) (fun e => T e < a ∧ C e = true)
  have ha := Finset.card_filter_add_card_filter_not (s := (runEdges a b T C l).actual) (fun e => T e < b)
  simp only [not_lt] at ha
  rw [←hf] at hs
  omega

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma step_reserved_mono {n : ℕ} (a b : ℝ) (S : State n) (e : Edge n) (t : ℝ) (c : Bool) :
    S.reserved ⊆ (step a b S e t c).reserved := by
  unfold step
  split_ifs <;> simp

lemma fold_edges_reserved_mono {n : ℕ} (a b : ℝ) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (S : State n) :
    S.reserved ⊆ (l.foldl (fun S e => step a b S e (T e) (C e)) S).reserved := by
  induction l generalizing S with
  | nil => exact Finset.Subset.refl _
  | cons e l ih => exact (step_reserved_mono a b S e (T e) (C e)).trans (ih _)

lemma fold_edges_actual_mono {n : ℕ} (a b : ℝ) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (S : State n) :
    S.actual ⊆ (l.foldl (fun S e => step a b S e (T e) (C e)) S).actual := by
  induction l generalizing S with
  | nil => exact Finset.Subset.refl _
  | cons e l ih => exact (actual_step_mono a b S e (T e) (C e)).trans (ih _)

lemma fold_blocks_late {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (S : State n) (e : Edge n) (he : e ∈ l) (ht : b ≤ T e)
    (hv : ∃ v ∈ e, v ∉ (l.foldl (fun S e => step a b S e (T e) (C e)) S).reserved) :
    ¬ free (l.foldl (fun S e => step a b S e (T e) (C e)) S).actual e := by
  induction l generalizing S with
  | nil => simp at he
  | cons f l ih =>
    simp only [List.foldl_cons] at hv ⊢
    rcases List.mem_cons.mp he with hfe | he
    · subst f
      intro hfree
      have hh := free_of_subset (fold_edges_actual_mono a b T C l (step a b S e (T e) (C e))) hfree
      have hta : ¬T e < a := not_lt.mpr (hab.trans ht)
      have htb : ¬T e < b := not_lt.mpr ht
      have hnr : ¬ (∀ v, v ∈ e → v ∈ S.reserved) := by
        obtain ⟨v,hve,hvr⟩ := hv
        intro hall
        apply hvr
        exact fold_edges_reserved_mono a b T C (e::l) S (hall v hve)
      by_cases hf : free S.actual e
      · have heq : (step a b S e (T e) (C e)).actual = insert e S.actual := by
          simp only [step,hta,htb,hf,hnr,true_and,not_false_eq_true,↓reduceIte]
        rw [heq] at hh
        exact not_free_insert_self S.actual e hh
      · have hsub := actual_step_mono a b S e (T e) (C e)
        exact hf (free_of_subset hsub hh)
    · exact ih _ he hv

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def reservedShadow {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℝ) (w : Sample G) : EdgeSet n :=
  (shadowAt G w.1 a).filter (fun e => ∃ he : e ∈ G.edgeSet, w.2 ⟨e,he⟩ = true)

set_option maxHeartbeats 700000 in
lemma execution_count_identity {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b) (w : Sample G) :
    ALG G a b w + ((reservedShadow G a w).card : ℝ) =
      ((shadowAt G w.1 b).card : ℝ) + ZXY G a b w + ZYY G a b w := by
  let T : Edge n → ℝ := fun e => if h : e ∈ G.edgeSet then w.1 ⟨e,h⟩ else 0
  let C : Edge n → Bool := fun e => if h : e ∈ G.edgeSet then w.2 ⟨e,h⟩ else false
  have hT (e : G.edgeSet) : T e.val = w.1 e := by simp [T,e.property]
  have hC (e : G.edgeSet) : C e.val = w.2 e := by simp [C,e.property]
  have hTG : (fun e : G.edgeSet => T e.val) = w.1 := funext hT
  let l := (orderedEdges G w.1).map Subtype.val
  let S := runEdges a b T C l
  have hexec : execution G a b w = S := execution_runEdges G a b w T C hT hC
  have hshadow : S.shadow = shadowAt G w.1 b := by
    rw [runEdges_shadow a b hab]
    have hh := shadowAt_values G T b
    rw [hTG] at hh
    exact hh.symm
  have hgraph (e : Edge n) (he : e ∈ S.actual) : e ∈ G.edgeSet := by
    have hm := List.mem_toFinset.mp (runEdges_seen a b T C l he)
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hm
    exact f.property
  have hgraphB (e : Edge n) (he : e ∈ S.shadow) : e ∈ G.edgeSet := by
    rw [hshadow] at he
    simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using shadowAt_subset_graph G w.1 b he
  have hl : l.Pairwise (fun e f => T e ≤ T f) := by
    apply List.pairwise_map.mpr
    simpa only [hT] using ordered_monotone G w.1
  have hloop : ∀ e ∈ l, ¬ e.IsDiag := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    exact G.not_isDiag_of_mem_edgeSet f.property
  have hrec : recovery G a b w = S.actual.filter (fun e => b ≤ T e) := by
    unfold recovery
    rw [hexec]
    apply Finset.filter_congr
    intro e he
    have heG := hgraph e he
    simp only [T,dif_pos heG]
    constructor
    · rintro ⟨h,hLate⟩; exact hLate
    · intro hLate; exact ⟨heG,hLate⟩
  have hAf : S.shadow.filter (fun e => T e < a) = shadowAt G w.1 a := by
    have hh := shadowAt_filter_time G T a b hab
    rw [hTG,←hshadow] at hh
    exact hh.symm
  have hR : reservedShadow G a w = S.shadow.filter (fun e => T e < a ∧ C e = true) := by
    unfold reservedShadow
    rw [←hAf]
    ext e
    by_cases he : e ∈ S.shadow
    · have heG := hgraphB e he
      simp only [Finset.mem_filter,he,true_and,C,dif_pos heG]
      constructor
      · rintro ⟨hT,⟨h,hcoin⟩⟩; exact ⟨hT,hcoin⟩
      · rintro ⟨hT,hcoin⟩; exact ⟨hT,heG,hcoin⟩
    · simp only [Finset.mem_filter,he,false_and]
  have hXY : ZXY G a b w =
      (((S.actual.filter (fun e => b ≤ T e)).filter (fun e => ∃ x y,
        e = s(x,y) ∧ x ∈ S.reserved ∧ y ∉ covered S.shadow)).card : ℝ) := by
    unfold ZXY
    rw [hrec,hexec]
    simp only [Yset,history,History.accepted,←hshadow,Finset.mem_sdiff,Finset.mem_univ,true_and]
  have hYY : ZYY G a b w =
      (((S.actual.filter (fun e => b ≤ T e)).filter (fun e => ∀ v, v ∈ e → v ∉ covered S.shadow)).card : ℝ) := by
    unfold ZYY
    rw [hrec]
    simp only [Yset,history,History.accepted,←hshadow,Finset.mem_sdiff,Finset.mem_univ,true_and]
  have hlate : ((S.actual.filter (fun e => b ≤ T e)).card : ℝ) = ZXY G a b w + ZYY G a b w := by
    rw [hXY,hYY]
    exact_mod_cast (runEdges_recovery_card a b hab T C l hl hloop).symm
  have hc := congrArg (fun k : ℕ => (k:ℝ)) (runEdges_count_identity a b hab T C l)
  simp only [Nat.cast_add] at hc
  change (S.actual.card:ℝ) + ((S.shadow.filter (fun e => T e < a ∧ C e = true)).card:ℝ) =
    (S.shadow.card:ℝ) + ((S.actual.filter (fun e => b ≤ T e)).card:ℝ) at hc
  rw [←hR,hshadow,hlate] at hc
  change (execution G a b w).actual.card + ((reservedShadow G a w).card:ℝ) = _
  rw [hexec]
  linarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma covered_biUnion {n : ℕ} (M : EdgeSet n) : covered M = M.biUnion Sym2.toFinset := by
  ext v
  simp [covered]

lemma covered_matching_card {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) :
    (covered M).card = 2*M.card := by
  rw [covered_biUnion,Finset.card_biUnion]
  · calc
      (∑ e ∈ M, e.toFinset.card) = ∑ e ∈ M, 2 := Finset.sum_congr rfl (fun e he => Sym2.card_toFinset_of_not_isDiag e (hM.1 e he))
      _ = _ := by simp [mul_comm]
  · intro e he f hf hne
    change Disjoint e.toFinset f.toFinset
    rw [Finset.disjoint_left]
    intro v hve hvf
    exact hM.2 e he f hf hne v (Sym2.mem_toFinset.mp hve) (Sym2.mem_toFinset.mp hvf)

lemma covered_card_le {n : ℕ} (B : EdgeSet n) : (covered B).card ≤ 2*B.card := by
  rw [covered_biUnion]
  calc
    _ ≤ ∑ e ∈ B, e.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ e ∈ B, 2 := Finset.sum_le_sum fun e he => by rw [Sym2.card_toFinset]; split_ifs <;> omega
    _ = _ := by simp [mul_comm]

lemma uncovered_matching_card {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (C : Finset (Fin n)) :
    (covered M \ C).card = ∑ e ∈ M, (e.toFinset \ C).card := by
  have heq : covered M \ C = M.biUnion (fun e => e.toFinset \ C) := by
    ext v
    simp only [covered,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_biUnion,Sym2.mem_toFinset]
    aesop
  rw [heq]
  apply Finset.card_biUnion
  intro e he f hf hne
  change Disjoint (e.toFinset \ C) (f.toFinset \ C)
  rw [Finset.disjoint_left]
  intro v hve hvf
  exact hM.2 e he f hf hne v (Sym2.mem_toFinset.mp (Finset.mem_sdiff.mp hve).1)
    (Sym2.mem_toFinset.mp (Finset.mem_sdiff.mp hvf).1)

lemma new_matching_edge_free {n : ℕ} (A B : EdgeSet n) (hAB : A ⊆ B) (hB : IsMatching B)
    (e : Edge n) (heB : e ∈ B) (heA : e ∉ A) : free A e := by
  intro v hv hcov
  obtain ⟨f,hf,hvf⟩ := (show ∃ f ∈ A, v ∈ f from by simpa [covered] using hcov)
  have hne : e ≠ f := fun heq => heA (heq.symm ▸ hf)
  exact hB.2 e heB f (hAB hf) hne v hv hvf

def crossPred {n : ℕ} (A B : EdgeSet n) (e : Edge n) : Prop :=
  ∃ x y, e = s(x,y) ∧ x ∈ covered A ∧ y ∉ covered B

lemma pair_uncovered_card {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y) (C : Finset α) :
    (({x,y} : Finset α) \ C).card = (if x ∈ C then 0 else 1) + (if y ∈ C then 0 else 1) := by
  have hsY : ({y} : Finset α) \ C = (if y ∈ C then ∅ else {y}) := by
    ext v
    by_cases hy : y ∈ C <;> by_cases hv : v = y
    · subst v; simp [hy]
    · simp [hy,hv]
    · subst v; simp [hy]
    · simp [hy,hv]
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;>
    simp [Finset.insert_sdiff_of_mem,Finset.insert_sdiff_of_notMem,hx,hy,hxy,hsY]

lemma boolean_vertex_account (A1 A2 B1 B2 C D : Prop) [Decidable A1] [Decidable A2]
    [Decidable B1] [Decidable B2] [Decidable C] [Decidable D]
    (h1 : A1 → B1) (h2 : A2 → B2) (hD : D → (¬A1 ∧ ¬A2) ∧ B1 ∧ B2)
    (hC : (A1 ∧ ¬B2) ∨ (A2 ∧ ¬B1) → C) :
    (if B1 then 0 else 1) + (if B2 then 0 else 1) + (if D then 1 else 0) ≤
      (if C then 1 else 0) + (if ¬A1 ∧ ¬A2 then 1 else 0) + (if ¬B1 ∧ ¬B2 then 1 else 0) := by
  by_cases ha1 : A1 <;> by_cases ha2 : A2 <;> by_cases hb1 : B1 <;> by_cases hb2 : B2 <;>
    by_cases hc : C <;> by_cases hd : D <;> simp_all <;> omega

set_option maxHeartbeats 700000 in
lemma per_edge_accounting {n : ℕ} (A B : EdgeSet n) (hAB : A ⊆ B) (hB : IsMatching B)
    (e : Edge n) (hne : ¬ e.IsDiag) :
    (e.toFinset \ covered B).card + (if e ∈ B \ A then 1 else 0) ≤
      (if crossPred A B e then 1 else 0) + (if free A e then 1 else 0) + (if free B e then 1 else 0) := by
  induction e using Sym2.inductionOn with | hf x y =>
    have hxy : x ≠ y := by simpa using hne
    have hxa : x ∈ covered A → x ∈ covered B := fun h => covered_mono hAB h
    have hya : y ∈ covered A → y ∈ covered B := fun h => covered_mono hAB h
    have hfree : s(x,y) ∈ B \ A → free A s(x,y) := fun h =>
      new_matching_edge_free A B hAB hB _ (Finset.mem_sdiff.mp h).1 (Finset.mem_sdiff.mp h).2
    have hcov : s(x,y) ∈ B \ A → x ∈ covered B ∧ y ∈ covered B := by
      intro h
      have hb := (Finset.mem_sdiff.mp h).1
      constructor <;> simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and]
      · exact ⟨s(x,y),hb,by simp⟩
      · exact ⟨s(x,y),hb,by simp⟩
    have hcross : (x ∈ covered A ∧ y ∉ covered B) ∨ (y ∈ covered A ∧ x ∉ covered B) → crossPred A B s(x,y) := by
      intro h
      rcases h with h | h
      · exact ⟨x,y,rfl,h⟩
      · exact ⟨y,x,Sym2.eq_swap,h⟩
    have hfA : free A s(x,y) ↔ x ∉ covered A ∧ y ∉ covered A := by simp [free,Sym2.mem_iff]
    have hfB : free B s(x,y) ↔ x ∉ covered B ∧ y ∉ covered B := by simp [free,Sym2.mem_iff]
    rw [Sym2.toFinset_mk_eq,pair_uncovered_card x y hxy (covered B)]
    simp only [hfA,hfB]
    exact boolean_vertex_account _ _ _ _ _ _ hxa hya
      (fun h => ⟨hfA.mp (hfree h),hcov h⟩) hcross

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma matching_vertex_accounting {n : ℕ} (M A B : EdgeSet n) (hM : IsMatching M)
    (hB : IsMatching B) (hAB : A ⊆ B) :
    2*M.card + (M ∩ (B \ A)).card ≤ 2*B.card + (M.filter (crossPred A B)).card +
      (M.filter (free A)).card + (M.filter (free B)).card := by
  have hsum := Finset.sum_le_sum (s := M) (fun e he => per_edge_accounting A B hAB hB e (hM.1 e he))
  simp only [Finset.sum_add_distrib] at hsum
  rw [← Finset.card_filter (fun e => e ∈ B \ A) M,← Finset.card_filter (crossPred A B) M,
    ← Finset.card_filter (free A) M,← Finset.card_filter (free B) M] at hsum
  have hbonus : M.filter (fun e => e ∈ B \ A) = M ∩ (B \ A) := by ext e; simp
  rw [hbonus,←uncovered_matching_card M hM (covered B)] at hsum
  have hsum' : (covered M \ covered B).card + (M ∩ (B \ A)).card ≤
      (M.filter (crossPred A B)).card + (M.filter (free A)).card + (M.filter (free B)).card := by
    convert! hsum using 1
  have hpart := Finset.card_sdiff_add_card_inter (covered M) (covered B)
  rw [covered_matching_card M hM] at hpart
  have hi := Finset.card_le_card (Finset.inter_subset_right (s₁ := covered M) (s₂ := covered B))
  have hb := covered_card_le B
  clear hsum
  omega

lemma greedy_fold_matching {n : ℕ} (l : List (Edge n)) (F : EdgeSet n)
    (hF : IsMatching F) (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    IsMatching (l.foldl (fun F e => if free F e then insert e F else F) F) := by
  induction l generalizing F with
  | nil => exact hF
  | cons e l ih =>
    simp only [List.foldl_cons]
    apply ih
    · by_cases he : free F e
      · simpa only [he,↓reduceIte] using matching_insert hF (hl e (by simp)) he
      · simpa only [he,↓reduceIte] using hF
    · intro f hf
      exact hl f (List.mem_cons_of_mem _ hf)

lemma shadowAt_matching {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (u : ℝ) :
    IsMatching (shadowAt G t u) := by
  apply greedy_fold_matching _ ∅ (by simp [IsMatching])
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  exact G.not_isDiag_of_mem_edgeSet f.property

lemma MYY_history_eq {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (b : ℝ) (t : Times G) :
    MYY M (history G b t) = M.filter (free (shadowAt G t b)) := by
  ext e
  simp only [MYY,free,Yset,history,History.accepted,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]

lemma M1Y_history_eq {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (a b : ℝ) (t : Times G) (hab : a ≤ b) :
    M1Y M a (history G b t) = M.filter (crossPred (shadowAt G t a) (shadowAt G t b)) := by
  unfold M1Y
  rw [early_history_eq G t a b hab]
  ext e
  simp only [crossPred,Yset,history,History.accepted,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]

lemma vertex_accounting {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (hM : IsMatching M)
    (hmax : M.card = OPT G) (a b : ℝ) (hab : a ≤ b) (t : Times G) :
    ((M1Y M a (history G b t)).card : ℝ) + (MYY M (history G b t)).card ≥
      2 * (OPT G : ℝ) - 2 * (shadowAt G t b).card - U G M t a + (M2 G M a b t).card := by
  have hh := matching_vertex_accounting M (shadowAt G t a) (shadowAt G t b) hM
    (shadowAt_matching G t b) (shadowAt_mono G t a b hab)
  have hr := Nat.cast_le (α:=ℝ).mpr hh
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hr
  rw [M1Y_history_eq G M a b t hab,MYY_history_eq]
  change _ + _ ≥ 2*(OPT G:ℝ) - 2*((shadowAt G t b).card:ℝ) -
    ((M.filter (free (shadowAt G t a))).card:ℝ) + (M ∩ (shadowAt G t b \ shadowAt G t a)).card
  rw [hmax] at hr
  linarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma matching_inter_count {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (A : Finset (Fin n)) :
    (A ∩ covered M).card = ∑ e ∈ M, (A ∩ covered {e}).card := by
  have heq : A ∩ covered M = M.biUnion (fun e => A ∩ covered {e}) := by
    ext v
    simp only [Finset.mem_inter,Finset.mem_biUnion,covered_singleton,Sym2.mem_toFinset,
      covered,Finset.mem_filter,Finset.mem_univ,true_and]
    aesop
  rw [heq,Finset.card_biUnion]
  intro e he f hf hne
  change Disjoint (A ∩ covered {e}) (A ∩ covered {f})
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact hM.2 e he f hf hne v
    (by simpa only [covered_singleton,Sym2.mem_toFinset] using (Finset.mem_inter.mp hv).2)
    (by simpa only [covered_singleton,Sym2.mem_toFinset] using (Finset.mem_inter.mp hv').2)

lemma pair_inter_of_cross {n : ℕ} (A : Finset (Fin n)) (x y : Fin n) (hx : x ∈ A) (hy : y ∉ A) :
    A ∩ covered {s(x,y)} = {x} := by
  ext v
  simp only [Finset.mem_inter,covered_singleton,Sym2.mem_toFinset,Sym2.mem_iff,Finset.mem_singleton]
  constructor
  · rintro ⟨hv,rfl | rfl⟩
    · rfl
    · exact (hy hv).elim
  · rintro rfl
    exact ⟨hx,Or.inl rfl⟩

lemma matching_cross_count {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (A : Finset (Fin n))
    (hcross : ∀ e ∈ M, ∃ x y, e = s(x,y) ∧ x ∈ A ∧ y ∉ A) :
    (A ∩ covered M).card = M.card := by
  rw [matching_inter_count M hM A]
  have he (e : Edge n) (he : e ∈ M) : (A ∩ covered {e}).card = 1 := by
    obtain ⟨x,y,rfl,hx,hy⟩ := hcross e he
    rw [pair_inter_of_cross A x y hx hy]
    exact Finset.card_singleton _
  rw [Finset.sum_congr rfl he]
  simp

lemma matching_hit_count {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (A : Finset (Fin n))
    (hhit : ∀ e ∈ M, ∃ v ∈ e, v ∈ A) : M.card ≤ (A ∩ covered M).card := by
  rw [matching_inter_count M hM A]
  calc
    M.card = ∑ e ∈ M, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun e he => by
      obtain ⟨v,hve,hvA⟩ := hhit e he
      apply Finset.card_pos.mpr
      exact ⟨v,Finset.mem_inter.mpr ⟨hvA,by simpa only [covered_singleton,Sym2.mem_toFinset] using hve⟩⟩)

lemma matching_subset {n : ℕ} (M F : EdgeSet n) (hM : IsMatching M) (hF : F ⊆ M) : IsMatching F := by
  exact ⟨fun e he => hM.1 e (hF he),fun e he f hf hne => hM.2 e (hF he) f (hF hf) hne⟩

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def edgeTimes {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (e : Edge n) : ℝ :=
  if h : e ∈ G.edgeSet then t ⟨e,h⟩ else 0

def edgeCoins {n : ℕ} (G : SimpleGraph (Fin n)) (c : Coins G) (e : Edge n) : Bool :=
  if h : e ∈ G.edgeSet then c ⟨e,h⟩ else false

def executionList {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) : List (Edge n) :=
  (orderedEdges G t).map Subtype.val

lemma edgeTimes_val {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (e : G.edgeSet) :
    edgeTimes G t e.val = t e := by simp [edgeTimes,e.property]

lemma edgeCoins_val {n : ℕ} (G : SimpleGraph (Fin n)) (c : Coins G) (e : G.edgeSet) :
    edgeCoins G c e.val = c e := by simp [edgeCoins,e.property]

lemma execution_runEdges_eq {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) :
    execution G a b w = runEdges a b (edgeTimes G w.1) (edgeCoins G w.2) (executionList G w.1) :=
  execution_runEdges G a b w _ _ (edgeTimes_val G w.1) (edgeCoins_val G w.2)

lemma execution_shadow_eq {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b) (w : Sample G) :
    (execution G a b w).shadow = shadowAt G w.1 b := by
  rw [execution_runEdges_eq,runEdges_shadow a b hab]
  have hh := shadowAt_values G (edgeTimes G w.1) b
  have hT : (fun f : G.edgeSet => edgeTimes G w.1 f.val) = w.1 := funext (edgeTimes_val G w.1)
  rw [hT] at hh
  exact hh.symm

lemma execution_actual_graph {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) :
    (execution G a b w).actual ⊆ graphEdges G := by
  rw [execution_runEdges_eq]
  intro e he
  have hm := List.mem_toFinset.mp (runEdges_seen a b (edgeTimes G w.1) (edgeCoins G w.2) (executionList G w.1) he)
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hm
  simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using f.property

lemma recovery_filter_eq {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) :
    recovery G a b w = (execution G a b w).actual.filter (fun e => b ≤ edgeTimes G w.1 e) := by
  unfold recovery
  apply Finset.filter_congr
  intro e he
  have heG : e ∈ G.edgeSet := by
    simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using execution_actual_graph G a b w he
  simp only [edgeTimes,dif_pos heG]
  constructor
  · rintro ⟨h,ht⟩; exact ht
  · intro ht; exact ⟨heG,ht⟩

lemma execution_list_order {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) :
    (executionList G t).Pairwise (fun e f => edgeTimes G t e ≤ edgeTimes G t f) := by
  apply List.pairwise_map.mpr
  simpa only [edgeTimes_val] using ordered_monotone G t

lemma execution_list_loopless {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) :
    ∀ e ∈ executionList G t, ¬ e.IsDiag := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  exact G.not_isDiag_of_mem_edgeSet f.property

lemma execution_matching {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b) (w : Sample G) :
    IsMatching (execution G a b w).actual := by
  rw [execution_runEdges_eq]
  exact runEdges_matching a b hab _ _ _ (execution_list_order G w.1) (execution_list_loopless G w.1)

lemma execution_reserved_subset {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b) (w : Sample G) :
    (execution G a b w).reserved ⊆ covered (shadowAt G w.1 b) := by
  rw [←execution_shadow_eq G a b hab w,execution_runEdges_eq]
  exact runEdges_reserved_subset a b hab _ _ _

lemma early_actual_subset_shadow {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b) (w : Sample G) :
    ((execution G a b w).actual.filter (fun e => edgeTimes G w.1 e < b)) ⊆ shadowAt G w.1 b := by
  rw [←execution_shadow_eq G a b hab w,execution_runEdges_eq,runEdges_before a b hab]
  exact Finset.filter_subset _ _

lemma covered_actual_outside_shadow {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b)
    (w : Sample G) (v : Fin n) (hv : v ∈ covered (execution G a b w).actual)
    (hvB : v ∉ covered (shadowAt G w.1 b)) : v ∈ covered (recovery G a b w) := by
  obtain ⟨e,he,hve⟩ := (Finset.mem_filter.mp hv).2
  have ht : b ≤ edgeTimes G w.1 e := by
    by_contra hn
    have heB := early_actual_subset_shadow G a b hab w (Finset.mem_filter.mpr ⟨he,lt_of_not_ge hn⟩)
    exact hvB (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,heB,hve⟩)
  rw [recovery_filter_eq]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,Finset.mem_filter.mpr ⟨he,ht⟩,hve⟩

lemma recovery_blocks_Y {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b)
    (w : Sample G) (e : G.edgeSet) (heY : free (shadowAt G w.1 b) e.val) :
    ¬ free (recovery G a b w) e.val := by
  have ht : b ≤ edgeTimes G w.1 e.val := by
    rw [edgeTimes_val]
    exact free_shadow_implies_time G w.1 b e heY
  have heL : e.val ∈ executionList G w.1 :=
    List.mem_map.mpr ⟨e,mem_orderedEdges G w.1 e,rfl⟩
  have hv : ∃ v ∈ e.val, v ∉ (execution G a b w).reserved := by
    refine ⟨e.val.out.1,Sym2.out_fst_mem e.val,?_⟩
    intro hv
    exact heY _ (Sym2.out_fst_mem e.val) (execution_reserved_subset G a b hab w hv)
  rw [execution_runEdges_eq] at hv
  have hblocked := fold_blocks_late a b hab (edgeTimes G w.1) (edgeCoins G w.2)
    (executionList G w.1) (initial n) e.val heL ht hv
  intro hf
  apply hblocked
  change free (runEdges a b (edgeTimes G w.1) (edgeCoins G w.2) (executionList G w.1)).actual e.val
  rw [←execution_runEdges_eq]
  intro v hve hvc
  have hvr := covered_actual_outside_shadow G a b hab w v hvc (heY v hve)
  exact hf v hve hvr

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma measurable_orderFor_score {α : Type*} [DecidableEq α] (E : Finset α) (f : List α → ℝ) :
    Measurable (fun t : E → ℝ => f (orderFor E t)) := by
  letI : MeasurableSpace (Equiv.Perm (Fin (Fintype.card E))) := ⊤
  letI : MeasurableSingletonClass (Equiv.Perm (Fin (Fintype.card E))) := ⟨fun _ => trivial⟩
  let enum := (Fintype.equivFin E).symm
  have hs : Measurable (Tuple.sort : (Fin (Fintype.card E) → ℝ) → Equiv.Perm (Fin (Fintype.card E))) := by
    apply measurable_to_countable'
    intro π
    exact sort_fiber_measurable π
  have ht : Measurable (fun t : E → ℝ => t ∘ enum) := measurable_pi_iff.mpr (fun i => measurable_pi_apply (enum i))
  exact (measurable_of_finite (fun π => f (enumerationOrder E enum π))).comp (hs.comp ht)

lemma orderFor_eq_sorted {α : Type*} [DecidableEq α] (E : Finset α) (T : α → ℝ)
    (hT : Set.InjOn T E) (l : List α) (hn : l.Nodup) (he : l.toFinset = E)
    (hs : l.Pairwise (fun e f => T e ≤ T f)) : orderFor E (fun e => T e.val) = l := by
  have hm := (mem_permLists E _).mp (orderFor_mem E (fun e => T e.val))
  have hp : (orderFor E (fun e => T e.val)).Perm l := List.perm_of_nodup_nodup_toFinset_eq hm.1 hn (hm.2.trans he.symm)
  apply List.Perm.eq_of_pairwise (le:=fun e f => T e ≤ T f) ?_ (orderFor_pairwise E T) hs hp
  intro e f he' hf' hef hfe
  apply hT
  · rw [←hm.2]; exact List.mem_toFinset.mpr he'
  · rw [←he]; exact List.mem_toFinset.mpr hf'
  · exact le_antisymm hef hfe

lemma execution_orderFor {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (ht : Function.Injective t)
    (E : EdgeSet n) (hEG : E ⊆ graphEdges G) :
    orderFor E (fun e => edgeTimes G t e.val) = (executionList G t).filter (fun e => e ∈ E) := by
  apply orderFor_eq_sorted E (edgeTimes G t)
  · intro e he f hf hef
    have heG : e ∈ G.edgeSet := by simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hEG he
    have hfG : f ∈ G.edgeSet := by simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hEG hf
    have hte := edgeTimes_val G t (⟨e,heG⟩ : G.edgeSet)
    have htf := edgeTimes_val G t (⟨f,hfG⟩ : G.edgeSet)
    rw [hte,htf] at hef
    exact congrArg Subtype.val (ht hef)
  · exact ((orderedEdges_nodup G t).map Subtype.val_injective).filter _
  · ext e
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    constructor
    · exact And.right
    · intro he
      have heG : e ∈ G.edgeSet := by simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hEG he
      exact ⟨List.mem_map.mpr ⟨⟨e,heG⟩,mem_orderedEdges G t _,rfl⟩,he⟩
  · exact (execution_list_order G t).filter _

lemma coupledRun_orderFor {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sample G) (ht : Function.Injective w.1)
    (E F : EdgeSet n) (hEG : E ⊆ graphEdges G) (hFE : F ⊆ E) :
    coupledRun G F w = greedy ((orderFor E (fun e => edgeTimes G w.1 e.val)).filter (fun e => e ∈ F)) := by
  rw [execution_orderFor G w.1 ht E hEG,filter_filter_subset E F hFE]
  rfl

lemma orderFor_map {α β : Type*} [DecidableEq α] [DecidableEq β] (E : Finset α)
    (g : α ↪ β) (T : β → ℝ) (hT : Set.InjOn T (E.map g)) :
    orderFor (E.map g) (fun i => T i.val) = (orderFor E (fun i => T (g i.val))).map g := by
  have hm := (mem_permLists E _).mp (orderFor_mem E (fun i => T (g i.val)))
  apply orderFor_eq_sorted (E.map g) T hT
  · exact hm.1.map g.injective
  · ext b
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_map]
    have hmem (a : α) : a ∈ orderFor E (fun i => T (g i.val)) ↔ a ∈ E := by
      constructor
      · intro ha
        have hh := List.mem_toFinset.mpr ha
        rw [hm.2] at hh
        exact hh
      · intro ha
        rw [←hm.2] at ha
        exact List.mem_toFinset.mp ha
    simp only [hmem]
  · exact List.pairwise_map.mpr (orderFor_pairwise E (fun a => T (g a)))

lemma coupledRun_greedy_orderFor {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sample G) (ht : Function.Injective w.1)
    (F : EdgeSet n) (hFG : F ⊆ graphEdges G) :
    coupledRun G F w = greedy (orderFor F (fun e => edgeTimes G w.1 e.val)) := by
  rw [execution_orderFor G w.1 ht F hFG]
  rfl

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma filter_initial_lower {α : Type*} (l : List α) (R : α → α → Prop) (hl : l.Pairwise R)
    (P : α → Prop) [DecidablePred P] (hP : ∀ x y, R x y → P y → P x) :
    (l.filter (fun x => P x)).IsPrefix l := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    by_cases hx : P x
    · simp only [List.filter_cons,decide_eq_true_eq,hx,↓reduceIte]
      obtain ⟨r,hr⟩ := ih hl.2
      exact ⟨r,by simpa only [List.cons_append] using congrArg (List.cons x) hr⟩
    · have heq : (x::l).filter (fun x => P x) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact fun h => hx (hP x y (hl.1 y hy) h)
      rw [heq]
      exact List.nil_prefix

lemma greedy_filter_initial {n : ℕ} (l : List (Edge n)) (P : Edge n → Prop) [DecidablePred P]
    (hp : (l.filter (fun e => P e)).IsPrefix l) :
    greedy (l.filter (fun e => P e)) = (greedy l).filter P := by
  let before := l.filter (fun e => P e)
  obtain ⟨after,hs⟩ := hp
  have hb : before.filter (fun e => P e) = before := by dsimp [before]; simp
  have hfilter := congrArg (List.filter (fun e => P e)) hs
  change (before ++ after).filter (fun e => P e) = before at hfilter
  rw [List.filter_append,hb] at hfilter
  have hn : after.filter (fun e => P e) = [] := List.append_cancel_left (as:=before) (by simpa only [List.append_nil] using hfilter)
  have ha : ∀ e ∈ after, ¬P e := by
    intro e he
    simpa only [decide_eq_true_eq] using List.filter_eq_nil_iff.mp hn e he
  have hfold : greedy l = after.foldl (fun F e => if free F e then insert e F else F) (greedy before) := by
    rw [←hs]
    unfold greedy
    rw [List.foldl_append]
  ext e
  rw [Finset.mem_filter]
  constructor
  · intro he
    refine ⟨greedy_prefix_mono ⟨after,hs⟩ he,?_⟩
    have hm := List.mem_toFinset.mp (greedy_seen before he)
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  · rintro ⟨he,hP⟩
    rw [hfold] at he
    rcases Finset.mem_union.mp (greedy_fold_seen after (greedy before) he) with he | he
    · exact he
    · exact (ha e (List.mem_toFinset.mp he) hP).elim

lemma greedy_filter_le_time {n : ℕ} (l : List (Edge n)) (T : Edge n → ℝ)
    (hl : l.Pairwise (fun e f => T e ≤ T f)) (s : ℝ) :
    greedy (l.filter (fun e => T e ≤ s)) = (greedy l).filter (fun e => T e ≤ s) :=
  greedy_filter_initial l _ (filter_initial_lower l _ hl _ (fun x y hxy hy => hxy.trans hy))

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def clockPrefix {n : ℕ} (E : EdgeSet n) (t : Edge n → ℝ) (s : ℝ) : List (Edge n) :=
  (orderFor E (fun e => t e.val)).filter (fun e => t e ≤ s)

def clockState {n : ℕ} (E : EdgeSet n) (t : Edge n → ℝ) (s : ℝ) : EdgeSet n :=
  greedy (clockPrefix E t s)

lemma orderFor_filter_sorted {α : Type*} [DecidableEq α] (E : Finset α) (t : α → ℝ)
    (P : α → Prop) [DecidablePred P] (ht : Set.InjOn t (E.filter P)) :
    orderFor (E.filter P) (fun e => t e.val) = (orderFor E (fun e => t e.val)).filter (fun e => P e) := by
  have hm := (mem_permLists E _).mp (orderFor_mem E (fun e => t e.val))
  apply orderFor_eq_sorted _ t ht
  · exact hm.1.filter _
  · simpa only [List.toFinset_filter,hm.2,decide_eq_true_eq]
  · exact (orderFor_pairwise E t).filter _

lemma clockPrefix_sorted {n : ℕ} (E : EdgeSet n) (t : Edge n → ℝ) (s : ℝ)
    (ht : Set.InjOn t (E.filter (fun e => t e ≤ s))) :
    clockPrefix E t s = orderFor (E.filter (fun e => t e ≤ s)) (fun e => t e.val) :=
  (orderFor_filter_sorted E t _ ht).symm

lemma clockPrefix_update_after {n : ℕ} (E : EdgeSet n) (t : Edge n → ℝ) (e : Edge n)
    (s x : ℝ) (he : s < t e) (hx : s < x) (ht : Set.InjOn t E) :
    clockPrefix E (Function.update t e x) s = clockPrefix E t s := by
  have hset : E.filter (fun f => Function.update t e x f ≤ s) = E.filter (fun f => t f ≤ s) := by
    apply Finset.filter_congr
    intro f hf
    by_cases hf' : f = e
    · subst f
      simp [Function.update_self,not_le.mpr he,not_le.mpr hx]
    · simp [Function.update_of_ne hf']
  have hsame : ∀ f ∈ E.filter (fun f => t f ≤ s), Function.update t e x f = t f := by
    intro f hf
    apply Function.update_of_ne
    intro hfe
    subst f
    exact (not_le.mpr he) (Finset.mem_filter.mp hf).2
  have hi : Set.InjOn (Function.update t e x) (E.filter (fun f => Function.update t e x f ≤ s)) := by
    rw [hset]
    intro f hf g hg hfg
    apply ht (Finset.mem_filter.mp hf).1 (Finset.mem_filter.mp hg).1
    rwa [hsame f hf,hsame g hg] at hfg
  rw [clockPrefix_sorted E _ s hi,clockPrefix_sorted E t s (ht.mono (Finset.filter_subset _ _)),hset]
  congr 1
  funext f
  exact hsame f.val f.property

lemma clockState_free_late {n : ℕ} (E : EdgeSet n) (t : Edge n → ℝ) (s : ℝ)
    (e : Edge n) (he : e ∈ E) (hf : free (clockState E t s) e) : s < t e := by
  by_contra hn
  have hseen : e ∈ clockPrefix E t s := by
    apply List.mem_filter.mpr
    refine ⟨?_,by simpa using le_of_not_gt hn⟩
    have hm := (mem_permLists E _).mp (orderFor_mem E (fun e => t e.val))
    apply List.mem_toFinset.mp
    rwa [hm.2]
  exact greedy_blocks_seen _ e hseen hf

lemma clockState_update_after {n : ℕ} (E : EdgeSet n) (t : Edge n → ℝ) (e : Edge n)
    (s x : ℝ) (he : s < t e) (hx : s < x) (ht : Set.InjOn t E) :
    clockState E (Function.update t e x) s = clockState E t s := by
  unfold clockState
  rw [clockPrefix_update_after E t e s x he hx ht]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma measurable_clockState {n : ℕ} (E : EdgeSet n) (s : ℝ) :
    Measurable (fun t : Edge n → ℝ => clockState E t s) := by
  letI : MeasurableSpace (Equiv.Perm (Fin (Fintype.card E))) := ⊤
  letI : MeasurableSingletonClass (Equiv.Perm (Fin (Fintype.card E))) := ⟨fun _ => trivial⟩
  let enum := (Fintype.equivFin E).symm
  have hs : Measurable (fun t : Edge n → ℝ => Tuple.sort (fun i => t (enum i).val)) := by
    apply measurable_to_countable'
    intro π
    exact (sort_fiber_measurable π).preimage (measurable_pi_iff.mpr (fun i => measurable_pi_apply (enum i).val))
  have hf : Measurable (fun t : Edge n → ℝ => E.filter (fun e => t e ≤ s)) := by
    rw [measurable_finset_iff]
    intro e
    apply measurableSet_setOfPred.mp
    by_cases he : e ∈ E
    · simpa only [Finset.mem_filter,he,true_and] using measurableSet_le (measurable_pi_apply e) (measurable_const : Measurable (fun _ : Edge n → ℝ => s))
    · simp only [Finset.mem_filter,he,false_and]
      exact (MeasurableSet.empty : MeasurableSet (∅ : Set (Edge n → ℝ)))
  let f : Equiv.Perm (Fin (Fintype.card E)) × EdgeSet n → EdgeSet n := fun z =>
    greedy ((enumerationOrder E enum z.1).filter (fun e => e ∈ z.2))
  have hh := (measurable_of_finite f).comp (hs.prodMk hf)
  convert! hh using 1
  funext t
  unfold clockState clockPrefix orderFor f
  congr 1
  apply List.filter_congr
  intro e he
  have heE : e ∈ E := by
    have hm := (mem_permLists E _).mp (orderFor_mem E (fun e => t e.val))
    rw [←hm.2]
    exact List.mem_toFinset.mpr he
  simp [heE]

lemma integrable_clockCell {n : ℕ} (E : EdgeSet n) (s : ℝ) (F : EdgeSet n) (e : Edge n)
    (μ : Measure (Edge n → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun t => if clockState E (Function.update t e 1) s = F then (1:ℝ) else 0) μ := by
  exact integrable_finite_comp μ _ ((measurable_clockState E s).comp measurable_update_left)
    (fun A : EdgeSet n => if A = F then (1:ℝ) else 0)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def realInsert {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι)
    (z : ℝ × ({i : ι // i ≠ e} → ℝ)) : ι → ℝ := fun i => if h : i = e then z.1 else z.2 ⟨i,h⟩

lemma realInsert_self {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι)
    (z : ℝ × ({i : ι // i ≠ e} → ℝ)) : realInsert e z e = z.1 := by simp [realInsert]

def realSplit {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι) :
    (ι → ℝ) ≃ᵐ ℝ × ({i : ι // i ≠ e} → ℝ) where
  toFun t := (t e,fun i => t i.val)
  invFun := realInsert e
  left_inv t := by
    funext i
    by_cases hi : i = e <;> simp [realInsert,hi]
  right_inv z := by
    apply Prod.ext
    · exact realInsert_self e z
    · funext i
      simp only [realInsert,i.property,↓reduceDIte]
  measurable_toFun := (measurable_pi_apply e).prodMk (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val))
  measurable_invFun := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun z : ℝ × ({i : ι // i ≠ e} → ℝ) => if h : i = e then z.1 else z.2 ⟨i,h⟩)
    split_ifs
    · exact measurable_fst
    · exact (measurable_pi_apply _).comp measurable_snd

lemma realSplit_preserving {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (e : ι) :
    MeasurePreserving (realSplit e) (Measure.pi μ) ((μ e).prod (Measure.pi (fun i : {i : ι // i ≠ e} => μ i.val))) := by
  letI : Fintype {i : ι // i = e} := Subtype.fintype _
  have hs := measurePreserving_piEquivPiSubtypeProd μ (fun i => i = e)
  have hf := measurePreserving_eval (fun i : {i : ι // i = e} => μ i.val) (⟨e,rfl⟩ : {i : ι // i = e})
  convert! (hf.prod (MeasurePreserving.id (Measure.pi (fun i : {i : ι // i ≠ e} => μ i.val)))).comp hs using 1

lemma real_pi_integral_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (e : ι)
    (F : (ι → ℝ) → ℝ) (hF : Integrable F (Measure.pi μ)) :
    (∫ t, F t ∂Measure.pi μ) = ∫ x, ∫ r, F (realInsert e (x,r))
      ∂Measure.pi (fun i : {i : ι // i ≠ e} => μ i.val) ∂μ e := by
  have hinv := MeasurePreserving.symm (realSplit e) (realSplit_preserving μ e)
  have hi := hinv.integrable_comp_of_integrable hF
  calc
    _ = ∫ z, F ((realSplit e).symm z) ∂(μ e).prod (Measure.pi (fun i : {i : ι // i ≠ e} => μ i.val)) :=
      (hinv.integral_comp' F).symm
    _ = _ := integral_prod _ hi

lemma coordinate_independent_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (e : ι)
    (F : (ι → ℝ) → ℝ) (hF : Integrable F (Measure.pi μ))
    (hignore : ∀ t x, F (Function.update t e x) = F t) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ t, (if t e ∈ S then F t else 0) ∂Measure.pi μ) = (μ e).real S*(∫ t, F t ∂Measure.pi μ) := by
  have hEvent : MeasurableSet {t : ι → ℝ | t e ∈ S} := hS.preimage (measurable_pi_apply e)
  have hflag : Integrable (fun t : ι → ℝ => if t e ∈ S then F t else 0) (Measure.pi μ) := by
    convert! hF.indicator hEvent using 1
  have hins (x : ℝ) (r : {i : ι // i ≠ e} → ℝ) : F (realInsert e (x,r)) = F (realInsert e (0,r)) := by
    rw [←hignore (realInsert e (0,r)) x]
    apply congrArg F
    funext i
    by_cases hi : i = e <;> simp [realInsert,Function.update,hi]
  rw [real_pi_integral_split μ e _ hflag,real_pi_integral_split μ e F hF]
  simp_rw [realInsert_self,hins]
  let R := ∫ r, F (realInsert e (0,r)) ∂Measure.pi (fun i : {i : ι // i ≠ e} => μ i.val)
  have hinner (x : ℝ) :
      (∫ r, (if x ∈ S then F (realInsert e (0,r)) else 0) ∂Measure.pi (fun i : {i : ι // i ≠ e} => μ i.val)) =
        S.indicator (fun _ => R) x := by
    by_cases hx : x ∈ S <;> simp [Set.indicator_apply,hx,R]
  simp_rw [hinner]
  change (∫ x, S.indicator (fun _ => R) x ∂μ e) = (μ e).real S*(∫ _ : ℝ, R ∂μ e)
  rw [integral_indicator hS,integral_const,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,measure_univ,ENNReal.toReal_one,one_smul,smul_eq_mul,one_mul]

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
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma measurable_history {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) : Measurable (history G b) := by
  apply Measurable.prodMk (measurable_shadow_fixed G b)
  apply measurable_pi_iff.mpr
  intro e
  by_cases he : e ∈ G.edgeSet
  · simp only [history,he,↓reduceDIte]
    change Measurable (fun t : Times G => if e ∈ shadowAt G t b then t ⟨e,he⟩ else 0)
    exact (measurable_pi_apply _).ite ((measurableSet_mem_finset e).preimage (measurable_shadow_fixed G b)) measurable_const
  · simpa only [history,he,↓reduceDIte] using (measurable_const : Measurable (fun _ : Times G => (0:ℝ)))

lemma measurable_early {n : ℕ} (a : ℝ) : Measurable (early (n:=n) a) := by
  rw [measurable_finset_iff]
  intro e
  apply measurableSet_setOfPred.mp
  have heq : {h : History n | e ∈ early a h} = {h | e ∈ h.1 ∧ h.2 e < a} := by
    ext h
    exact Finset.mem_filter
  rw [heq]
  exact ((measurableSet_mem_finset e).preimage measurable_fst).inter
    (measurableSet_lt ((measurable_pi_apply e).comp measurable_snd) measurable_const)

lemma measurable_M1Y {n : ℕ} (M : EdgeSet n) (a : ℝ) : Measurable (M1Y M a) := by
  let f : EdgeSet n × EdgeSet n → EdgeSet n := fun z =>
    M.filter fun e => ∃ x y, e = s(x,y) ∧ x ∈ covered z.2 ∧ y ∈ univ \ covered z.1
  have hh := (measurable_of_finite f).comp (measurable_fst.prodMk (measurable_early (n:=n) a))
  convert! hh using 1

lemma measurable_MYY {n : ℕ} (M : EdgeSet n) : Measurable (MYY M) :=
  (measurable_of_finite (fun F : EdgeSet n => M.filter fun e => ∀ v, v ∈ e → v ∈ univ \ covered F)).comp measurable_fst

lemma integrable_history_counts {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (a b : ℝ) :
    Integrable (fun h : History n => ((M1Y M a h).card:ℝ)) (historyLaw G b) ∧
    Integrable (fun h : History n => ((MYY M h).card:ℝ)) (historyLaw G b) := by
  haveI : IsFiniteMeasure (historyLaw G b) := by
    haveI := arrival_probability G
    unfold historyLaw
    infer_instance
  exact ⟨integrable_finite_comp _ _ (measurable_M1Y M a) (fun F => (F.card:ℝ)),
    integrable_finite_comp _ _ (measurable_MYY M) (fun F => (F.card:ℝ))⟩

lemma integrable_history_counts_arrival {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (a b : ℝ) :
    Integrable (fun t => ((M1Y M a (history G b t)).card:ℝ)) (arrivalLaw G) ∧
    Integrable (fun t => ((MYY M (history G b t)).card:ℝ)) (arrivalLaw G) := by
  haveI := arrival_probability G
  exact ⟨integrable_finite_comp _ _ ((measurable_M1Y M a).comp (measurable_history G b)) (fun F => (F.card:ℝ)),
    integrable_finite_comp _ _ ((measurable_MYY M).comp (measurable_history G b)) (fun F => (F.card:ℝ))⟩

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical ProbabilityTheory
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma uniform_affine_map (l : ℝ) (hl : l < 1) :
    (volume.restrict (Set.Icc (0:ℝ) 1)).map (fun u => l+(1-l)*u) =
      (ENNReal.ofReal (1-l))⁻¹ • volume.restrict (Set.Ioo l 1) := by
  have hp : 0 < 1-l := sub_pos.mpr hl
  have hf : Measurable (fun u : ℝ => l+(1-l)*u) := measurable_const.add (measurable_const.mul measurable_id)
  have hfull : (volume : Measure ℝ).map (fun u => l+(1-l)*u) =
      (ENNReal.ofReal (1-l))⁻¹ • volume := by
    have he : (fun u : ℝ => l+(1-l)*u) = (fun v : ℝ => l+v) ∘ (fun u => (1-l)*u) := rfl
    rw [he,←Measure.map_map (measurable_const_add l) (measurable_const_mul (1-l)),
      Real.map_volume_mul_left (ne_of_gt hp),Measure.map_smul,map_add_left_eq_self]
    rw [abs_of_pos (inv_pos.mpr hp),ENNReal.ofReal_inv_of_pos hp]
  have hpre : (fun u : ℝ => l+(1-l)*u) ⁻¹' Set.Ioo l 1 = Set.Ioo 0 1 := by
    ext u
    simp only [Set.mem_preimage,Set.mem_Ioo]
    constructor
    · intro h
      constructor
      · nlinarith
      · nlinarith
    · intro h
      constructor <;> nlinarith
  rw [←Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ:=(volume : Measure ℝ)) (a:=0) (b:=1))]
  rw [←hpre,←Measure.restrict_map hf measurableSet_Ioo,hfull,Measure.restrict_smul]

lemma measurable_fold_min {Ω α : Type*} [MeasurableSpace Ω] (l : List α)
    (f : α → Ω → ℝ) (hf : ∀ x, Measurable (f x)) (g : Ω → ℝ) (hg : Measurable g) :
    Measurable (fun w => l.foldl (fun s x => min s (f x w)) (g w)) := by
  induction l generalizing g with
  | nil => exact hg
  | cons x l ih => exact ih _ (hg.min (hf x))

lemma measurable_matchTime {n : ℕ} (b : ℝ) (v : Fin n) : Measurable (fun h : History n => matchTime b h v) := by
  apply measurable_from_prod_countable_right
  intro F
  change Measurable (fun t : Edge n → ℝ => F.toList.foldl (fun s e => if v ∈ e then min s (t e) else s) b)
  have hfold (l : List (Edge n)) (g : (Edge n → ℝ) → ℝ) (hg : Measurable g) :
      Measurable (fun t => l.foldl (fun s e => if v ∈ e then min s (t e) else s) (g t)) := by
    induction l generalizing g with
    | nil => exact hg
    | cons e l ih =>
      apply ih
      by_cases hv : v ∈ e
      · simpa only [hv,↓reduceIte] using hg.min (measurable_pi_apply e)
      · simpa only [hv,↓reduceIte] using hg
  exact hfold _ _ measurable_const

lemma measurable_lowerTime {n : ℕ} (b : ℝ) (e : Edge n) : Measurable (fun h : History n => lowerTime b h e) :=
  measurable_fold_min _ (fun v h => matchTime b h v) (measurable_matchTime b) _ measurable_const

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def tailLaw (l : ℝ) : Measure ℝ := (ENNReal.ofReal (1-l))⁻¹ • volume.restrict (Set.Ioo l 1)

lemma tailLaw_probability (l : ℝ) (hl : l < 1) : IsProbabilityMeasure (tailLaw l) := by
  constructor
  simp only [tailLaw,Measure.smul_apply,Measure.restrict_apply_univ,Real.volume_Ioo,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hl))) ENNReal.ofReal_ne_top

lemma tailLaw_atomless (l : ℝ) : NullSingletonClass (tailLaw l) := by
  constructor
  intro x
  simp [tailLaw,Measure.smul_apply]

lemma tailLaw_map_uniform (l : ℝ) (hl : l < 1) :
    (volume.restrict (Set.Icc (0:ℝ) 1)).map (fun u => l+(1-l)*u) = tailLaw l := uniform_affine_map l hl

lemma tailLaw_late_mass (l b : ℝ) (hlb : l ≤ b) (hb : b < 1) :
    tailLaw l (Set.Ioi b) = ENNReal.ofReal ((1-b)/(1-l)) := by
  have hl : l < 1 := hlb.trans_lt hb
  have hset : Set.Ioi b ∩ Set.Ioo l 1 = Set.Ioo b 1 := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_Ioi,Set.mem_Ioo]
    constructor
    · exact fun hx => ⟨hx.1,hx.2.2⟩
    · exact fun hx => ⟨hx.1,lt_of_le_of_lt hlb hx.1,hx.2⟩
  rw [tailLaw,Measure.smul_apply,Measure.restrict_apply measurableSet_Ioi,hset,Real.volume_Ioo,smul_eq_mul,mul_comm]
  rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr hl)]
  rfl

lemma tailLaw_restrict_late (l b : ℝ) (hlb : l ≤ b) (hb : b < 1) :
    (tailLaw l).restrict (Set.Ioi b) = ENNReal.ofReal ((1-b)/(1-l)) • tailLaw b := by
  have hl : l < 1 := hlb.trans_lt hb
  have hset : Set.Ioi b ∩ Set.Ioo l 1 = Set.Ioo b 1 := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_Ioi,Set.mem_Ioo]
    constructor
    · exact fun hx => ⟨hx.1,hx.2.2⟩
    · exact fun hx => ⟨hx.1,lt_of_le_of_lt hlb hx.1,hx.2⟩
  unfold tailLaw
  rw [Measure.restrict_smul,Measure.restrict_restrict measurableSet_Ioi,hset,smul_smul]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr hl)]
  have hb0 : ENNReal.ofReal (1-b) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hb))
  rw [div_eq_mul_inv,mul_right_comm,ENNReal.mul_inv_cancel hb0 ENNReal.ofReal_ne_top,one_mul]

lemma tailLaw_early_mass (l b : ℝ) (hlb : l ≤ b) (hb : b < 1) :
    tailLaw l (Set.Iic b) = ENNReal.ofReal (1-(1-b)/(1-l)) := by
  have hl : l < 1 := hlb.trans_lt hb
  have hset : Set.Iic b ∩ Set.Ioo l 1 = Set.Ioc l b := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_Iic,Set.mem_Ioo,Set.mem_Ioc]
    constructor
    · exact fun hx => ⟨hx.2.1,hx.1⟩
    · exact fun hx => ⟨hx.2,hx.1,hx.2.trans_lt hb⟩
  have hr : 1-(1-b)/(1-l) = (b-l)/(1-l) := by
    apply (eq_div_iff (ne_of_gt (sub_pos.mpr hl))).mpr
    rw [sub_mul,one_mul,div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hl))]
    ring
  rw [hr,tailLaw,Measure.smul_apply,Measure.restrict_apply measurableSet_Iic,hset,Real.volume_Ioc,smul_eq_mul,mul_comm,
    ENNReal.ofReal_div_of_pos (sub_pos.mpr hl)]
  rfl

lemma tailLaw_restrict_late_closed (l b : ℝ) (hlb : l ≤ b) (hb : b < 1) :
    (tailLaw l).restrict (Set.Ici b) = ENNReal.ofReal ((1-b)/(1-l)) • tailLaw b := by
  haveI := tailLaw_atomless l
  rw [←Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ:=tailLaw l) (a:=b))]
  exact tailLaw_restrict_late l b hlb hb

lemma tailLaw_late_mass_closed (l b : ℝ) (hlb : l ≤ b) (hb : b < 1) :
    tailLaw l (Set.Ici b) = ENNReal.ofReal ((1-b)/(1-l)) := by
  haveI := tailLaw_atomless l
  rw [←measure_congr (Ioi_ae_eq_Ici (μ:=tailLaw l) (a:=b))]
  exact tailLaw_late_mass l b hlb hb

lemma tailLaw_early_mass_open (l b : ℝ) (hlb : l ≤ b) (hb : b < 1) :
    tailLaw l (Set.Iio b) = ENNReal.ofReal (1-(1-b)/(1-l)) := by
  haveI := tailLaw_atomless l
  rw [measure_congr (Iio_ae_eq_Iic (μ:=tailLaw l) (a:=b))]
  exact tailLaw_early_mass l b hlb hb

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma tailLaw_interval_real (l s t : ℝ) (hls : l ≤ s) (hst : s ≤ t) (ht : t < 1) :
    (tailLaw l).real (Set.Ioc s t) = (t-s)/(1-l) := by
  have hl : l < 1 := (hls.trans hst).trans_lt ht
  have hset : Set.Ioc s t ∩ Set.Ioo l 1 = Set.Ioc s t := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_Ioc,Set.mem_Ioo]
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx,lt_of_le_of_lt hls hx.1,hx.2.trans_lt ht⟩
  rw [Measure.real,tailLaw,Measure.smul_apply,Measure.restrict_apply measurableSet_Ioc,hset,Real.volume_Ioc,smul_eq_mul,
    ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_ofReal (sub_nonneg.mpr hst),
    ENNReal.toReal_ofReal (le_of_lt (sub_pos.mpr hl))]
  ring

lemma coordinate_tail_proportion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (e : ι)
    (F : (ι → ℝ) → ℝ) (hF : Integrable F (Measure.pi μ))
    (hignore : ∀ t x, F (Function.update t e x) = F t)
    (l s t : ℝ) (hμ : μ e = tailLaw l) (hls : l ≤ s) (hst : s ≤ t) (ht : t < 1) :
    (∫ v, (if s < v e ∧ v e ≤ t then F v else 0) ∂Measure.pi μ) =
      ((t-s)/(1-s)) * (∫ v, (if s < v e then F v else 0) ∂Measure.pi μ) := by
  have hs : s < 1 := hst.trans_lt ht
  have hl : l < 1 := hls.trans_lt hs
  have ha := coordinate_independent_integral μ e F hF hignore (Set.Ioc s t) measurableSet_Ioc
  have hb := coordinate_independent_integral μ e F hF hignore (Set.Ioi s) measurableSet_Ioi
  change (∫ v, (if v e ∈ Set.Ioc s t then F v else 0) ∂Measure.pi μ) =
    ((t-s)/(1-s)) * (∫ v, (if v e ∈ Set.Ioi s then F v else 0) ∂Measure.pi μ)
  have ha' : (∫ v, (if v e ∈ Set.Ioc s t then F v else 0) ∂Measure.pi μ) = (μ e).real (Set.Ioc s t)*(∫ v, F v ∂Measure.pi μ) := by
    convert! ha using 1
    apply integral_congr_ae
    filter_upwards [] with v
    simp only [Set.mem_Ioc]
  have hb' : (∫ v, (if v e ∈ Set.Ioi s then F v else 0) ∂Measure.pi μ) = (μ e).real (Set.Ioi s)*(∫ v, F v ∂Measure.pi μ) := by convert! hb using 1
  rw [ha',hb',hμ,tailLaw_interval_real l s t hls hst ht]
  have hr : (tailLaw l).real (Set.Ioi s) = (1-s)/(1-l) := by
    rw [Measure.real,tailLaw_late_mass l s hls hs,ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr hs.le) (sub_nonneg.mpr hl.le))]
  rw [hr]
  field_simp [ne_of_gt (sub_pos.mpr hs),ne_of_gt (sub_pos.mpr hl)]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma clock_cell_update {n : ℕ} (E : EdgeSet n) (F : EdgeSet n) (e : Edge n)
    (he : e ∈ E) (hf : free F e) (s : ℝ) (hs : s < 1) (v : Edge n → ℝ) (hv : Set.InjOn v E) :
    clockState E v s = F ↔ s < v e ∧ clockState E (Function.update v e 1) s = F := by
  constructor
  · intro h
    have hlate := clockState_free_late E v s e he (h.symm ▸ hf)
    exact ⟨hlate,(clockState_update_after E v e s 1 hlate hs hv).trans h⟩
  · rintro ⟨h,hF⟩
    rwa [clockState_update_after E v e s 1 h hs hv] at hF

lemma clock_cell_erosion {n : ℕ} (E F : EdgeSet n) (e : Edge n) (he : e ∈ E) (hf : free F e)
    (μ : Edge n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hreg : ∀ᵐ v ∂Measure.pi μ, Set.InjOn v E)
    (l s t : ℝ) (hμ : μ e = tailLaw l) (hls : l ≤ s) (hst : s ≤ t) (ht : t < 1) :
    (∫ v, (if clockState E v s = F ∧ v e ≤ t then (1:ℝ) else 0) ∂Measure.pi μ) =
      ((t-s)/(1-s)) * (∫ v, (if clockState E v s = F then (1:ℝ) else 0) ∂Measure.pi μ) := by
  let f : (Edge n → ℝ) → ℝ := fun v => if clockState E (Function.update v e 1) s = F then 1 else 0
  have hi : Integrable f (Measure.pi μ) := integrable_clockCell E s F e _
  have hignore : ∀ v x, f (Function.update v e x) = f v := by intro v x; simp [f,Function.update_idem]
  have h1 : (∫ v, (if clockState E v s = F ∧ v e ≤ t then (1:ℝ) else 0) ∂Measure.pi μ) =
      ∫ v, (if s < v e ∧ v e ≤ t then f v else 0) ∂Measure.pi μ := by
    apply integral_congr_ae
    filter_upwards [hreg] with v hv
    have heq := clock_cell_update E F e he hf s (hst.trans_lt ht) v hv
    simp only [heq,f]
    split_ifs <;> simp_all
  have h2 : (∫ v, (if clockState E v s = F then (1:ℝ) else 0) ∂Measure.pi μ) =
      ∫ v, (if s < v e then f v else 0) ∂Measure.pi μ := by
    apply integral_congr_ae
    filter_upwards [hreg] with v hv
    have heq := clock_cell_update E F e he hf s (hst.trans_lt ht) v hv
    simp only [heq,f]
    split_ifs <;> simp_all
  rw [h1,h2]
  exact coordinate_tail_proportion μ e f hi hignore l s t hμ hls hst ht

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def holeSet {n : ℕ} (z : Fin n) (F H : EdgeSet n) : Finset (Fin n) :=
  insert z (covered H) \ covered F

lemma holeSet_card {n : ℕ} (z : Fin n) (F H : EdgeSet n)
    (hz : z ∉ covered H) (hc : CoverCoupling z (covered F) (covered H)) :
    (holeSet z F H).card ≤ 1 := by
  rcases hc with h | ⟨u,⟨h,hu⟩ | ⟨h,hu⟩⟩
  · have heq : holeSet z F H = {z} := by ext v; simp only [holeSet,h,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]; grind
    rw [heq]; simp
  · have heq : holeSet z F H = ∅ := by ext v; simp [holeSet,h]; tauto
    rw [heq]; simp
  · have hsub : holeSet z F H ⊆ {u} := by
      intro v hv
      simp only [holeSet,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase,not_or,not_and] at hv
      simp only [Finset.mem_singleton]
      grind
    exact (Finset.card_le_card hsub).trans (by simp)

lemma matching_new_edge_free {n : ℕ} (F M : EdgeSet n) (hM : IsMatching M) (hFM : F ⊆ M)
    (e : Edge n) (he : e ∈ M) (hne : e ∉ F) : free F e := by
  intro v hve hvF
  obtain ⟨f,hf,hvf⟩ : ∃ f ∈ F, v ∈ f := by simpa [covered] using hvF
  exact hM.2 e he f (hFM hf) (fun hef => hne (hef.symm ▸ hf)) v hve hvf

lemma new_match_from_hole {n : ℕ} (z w : Fin n) (F M H : EdgeSet n)
    (hM : IsMatching M) (hFM : F ⊆ M) (hwF : w ∉ covered F) (hwH : w ∉ covered H)
    (hwM : w ∈ covered M) (hwz : w ≠ z)
    (hblock : ∀ e ∈ M, z ∉ e → ¬ free H e) :
    ∃ u ∈ holeSet z F H, s(w,u) ∈ M := by
  obtain ⟨e,he,hwe⟩ : ∃ e ∈ M, w ∈ e := by simpa [covered] using hwM
  obtain ⟨u,heu⟩ := Sym2.mem_iff_exists.mp hwe
  subst e
  have hne : s(w,u) ∉ F := by
    intro hf
    exact hwF (by simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨s(w,u),hf,by simp⟩)
  have hfree := matching_new_edge_free F M hM hFM s(w,u) he hne
  have huF : u ∉ covered F := hfree u (by simp)
  refine ⟨u,Finset.mem_sdiff.mpr ⟨?_,huF⟩,he⟩
  by_cases hu : u ∈ insert z (covered H)
  · exact hu
  · have huh : u ≠ z ∧ u ∉ covered H := by simpa only [Finset.mem_insert,not_or] using hu
    have huz := huh.1
    have huH := huh.2
    have hze : z ∉ s(w,u) := by simp [Sym2.mem_iff,hwz.symm,huz.symm]
    have hfH : free H s(w,u) := by
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hwH
      · exact huH
    exact (hblock _ he hze hfH).elim

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma mem_clockPrefix {n : ℕ} (E : EdgeSet n) (t : Edge n → ℝ) (s : ℝ) (e : Edge n) :
    e ∈ clockPrefix E t s ↔ e ∈ E ∧ t e ≤ s := by
  have hm := (mem_permLists E _).mp (orderFor_mem E (fun e => t e.val))
  simp only [clockPrefix,List.mem_filter,decide_eq_true_eq]
  rw [←List.mem_toFinset,hm.2]

lemma clockState_subset {n : ℕ} (E : EdgeSet n) (t : Edge n → ℝ) (s : ℝ) : clockState E t s ⊆ E := by
  intro e he
  exact ((mem_clockPrefix E t s e).mp (List.mem_toFinset.mp (greedy_seen _ he))).1

lemma clockState_matching {n : ℕ} (E : EdgeSet n) (hE : ∀ e ∈ E, ¬e.IsDiag) (t : Edge n → ℝ) (s : ℝ) :
    IsMatching (clockState E t s) := by
  apply greedy_fold_matching _ ∅ (by simp [IsMatching])
  intro e he
  exact hE e ((mem_clockPrefix E t s e).mp he).1

lemma clockState_mono {n : ℕ} (E : EdgeSet n) (t : Edge n → ℝ) (s u : ℝ) (hsu : s ≤ u) :
    clockState E t s ⊆ clockState E t u := by
  let l := orderFor E (fun e => t e.val)
  have hp := filter_initial_lower (l.filter (fun e => t e ≤ u)) (fun e f => t e ≤ t f)
    ((orderFor_pairwise E t).filter _) (fun e => t e ≤ s) (fun _ _ h h' => h.trans h')
  have hf : (l.filter (fun e => t e ≤ u)).filter (fun e => t e ≤ s) = l.filter (fun e => t e ≤ s) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro e he
    by_cases h : t e ≤ s
    · simp [h,h.trans hsu]
    · simp [h]
  rw [hf] at hp
  exact greedy_prefix_mono hp

lemma clockPrefix_delete {n : ℕ} (E : EdgeSet n) (t : Edge n → ℝ) (s : ℝ) (z : Fin n)
    (ht : Set.InjOn t E) :
    clockPrefix (E.filter (fun e => z ∉ e)) t s = (clockPrefix E t s).filter (fun e => z ∉ e) := by
  unfold clockPrefix
  rw [orderFor_filter_sorted E t (fun e => z ∉ e) (ht.mono (Finset.filter_subset _ _))]
  rw [List.filter_filter,List.filter_filter]
  apply List.filter_congr
  intro e he
  simp only [Bool.and_comm]

lemma clockState_coupling {n : ℕ} (E : EdgeSet n) (hE : ∀ e ∈ E, ¬e.IsDiag)
    (t : Edge n → ℝ) (s : ℝ) (z : Fin n) (ht : Set.InjOn t E) :
    CoverCoupling z (covered (clockState E t s)) (covered (clockState (E.filter (fun e => z ∉ e)) t s)) := by
  have hc := greedy_coupling z (clockPrefix E t s) (fun e he => hE e ((mem_clockPrefix E t s e).mp he).1)
  rwa [←clockPrefix_delete E t s z ht] at hc

lemma clockState_new_hole {n : ℕ} (E : EdgeSet n) (hE : ∀ e ∈ E, ¬e.IsDiag)
    (t : Edge n → ℝ) (s u : ℝ) (hsu : s ≤ u) (z w : Fin n) (hwz : w ≠ z)
    (hwF : w ∉ covered (clockState E t s))
    (hwH : w ∉ covered (clockState (E.filter (fun e => z ∉ e)) t u))
    (hwM : w ∈ covered (clockState E t u))
    (hstable : clockState (E.filter (fun e => z ∉ e)) t s = clockState (E.filter (fun e => z ∉ e)) t u) :
    ∃ a ∈ holeSet z (clockState E t s) (clockState (E.filter (fun e => z ∉ e)) t s),
      s(w,a) ∈ clockState E t u := by
  rw [hstable]
  apply new_match_from_hole z w _ _ _ (clockState_matching E hE t u) (clockState_mono E t s u hsu) hwF hwH hwM hwz
  intro e he hze
  have hm := (mem_clockPrefix E t u e).mp (List.mem_toFinset.mp (greedy_seen _ he))
  apply greedy_blocks_seen
  exact (mem_clockPrefix _ t u e).mpr ⟨Finset.mem_filter.mpr ⟨hm.1,hze⟩,hm.2⟩

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma integrable_clock_pair {n : ℕ} (E : EdgeSet n) (s t : ℝ)
    (f : EdgeSet n × EdgeSet n → ℝ) (μ : Measure (Edge n → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun v => f (clockState E v s,clockState E v t)) μ :=
  integrable_finite_comp μ _ ((measurable_clockState E s).prodMk (measurable_clockState E t)) f

lemma clock_survival_cell {n : ℕ} (E D F : EdgeSet n)
    (z w : Fin n) (hwz : w ≠ z) (hwD : w ∉ covered D) (hwF : w ∉ covered F)
    (hcard : (holeSet z F D).card ≤ 1)
    (μ : Edge n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s t : ℝ) (hst : s ≤ t) (ht : t < 1)
    (hreg : ∀ᵐ v ∂Measure.pi μ, Set.InjOn v E)
    (M : (Edge n → ℝ) → EdgeSet n) (hM : Measurable M)
    (hMgood : ∀ᵐ v ∂Measure.pi μ, IsMatching (M v) ∧ clockState E v s ⊆ M v ∧
      ∀ e ∈ M v, e ∈ E ∧ v e ≤ t ∧ (z ∉ e → ¬ free D e))
    (hclock : ∀ a ∈ holeSet z F D, s(w,a) ∈ E → ∃ l, l ≤ s ∧ μ s(w,a) = tailLaw l) :
    (∫ v, (if clockState E v s = F ∧ w ∉ covered (M v) then (1:ℝ) else 0) ∂Measure.pi μ) ≥
      (1-(t-s)/(1-s)) * (∫ v, (if clockState E v s = F then (1:ℝ) else 0) ∂Measure.pi μ) := by
  let r := (t-s)/(1-s)
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr (hst.trans ht.le))
  have hstart : Integrable (fun v => if clockState E v s = F then (1:ℝ) else 0) (Measure.pi μ) :=
    integrable_finite_comp _ _ (measurable_clockState E s) (fun A => if A=F then (1:ℝ) else 0)
  have hend : Integrable (fun v => if clockState E v s = F ∧ w ∉ covered (M v) then (1:ℝ) else 0) (Measure.pi μ) :=
    integrable_finite_comp _ _ ((measurable_clockState E s).prodMk hM) (fun A => if A.1=F ∧ w ∉ covered A.2 then (1:ℝ) else 0)
  have hnew : ∀ᵐ v ∂Measure.pi μ, clockState E v s = F → w ∈ covered (M v) →
      ∃ a ∈ holeSet z F D, s(w,a) ∈ M v := by
    filter_upwards [hMgood] with v hv hF hw
    exact new_match_from_hole z w F (M v) D hv.1 (hF ▸ hv.2.1) hwF hwD hw hwz
      (fun e he hz => (hv.2.2 e he).2.2 hz)
  by_cases hex : ∃ a ∈ holeSet z F D, s(w,a) ∈ E
  · obtain ⟨a,ha,haE⟩ := hex
    obtain ⟨l,hls,hμ⟩ := hclock a ha haE
    have haF : a ∉ covered F := (Finset.mem_sdiff.mp ha).2
    have hfree : free F s(w,a) := by
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hwF
      · exact haF
    have hbad : Integrable (fun v => if clockState E v s=F ∧ v s(w,a) ≤ t then (1:ℝ) else 0) (Measure.pi μ) := by
      have hm : MeasurableSet {v : Edge n → ℝ | v s(w,a) ≤ t} := measurableSet_le (measurable_pi_apply _) measurable_const
      convert! hstart.indicator hm using 1
      apply funext
      intro v
      by_cases h1 : clockState E v s = F <;> by_cases h2 : v s(w,a) ≤ t <;> simp [Set.indicator_apply,h1,h2]
    have hineq := integral_mono_ae (hstart.sub hbad) hend (by
      filter_upwards [hnew,hMgood] with v hv hvM
      by_cases hF : clockState E v s=F
      · by_cases hw : w ∈ covered (M v)
        · obtain ⟨a',ha',he⟩ := hv hF hw
          have heq : a'=a := Finset.card_le_one.mp hcard a' ha' a ha
          subst a'
          have htime := (hvM.2.2 _ he).2.1
          simp [hF,hw,htime]
        · by_cases htime : v s(w,a) ≤ t <;> simp [hF,hw,htime]
      · simp [hF])
    change (∫ v, ((if clockState E v s=F then (1:ℝ) else 0) - (if clockState E v s=F ∧ v s(w,a) ≤ t then (1:ℝ) else 0)) ∂Measure.pi μ) ≤ _ at hineq
    rw [integral_sub hstart hbad,clock_cell_erosion E F s(w,a) haE hfree μ hreg l s t hμ hls hst ht] at hineq
    dsimp [r] at *
    nlinarith
  · have heq : (∫ v, (if clockState E v s = F ∧ w ∉ covered (M v) then (1:ℝ) else 0) ∂Measure.pi μ) =
        ∫ v, (if clockState E v s = F then (1:ℝ) else 0) ∂Measure.pi μ := by
      apply integral_congr_ae
      filter_upwards [hnew,hMgood] with v hv hvM
      by_cases hF : clockState E v s=F
      · have hw : w ∉ covered (M v) := by
          intro hw
          obtain ⟨a,ha,he⟩ := hv hF hw
          exact hex ⟨a,ha,(hvM.2.2 _ he).1⟩
        simp [hF,hw]
      · simp [hF]
    rw [heq]
    have hnonneg : 0 ≤ ∫ v, (if clockState E v s = F then (1:ℝ) else 0) ∂Measure.pi μ := integral_nonneg (fun v => by split_ifs <;> norm_num)
    change _ ≥ (1-r)*_
    nlinarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma sum_state_flags {α β : Type*} [DecidableEq β] (A : Finset β) (X : α → β) (Q : α → Prop)
    [DecidablePred Q] (v : α) :
    (∑ F ∈ A, (if X v = F ∧ Q v then (1:ℝ) else 0)) = if X v ∈ A ∧ Q v then 1 else 0 := by
  by_cases hQ : Q v <;> simp [hQ,eq_comm]

lemma clock_survival_step {n : ℕ} (E D : EdgeSet n) (hE : ∀ e ∈ E, ¬e.IsDiag)
    (z w : Fin n) (hwz : w ≠ z) (hwD : w ∉ covered D) (hzD : z ∉ covered D)
    (μ : Edge n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s t : ℝ) (hst : s ≤ t) (ht : t < 1)
    (hreg : ∀ᵐ v ∂Measure.pi μ, Set.InjOn v E)
    (hleft : ∀ᵐ v ∂Measure.pi μ, clockState (E.filter (fun e => z ∉ e)) v s = D)
    (M : (Edge n → ℝ) → EdgeSet n) (hM : Measurable M)
    (hMgood : ∀ᵐ v ∂Measure.pi μ, IsMatching (M v) ∧ clockState E v s ⊆ M v ∧
      ∀ e ∈ M v, e ∈ E ∧ v e ≤ t ∧ (z ∉ e → ¬ free D e))
    (hclock : ∀ a ∈ insert z (covered D), s(w,a) ∈ E → ∃ l, l ≤ s ∧ μ s(w,a) = tailLaw l) :
    (∫ v, (if w ∉ covered (M v) then (1:ℝ) else 0) ∂Measure.pi μ) ≥
      (1-(t-s)/(1-s)) * (∫ v, (if w ∉ covered (clockState E v s) then (1:ℝ) else 0) ∂Measure.pi μ) := by
  let A : Finset (EdgeSet n) := Finset.univ.filter (fun F => w ∉ covered F ∧ (holeSet z F D).card ≤ 1)
  have hA : ∀ᵐ v ∂Measure.pi μ, w ∉ covered (clockState E v s) → clockState E v s ∈ A := by
    filter_upwards [hreg,hleft] with v hv hD hw
    have hc := clockState_coupling E hE v s z hv
    rw [hD] at hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw,holeSet_card z _ D hzD hc⟩
  have hstart (F : EdgeSet n) : Integrable (fun v => if clockState E v s=F then (1:ℝ) else 0) (Measure.pi μ) :=
    integrable_finite_comp _ _ (measurable_clockState E s) (fun X => if X=F then (1:ℝ) else 0)
  have hend (F : EdgeSet n) : Integrable (fun v => if clockState E v s=F ∧ w ∉ covered (M v) then (1:ℝ) else 0) (Measure.pi μ) :=
    integrable_finite_comp _ _ ((measurable_clockState E s).prodMk hM) (fun X => if X.1=F ∧ w ∉ covered X.2 then (1:ℝ) else 0)
  have hsume : (∑ F ∈ A, ∫ v, (if clockState E v s=F ∧ w ∉ covered (M v) then (1:ℝ) else 0) ∂Measure.pi μ) =
      ∫ v, (if w ∉ covered (M v) then (1:ℝ) else 0) ∂Measure.pi μ := by
    rw [←integral_finsetSum A (fun F hF => hend F)]
    apply integral_congr_ae
    filter_upwards [hA,hMgood] with v hv hvM
    by_cases hw : w ∉ covered (M v)
    · have hwS : w ∉ covered (clockState E v s) := fun h => hw (covered_mono hvM.2.1 h)
      simp [hw,hv hwS,eq_comm]
    · simp [hw]
  have hsums : (∑ F ∈ A, ∫ v, (if clockState E v s=F then (1:ℝ) else 0) ∂Measure.pi μ) =
      ∫ v, (if w ∉ covered (clockState E v s) then (1:ℝ) else 0) ∂Measure.pi μ := by
    rw [←integral_finsetSum A (fun F hF => hstart F)]
    apply integral_congr_ae
    filter_upwards [hA] with v hv
    have heq := sum_state_flags A (fun v => clockState E v s) (fun _ => True) v
    simp only [and_true,ite_true] at heq
    rw [heq]
    by_cases hw : w ∉ covered (clockState E v s)
    · simp [hw,hv hw]
    · have hn : clockState E v s ∉ A := fun h => hw (Finset.mem_filter.mp h).2.1
      simp [hw,hn]
  have hsum := Finset.sum_le_sum (s:=A) (fun F hF => by
    have hh := (Finset.mem_filter.mp hF).2
    exact clock_survival_cell E D F z w hwz hwD hh.1 hh.2 μ s t hst ht hreg M hM hMgood
      (fun a ha he => hclock a (Finset.mem_sdiff.mp ha).1 he))
  rw [hsume,←Finset.mul_sum,hsums] at hsum
  exact hsum

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def clockOpenPrefix {n : ℕ} (E : EdgeSet n) (v : Edge n → ℝ) (t : ℝ) : List (Edge n) :=
  (orderFor E (fun e => v e.val)).filter (fun e => v e < t)

def clockOpenState {n : ℕ} (E : EdgeSet n) (v : Edge n → ℝ) (t : ℝ) : EdgeSet n :=
  greedy (clockOpenPrefix E v t)

lemma clockOpenState_filter {n : ℕ} (E : EdgeSet n) (v : Edge n → ℝ) (t : ℝ) :
    clockOpenState E v t = (clockState E v t).filter (fun e => v e < t) := by
  have hh := greedy_filter_time ((orderFor E (fun e => v e.val)).filter (fun e => v e ≤ t)) v
    ((orderFor_pairwise E v).filter _) t
  have hf : ((orderFor E (fun e => v e.val)).filter (fun e => v e ≤ t)).filter (fun e => v e < t) =
      clockOpenPrefix E v t := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro e he
    by_cases h : v e < t
    · simp [h,h.le]
    · simp [h]
  rw [hf] at hh
  exact hh

lemma measurable_clockOpenState {n : ℕ} (E : EdgeSet n) (t : ℝ) :
    Measurable (fun v : Edge n → ℝ => clockOpenState E v t) := by
  have hm : Measurable (fun v : Edge n → ℝ => E.filter (fun e => v e < t)) := by
    rw [measurable_finset_iff]
    intro e
    apply measurableSet_setOfPred.mp
    by_cases he : e ∈ E
    · simpa only [Finset.mem_filter,he,true_and] using measurableSet_lt (measurable_pi_apply e) (measurable_const : Measurable (fun _ : Edge n → ℝ => t))
    · simp only [Finset.mem_filter,he,false_and]
      exact (MeasurableSet.empty : MeasurableSet (∅ : Set (Edge n → ℝ)))
  have h := (measurable_of_finite (fun p : EdgeSet n × EdgeSet n => p.1 ∩ p.2)).comp
    ((measurable_clockState E t).prodMk hm)
  convert! h using 1
  funext v
  change clockOpenState E v t = clockState E v t ∩ E.filter (fun e => v e < t)
  rw [clockOpenState_filter]
  ext e
  simp only [Finset.mem_filter,Finset.mem_inter]
  have he := clockState_subset E v t
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨h1,he h1,h2⟩
  · rintro ⟨h1,h2,h3⟩
    exact ⟨h1,h3⟩

lemma mem_clockOpenPrefix {n : ℕ} (E : EdgeSet n) (v : Edge n → ℝ) (t : ℝ) (e : Edge n) :
    e ∈ clockOpenPrefix E v t ↔ e ∈ E ∧ v e < t := by
  have hm := (mem_permLists E _).mp (orderFor_mem E (fun e => v e.val))
  simp only [clockOpenPrefix,List.mem_filter,decide_eq_true_eq]
  rw [←List.mem_toFinset,hm.2]

lemma clockState_subset_open {n : ℕ} (E : EdgeSet n) (v : Edge n → ℝ) (s t : ℝ) (hst : s < t) :
    clockState E v s ⊆ clockOpenState E v t := by
  have hc := greedy_filter_le_time (orderFor E (fun e => v e.val)) v (orderFor_pairwise E v) s
  have ho := greedy_filter_time (orderFor E (fun e => v e.val)) v (orderFor_pairwise E v) t
  change greedy ((orderFor E (fun e => v e.val)).filter (fun e => v e ≤ s)) ⊆ greedy ((orderFor E (fun e => v e.val)).filter (fun e => v e < t))
  rw [hc,ho]
  intro e he
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2.trans_lt hst⟩

lemma clockOpen_good {n : ℕ} (E D : EdgeSet n) (hE : ∀ e ∈ E, ¬e.IsDiag)
    (v : Edge n → ℝ) (s t : ℝ) (hst : s < t) (z : Fin n)
    (ht : Set.InjOn v E) (hD : clockOpenState (E.filter (fun e => z ∉ e)) v t = D) :
    IsMatching (clockOpenState E v t) ∧ clockState E v s ⊆ clockOpenState E v t ∧
      ∀ e ∈ clockOpenState E v t, e ∈ E ∧ v e ≤ t ∧ (z ∉ e → ¬free D e) := by
  refine ⟨?_,clockState_subset_open E v s t hst,?_⟩
  · apply greedy_fold_matching _ ∅ (by simp [IsMatching])
    intro e he
    exact hE e ((mem_clockOpenPrefix E v t e).mp he).1
  · intro e he
    have hm := (mem_clockOpenPrefix E v t e).mp (List.mem_toFinset.mp (greedy_seen _ he))
    refine ⟨hm.1,hm.2.le,?_⟩
    intro hze
    rw [←hD]
    apply greedy_blocks_seen
    exact (mem_clockOpenPrefix _ v t e).mpr ⟨Finset.mem_filter.mpr ⟨hm.1,hze⟩,hm.2⟩

lemma clockOpen_closed_vertex {n : ℕ} (E : EdgeSet n) (v : Edge n → ℝ) (t : ℝ) (w : Fin n)
    (ht : ∀ e ∈ E, v e = t → w ∉ e) :
    w ∈ covered (clockOpenState E v t) ↔ w ∈ covered (clockState E v t) := by
  rw [clockOpenState_filter]
  constructor
  · intro hw
    exact covered_mono (show (clockState E v t).filter (fun e => v e < t) ⊆ clockState E v t from Finset.filter_subset _ _) hw
  · intro hw
    obtain ⟨e,he,hwe⟩ : ∃ e ∈ clockState E v t, w ∈ e := by simpa [covered] using hw
    have hm := (mem_clockPrefix E v t e).mp (List.mem_toFinset.mp (greedy_seen _ he))
    have hlt : v e < t := lt_of_le_of_ne hm.2 (fun heq => ht e hm.1 heq hwe)
    simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨e,⟨he,hlt⟩,hwe⟩

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma greedy_fold_remove_unselected {n : ℕ} (l : List (Edge n)) (F : EdgeSet n) (e : Edge n)
    (he : e ∉ l.foldl (fun F f => if free F f then insert f F else F) F) :
    l.foldl (fun F f => if free F f then insert f F else F) F =
      (l.filter (fun f => f ≠ e)).foldl (fun F f => if free F f then insert f F else F) F := by
  induction l generalizing F with
  | nil => rfl
  | cons f l ih =>
    by_cases hfe : f = e
    · subst f
      have hf : ¬ free F e := by
        intro hf
        apply he
        simp only [List.foldl_cons,hf,↓reduceIte]
        exact greedy_fold_mono l (insert e F) (Finset.mem_insert_self _ _)
      simp only [List.foldl_cons,hf,↓reduceIte] at he ⊢
      simpa only [List.filter_cons,ne_self_iff_false,decide_false,Bool.false_eq_true,↓reduceIte] using ih F he
    · have he' : e ∉ l.foldl (fun F f => if free F f then insert f F else F) (if free F f then insert f F else F) := he
      have hh := ih _ he'
      simpa [List.filter_cons,hfe] using hh

lemma greedy_remove_unselected {n : ℕ} (l : List (Edge n)) (e : Edge n) (he : e ∉ greedy l) :
    greedy l = greedy (l.filter (fun f => f ≠ e)) :=
  greedy_fold_remove_unselected l ∅ e he

lemma deleted_prefix_eq {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (hT : Set.InjOn T G.edgeSet) (e : Edge n) (b : ℝ) :
    ((((orderedEdges G (fun f => T f.val)).filter (fun f => T f.val < b)).map Subtype.val).filter (fun f => f ≠ e)) =
      (((orderedEdges (G.deleteEdges {e}) (fun f => T f.val)).filter (fun f => T f.val < b)).map Subtype.val) := by
  let lG := (((orderedEdges G (fun f => T f.val)).filter (fun f => T f.val < b)).map Subtype.val).filter (fun f => f ≠ e)
  let lH := ((orderedEdges (G.deleteEdges {e}) (fun f => T f.val)).filter (fun f => T f.val < b)).map Subtype.val
  have hnG : lG.Nodup := (((orderedEdges_nodup G _).filter _).map Subtype.val_injective).filter _
  have hnH : lH.Nodup := ((orderedEdges_nodup (G.deleteEdges {e}) _).filter _).map Subtype.val_injective
  have hmem (f : Edge n) : f ∈ lG ↔ f ∈ lH := by
    dsimp only [lG,lH]
    rw [List.mem_filter,prefix_mem,prefix_mem,SimpleGraph.edgeSet_deleteEdges]
    simp only [decide_eq_true_eq,Set.mem_sdiff,Set.mem_singleton_iff]
    tauto
  have hp : lG.Perm lH := (List.perm_ext_iff_of_nodup hnG hnH).mpr hmem
  apply List.Perm.eq_of_pairwise (le:=fun f g => T f ≤ T g) ?_
    ((prefix_pairwise G T b).filter _) (prefix_pairwise (G.deleteEdges {e}) T b) hp
  intro f g hf hg hfg hgf
  apply hT
  · exact ((prefix_mem G T b f).mp (List.mem_filter.mp hf).1).1
  · have hh := (prefix_mem (G.deleteEdges {e}) T b g).mp hg
    have hgg := hh.1
    rw [SimpleGraph.edgeSet_deleteEdges] at hgg
    exact hgg.1
  · exact le_antisymm hfg hgf

lemma shadowAt_delete_unselected {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (hT : Set.InjOn T G.edgeSet) (e : Edge n) (b : ℝ)
    (he : e ∉ shadowAt G (fun f => T f.val) b) :
    shadowAt G (fun f => T f.val) b = shadowAt (G.deleteEdges {e}) (fun f => T f.val) b := by
  unfold shadowAt at he ⊢
  rw [greedy_remove_unselected _ e he,deleted_prefix_eq G T hT e b]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical ProbabilityTheory
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

def residualSample {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (h : History n) (u : Times G) : Times G :=
  fun e => if e.val ∈ h.accepted then h.time e.val
    else lowerTime b h e.val + (1-lowerTime b h e.val)*u e

lemma measurable_residualSample {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) :
    Measurable (fun z : History n × Times G => residualSample G b z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro e
  have hacc : MeasurableSet {z : History n × Times G | e.val ∈ z.1.accepted} :=
    (measurableSet_mem_finset e.val).preimage (measurable_fst.comp measurable_fst)
  have ht : Measurable (fun z : History n × Times G => z.1.time e.val) :=
    (measurable_pi_apply e.val).comp (measurable_snd.comp measurable_fst)
  have hl : Measurable (fun z : History n × Times G => lowerTime b z.1 e.val) :=
    (measurable_lowerTime b e.val).comp measurable_fst
  exact ht.ite hacc (hl.add ((measurable_const.sub hl).mul ((measurable_pi_apply e).comp measurable_snd)))

lemma residual_sample_map {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : b < 1) (h : History n) :
    (arrivalLaw G).map (residualSample G b h) = residualLaw G b h := by
  let f : G.edgeSet → ℝ → ℝ := fun e u =>
    if e.val ∈ h.accepted then h.time e.val else lowerTime b h e.val + (1-lowerTime b h e.val)*u
  have hf (e : G.edgeSet) : Measurable (f e) := by
    dsimp only [f]
    split_ifs
    · exact measurable_const
    · exact measurable_const.add (measurable_const.mul measurable_id)
  have hmap (e : G.edgeSet) :
      (volume.restrict (Set.Icc (0:ℝ) 1)).map (f e) =
      if e.val ∈ h.accepted then Measure.dirac (h.time e.val)
      else (ENNReal.ofReal (1-lowerTime b h e.val))⁻¹ • volume.restrict (Set.Ioo (lowerTime b h e.val) 1) := by
    dsimp only [f]
    by_cases he : e.val ∈ h.accepted
    · simp only [he,↓reduceIte]
      rw [Measure.map_const]
      norm_num [Measure.restrict_apply_univ,Real.volume_Icc]
    · simp only [he,↓reduceIte]
      exact uniform_affine_map _ ((lowerTime_le b h e.val).trans_lt hb)
  haveI (e : G.edgeSet) : IsFiniteMeasure ((volume.restrict (Set.Icc (0:ℝ) 1)).map (f e)) := inferInstance
  have hh := Measure.pi_map_pi (fun e => (hf e).aemeasurable (μ:=volume.restrict (Set.Icc (0:ℝ) 1)))
  change (Measure.pi (fun _ : G.edgeSet => volume.restrict (Set.Icc (0:ℝ) 1))).map (fun u e => f e (u e)) = _ at hh
  convert! hh.trans (congrArg Measure.pi (funext hmap)) using 1

lemma measurable_residualLaw {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : b < 1)
    (A : Set (Times G)) (hA : MeasurableSet A) :
    Measurable (fun h : History n => residualLaw G b h A) := by
  haveI := arrival_probability G
  have hm := measurable_measure_prodMk_left (ν:=arrivalLaw G) ((measurable_residualSample G b) hA)
  convert! hm using 1
  funext h
  rw [←residual_sample_map G b hb h,Measure.map_apply]
  · rfl
  · exact (measurable_residualSample G b).comp measurable_prodMk_left
  · exact hA

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma le_fold_min_iff {α : Type*} (l : List α) (f : α → ℝ) (u b : ℝ) :
    u ≤ l.foldl (fun s x => min s (f x)) b ↔ u ≤ b ∧ ∀ x ∈ l, u ≤ f x := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons,ih,le_min_iff,List.forall_mem_cons]; tauto

lemma le_fold_match_iff {α : Type*} (l : List α) (f : α → ℝ) (P : α → Prop)
    [DecidablePred P] (u b : ℝ) :
    u ≤ l.foldl (fun s x => if P x then min s (f x) else s) b ↔
      u ≤ b ∧ ∀ x ∈ l, P x → u ≤ f x := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih =>
    by_cases hx : P x
    · simp only [List.foldl_cons,hx,↓reduceIte,ih,le_min_iff,List.forall_mem_cons,true_implies]; tauto
    · simp only [List.foldl_cons,hx,↓reduceIte,ih,List.forall_mem_cons,false_implies,true_and]

lemma le_matchTime_iff {n : ℕ} (u b : ℝ) (h : History n) (v : Fin n) :
    u ≤ matchTime b h v ↔ u ≤ b ∧ ∀ f ∈ h.accepted, v ∈ f → u ≤ h.time f := by
  rw [matchTime,le_fold_match_iff]
  simp only [Finset.mem_toList]

lemma le_lowerTime_iff {n : ℕ} (u b : ℝ) (h : History n) (e : Edge n) :
    u ≤ lowerTime b h e ↔ u ≤ b ∧ ∀ v, v ∈ e → ∀ f ∈ h.accepted, v ∈ f → u ≤ h.time f := by
  rw [lowerTime,le_fold_min_iff]
  simp only [Finset.mem_toList,covered_singleton,Sym2.mem_toFinset,le_matchTime_iff]
  constructor
  · rintro ⟨hub,hv⟩
    exact ⟨hub,fun v hve => (hv v hve).2⟩
  · rintro ⟨hub,hv⟩
    exact ⟨hub,fun v hve => ⟨hub,hv v hve⟩⟩

lemma free_early_iff_lower {n : ℕ} (u b : ℝ) (hub : u ≤ b) (h : History n) (e : Edge n) :
    free (early u h) e ↔ u ≤ lowerTime b h e := by
  rw [le_lowerTime_iff]
  constructor
  · intro hf
    refine ⟨hub,?_⟩
    intro v hve f hfF hvf
    by_contra hn
    have hfe : f ∈ early u h := Finset.mem_filter.mpr ⟨hfF,lt_of_not_ge hn⟩
    exact hf v hve (Finset.mem_filter.mpr ⟨Finset.mem_univ v,⟨f,hfe,hvf⟩⟩)
  · rintro ⟨_,hf⟩ v hve hv
    obtain ⟨f,hfF,hvf⟩ := (Finset.mem_filter.mp hv).2
    have hh := Finset.mem_filter.mp hfF
    exact (not_lt_of_ge (hf v hve f hh.1 hvf)) hh.2

lemma free_shadow_iff_lower {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G)
    (u b : ℝ) (hub : u ≤ b) (e : Edge n) :
    free (shadowAt G t u) e ↔ u ≤ lowerTime b (history G b t) e := by
  rw [←early_history_eq G t u b hub]
  exact free_early_iff_lower u b hub _ e

lemma history_eq_of_shadow_eq {n : ℕ} (G H : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (b : ℝ) (hshadow : shadowAt G (fun f => T f.val) b = shadowAt H (fun f => T f.val) b) :
    history G b (fun f => T f.val) = history H b (fun f => T f.val) := by
  apply Prod.ext hshadow
  funext e
  by_cases he : e ∈ shadowAt G (fun f => T f.val) b
  · have heG : e ∈ G.edgeSet := by simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using shadowAt_subset_graph G _ b he
    have heH : e ∈ H.edgeSet := by simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using shadowAt_subset_graph H _ b (hshadow ▸ he)
    simp only [history,heG,heH,↓reduceDIte,←hshadow,he,↓reduceIte]
  · simp only [history,←hshadow,he,↓reduceIte]
    split_ifs <;> rfl

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma edge_acceptance_threshold {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (hT : Set.InjOn T G.edgeSet) (e : G.edgeSet) (b : ℝ) :
    e.val ∈ shadowAt G (fun f => T f.val) b ↔
      T e.val < b ∧ T e.val ≤ lowerTime b (history (G.deleteEdges {e.val}) b (fun f => T f.val)) e.val := by
  rw [shadow_member_iff G T hT b e]
  by_cases htb : T e.val < b
  · simp only [htb,true_and]
    exact free_shadow_iff_lower _ _ _ b (le_of_lt htb) e.val
  · simp only [htb,false_and]

lemma rejected_edge_threshold {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (hT : Set.InjOn T G.edgeSet) (e : G.edgeSet) (b : ℝ)
    (he : e.val ∉ shadowAt G (fun f => T f.val) b) :
    lowerTime b (history (G.deleteEdges {e.val}) b (fun f => T f.val)) e.val ≤ T e.val ∧
    history G b (fun f => T f.val) = history (G.deleteEdges {e.val}) b (fun f => T f.val) := by
  constructor
  · by_contra hn
    have ht := lt_of_not_ge hn
    apply he
    apply (edge_acceptance_threshold G T hT e b).mpr
    exact ⟨ht.trans_le (lowerTime_le _ _ _),le_of_lt ht⟩
  · exact history_eq_of_shadow_eq G _ T b (shadowAt_delete_unselected G T hT e.val b he)

lemma edge_after_threshold {n : ℕ} (G : SimpleGraph (Fin n)) (T : Edge n → ℝ)
    (hT : Set.InjOn T G.edgeSet) (e : G.edgeSet) (b : ℝ)
    (ht : lowerTime b (history (G.deleteEdges {e.val}) b (fun f => T f.val)) e.val < T e.val) :
    history G b (fun f => T f.val) = history (G.deleteEdges {e.val}) b (fun f => T f.val) := by
  apply (rejected_edge_threshold G T hT e b ?_).2
  intro he
  exact (not_le_of_gt ht) ((edge_acceptance_threshold G T hT e b).mp he).2

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def insertTime {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet)
    (z : ℝ × Times (G.deleteEdges {e.val})) : Times G := fun f =>
  if h : f = e then z.1 else z.2 ⟨f.val,by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨f.property,fun hh => h (Subtype.ext hh)⟩⟩

lemma insertTime_self {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet)
    (z : ℝ × Times (G.deleteEdges {e.val})) : insertTime G e z e = z.1 := by simp [insertTime]

lemma insertTime_restrict {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (t : Times G) :
    insertTime G e (t e,restrictTimes G e t) = t := by
  funext f
  by_cases hfe : f = e
  · subst f; exact insertTime_self G e _
  · simp only [insertTime,hfe,↓reduceDIte]
    rfl

lemma restrictTimes_insertTime {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet)
    (z : ℝ × Times (G.deleteEdges {e.val})) : restrictTimes G e (insertTime G e z) = z.2 := by
  funext f
  dsimp only [restrictTimes,insertTime]
  split_ifs with h
  · have hf := f.property
    simp only [SimpleGraph.edgeSet_deleteEdges,Set.mem_sdiff,Set.mem_singleton_iff] at hf
    exact (hf.2 (congrArg Subtype.val h)).elim
  · rfl

lemma measurable_insertTime {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) : Measurable (insertTime G e) := by
  apply measurable_pi_iff.mpr
  intro f
  dsimp only [insertTime]
  split_ifs
  · exact measurable_fst
  · exact (measurable_pi_apply _).comp measurable_snd

def edgeSplit {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) :
    Times G ≃ᵐ ℝ × Times (G.deleteEdges {e.val}) where
  toFun t := (t e,restrictTimes G e t)
  invFun := insertTime G e
  left_inv := insertTime_restrict G e
  right_inv z := Prod.ext (insertTime_self G e z) (restrictTimes_insertTime G e z)
  measurable_toFun := (edge_product_preserving G e).measurable
  measurable_invFun := measurable_insertTime G e

lemma insertTime_preserving {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) :
    MeasurePreserving (insertTime G e)
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (arrivalLaw (G.deleteEdges {e.val}))) (arrivalLaw G) :=
  MeasurePreserving.symm (edgeSplit G e) (edge_product_preserving G e)

lemma insertTime_other {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet)
    (z : ℝ × Times (G.deleteEdges {e.val})) (f : (G.deleteEdges {e.val}).edgeSet) :
    insertTime G e z ⟨f.val,by
      have hf := f.property; simp only [SimpleGraph.edgeSet_deleteEdges,Set.mem_sdiff,Set.mem_singleton_iff] at hf; exact hf.1⟩ = z.2 f := by
  dsimp only [insertTime]
  split_ifs with h
  · have hf := f.property
    simp only [SimpleGraph.edgeSet_deleteEdges,Set.mem_sdiff,Set.mem_singleton_iff] at hf
    exact (hf.2 (congrArg Subtype.val h)).elim
  · rfl

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def refreshPair (a : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  if z.1 < a then z else (a+(1-a)*z.2,(z.1-a)/(1-a))

lemma measurable_refreshPair : Measurable (fun z : ℝ × (ℝ × ℝ) => refreshPair z.1 z.2) := by
  have hx : Measurable (fun z : ℝ × (ℝ × ℝ) => z.2.1) := measurable_fst.comp measurable_snd
  have hu : Measurable (fun z : ℝ × (ℝ × ℝ) => z.2.2) := measurable_snd.comp measurable_snd
  have ha : Measurable (fun z : ℝ × (ℝ × ℝ) => z.1) := measurable_fst
  exact measurable_snd.ite (measurableSet_lt hx ha)
    ((ha.add ((measurable_const.sub ha).mul hu)).prodMk ((hx.sub ha).div (measurable_const.sub ha)))

lemma refreshPair_preserving (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    MeasurePreserving (refreshPair a)
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1)))
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  let c := ENNReal.ofReal (1-a)
  let ν : Measure ℝ := c⁻¹ • volume.restrict (Set.Ioo a 1)
  let M := μ.prod μ
  let S : Set (ℝ × ℝ) := Set.Ici a ×ˢ Set.univ
  let A : ℝ → ℝ := fun u => a+(1-a)*u
  let I : ℝ → ℝ := fun x => (x-a)/(1-a)
  have hp : 0 < 1-a := sub_pos.mpr ha1
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA : Measurable A := measurable_const.add (measurable_const.mul measurable_id)
  have hI : Measurable I := (measurable_id.sub measurable_const).div_const _
  have hAMP : MeasurePreserving A μ ν := ⟨hA,uniform_affine_map a ha1⟩
  have hIMP : MeasurePreserving I ν μ := by
    constructor
    · exact hI
    · rw [←hAMP.map_eq,Measure.map_map hI hA]
      have hcomp : I ∘ A = id := by
        funext u
        dsimp [I,A]
        field_simp [ne_of_gt hp]
        ring
      rw [hcomp,Measure.map_id]
  haveI : IsFiniteMeasure ν := by rw [←hAMP.map_eq]; infer_instance
  have htailMP : MeasurePreserving (fun z : ℝ × ℝ => (A z.2,I z.1)) (ν.prod μ) (ν.prod μ) := by
    convert! (hAMP.prod (MeasurePreserving.id μ)).comp
      ((show MeasurePreserving Prod.swap (μ.prod μ) (μ.prod μ) from ⟨measurable_swap,Measure.prod_swap⟩).comp (hIMP.prod (MeasurePreserving.id μ))) using 1
  have hμtail : μ.restrict (Set.Ici a) = c • ν := by
    dsimp only [μ,ν]
    rw [Measure.restrict_restrict measurableSet_Ici]
    have hset : Set.Ici a ∩ Set.Icc (0:ℝ) 1 = Set.Icc a 1 := by
      ext x
      simp only [Set.mem_inter_iff,Set.mem_Ici,Set.mem_Icc]
      constructor <;> intro hh
      · exact ⟨hh.1,hh.2.2⟩
      · exact ⟨hh.1,ha.trans hh.1,hh.2⟩
    rw [hset,←restrict_Ioo_eq_restrict_Icc,smul_smul,ENNReal.mul_inv_cancel hc hct,one_smul]
  have hS : MeasurableSet S := measurableSet_Ici.prod MeasurableSet.univ
  have htail : M.restrict S = c • (ν.prod μ) := by
    dsimp only [M,S]
    rw [←Measure.prod_restrict,Measure.restrict_univ,hμtail,Measure.prod_smul_left]
  have hpres : MeasurePreserving (fun z : ℝ × ℝ => (A z.2,I z.1)) (M.restrict S) (M.restrict S) := by
    rw [htail]
    exact htailMP.smul_measure c
  have hmeas : Measurable (refreshPair a) := measurable_refreshPair.comp measurable_prodMk_left
  constructor
  · exact hmeas
  · have heq1 : (M.restrict S).map (refreshPair a) = M.restrict S := by
      calc
        _ = (M.restrict S).map (fun z : ℝ × ℝ => (A z.2,I z.1)) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem hS] with z hz
          have hz' : a ≤ z.1 := hz.1
          simp only [refreshPair,not_lt.mpr hz',↓reduceIte,A,I]
        _ = _ := hpres.map_eq
    have heq2 : (M.restrict Sᶜ).map (refreshPair a) = M.restrict Sᶜ := by
      calc
        _ = (M.restrict Sᶜ).map id := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem hS.compl] with z hz
          have hz' : z.1 < a := by
            have hn : ¬a ≤ z.1 := fun hh => hz ⟨hh,Set.mem_univ _⟩
            exact lt_of_not_ge hn
          simp only [refreshPair,hz',↓reduceIte,id_eq]
        _ = _ := Measure.map_id
    have hsplt := Measure.restrict_add_restrict_compl hS (μ:=M)
    change M.map (refreshPair a) = M
    rw [←hsplt,Measure.map_add _ _ hmeas,heq1,heq2,hsplt]

end
end FengLiYangMatching.General
open MeasureTheory
namespace FengLiYangMatching.General

lemma product_reorder_preserving {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun z : (α × β) × (γ × δ) => ((z.1.1,z.2.1),(z.1.2,z.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μb μc μd))
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ:=μb) (ν:=μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μa μc (μb.prod μd))
  convert! h5.comp (h4.comp (h3.comp (h2.comp h1))) using 1

end FengLiYangMatching.General
open MeasureTheory Classical
namespace FengLiYangMatching.General
noncomputable section

def jointEdgeSplit {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) :
    (Times G × Times G) ≃ᵐ
      (Times (G.deleteEdges {e.val}) × Times (G.deleteEdges {e.val})) × (ℝ × ℝ) where
  toFun w := ((restrictTimes G e w.1,restrictTimes G e w.2),(w.1 e,w.2 e))
  invFun z := (insertTime G e (z.2.1,z.1.1),insertTime G e (z.2.2,z.1.2))
  left_inv w := Prod.ext (insertTime_restrict G e w.1) (insertTime_restrict G e w.2)
  right_inv z := by
    apply Prod.ext
    · exact Prod.ext (restrictTimes_insertTime G e _) (restrictTimes_insertTime G e _)
    · exact Prod.ext (insertTime_self G e _) (insertTime_self G e _)
  measurable_toFun := by
    have hm := (edge_product_preserving G e).measurable
    exact (((measurable_snd.comp hm).comp measurable_fst).prodMk
      ((measurable_snd.comp hm).comp measurable_snd)).prodMk
      (((measurable_pi_apply e).comp measurable_fst).prodMk ((measurable_pi_apply e).comp measurable_snd))
  measurable_invFun := by
    exact ((measurable_insertTime G e).comp
      ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_insertTime G e).comp
        ((measurable_snd.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)))

lemma jointEdgeSplit_preserving {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) :
    MeasurePreserving (jointEdgeSplit G e) ((arrivalLaw G).prod (arrivalLaw G))
      (((arrivalLaw (G.deleteEdges {e.val})).prod (arrivalLaw (G.deleteEdges {e.val}))).prod
        ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1)))) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  let ν := arrivalLaw (G.deleteEdges {e.val})
  haveI := arrival_probability (G.deleteEdges {e.val})
  haveI := arrival_probability G
  have hsplit := (Measure.measurePreserving_swap (μ:=μ) (ν:=ν)).comp (edge_product_preserving G e)
  convert! (product_reorder_preserving ν μ ν μ).comp (hsplit.prod hsplit) using 1

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def edgeCutoff {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ)
    (r : Times (G.deleteEdges {e.val})) : ℝ := lowerTime b (history (G.deleteEdges {e.val}) b r) e.val

lemma measurable_edgeCutoff {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ) :
    Measurable (edgeCutoff G e b) := (measurable_lowerTime b e.val).comp (measurable_history _ b)

lemma arrival_positive {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ᵐ t ∂arrivalLaw G, ∀ e, 0 < t e := by
  unfold arrivalLaw RandomOrderCRS.arrivalTimeLaw
  apply ae_all_iff.mpr
  intro e
  have hbase : ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), 0 < x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (show ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), x ≠ 0 from by simp only [ae_iff,not_not,Set.setOf_eq_eq_singleton,measure_singleton])] with x hx hne
    exact lt_of_le_of_ne hx.1 hne.symm
  exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : G.edgeSet => volume.restrict (Set.Icc (0:ℝ) 1)) (i:=e)).eventually hbase

lemma lowerTime_history_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : 0 ≤ b)
    (t : Times G) (ht : ∀ e, 0 ≤ t e) (e : Edge n) : 0 ≤ lowerTime b (history G b t) e := by
  apply (le_lowerTime_iff 0 b _ e).mpr
  refine ⟨hb,?_⟩
  intro v hve f hf hvf
  have hfG : f ∈ G.edgeSet := by
    simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using shadowAt_subset_graph G t b hf
  have htime : (history G b t).time f = t ⟨f,hfG⟩ := by
    simp only [History.time,history,hfG,↓reduceDIte]
    exact if_pos hf
  rw [htime]
  exact ht _

def refreshEdge {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ)
    (w : Times G × Times G) : Times G × Times G :=
  let z := jointEdgeSplit G e w
  (jointEdgeSplit G e).symm (z.1,refreshPair (edgeCutoff G e b z.1.1) z.2)

lemma refreshEdge_preserving {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b < 1) :
    MeasurePreserving (refreshEdge G e b) ((arrivalLaw G).prod (arrivalLaw G))
      ((arrivalLaw G).prod (arrivalLaw G)) := by
  let J := G.deleteEdges {e.val}
  let ν := arrivalLaw J
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  haveI := arrival_probability G
  haveI := arrival_probability J
  have hm : Measurable (fun z : (Times J × Times J) × (ℝ × ℝ) =>
      refreshPair (edgeCutoff G e b z.1.1) z.2) :=
    measurable_refreshPair.comp (((measurable_edgeCutoff G e b).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hnonneg : ∀ᵐ r ∂ν, 0 ≤ edgeCutoff G e b r := by
    filter_upwards [arrival_positive J] with r hr
    exact lowerTime_history_nonneg J b hb r (fun f => le_of_lt (hr f)) e.val
  have hprod := (measurePreserving_fst (μ:=ν) (ν:=ν)).quasiMeasurePreserving.ae hnonneg
  have hskew := (MeasurePreserving.id (ν.prod ν)).skew_product hm
    (hprod.mono fun z hz => (refreshPair_preserving (edgeCutoff G e b z.1) hz
      ((lowerTime_le b _ e.val).trans_lt hb1)).map_eq)
  exact (MeasurePreserving.symm (jointEdgeSplit G e) (jointEdgeSplit_preserving G e)).comp
    (hskew.comp (jointEdgeSplit_preserving G e))

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma insertTime_update {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (t : Times G) (s : ℝ) :
    insertTime G e (s,restrictTimes G e t) = Function.update t e s := by
  funext f
  by_cases hfe : f = e
  · subst f
    simp [insertTime]
  · simp only [insertTime,hfe,↓reduceDIte,Function.update_of_ne hfe]
    rfl

lemma refreshEdge_eq_update {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ)
    (w : Times G × Times G) :
    refreshEdge G e b w =
      (Function.update w.1 e (refreshPair (edgeCutoff G e b (restrictTimes G e w.1)) (w.1 e,w.2 e)).1,
       Function.update w.2 e (refreshPair (edgeCutoff G e b (restrictTimes G e w.1)) (w.1 e,w.2 e)).2) := by
  change (insertTime G e (_,restrictTimes G e w.1),insertTime G e (_,restrictTimes G e w.2)) = _
  rw [insertTime_update,insertTime_update]
  rfl

lemma history_after_cutoff {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ)
    (t : Times G) (ht : Function.Injective t) (ha : edgeCutoff G e b (restrictTimes G e t) < t e) :
    history G b t = history (G.deleteEdges {e.val}) b (restrictTimes G e t) := by
  let T : Edge n → ℝ := fun f => if h : f ∈ G.edgeSet then t ⟨f,h⟩ else 0
  have hcoords (f : G.edgeSet) : T f.val = t f := by simp [T,f.property]
  have hTG : (fun f : G.edgeSet => T f.val) = t := funext hcoords
  have hT : Set.InjOn T G.edgeSet := by
    intro f hf g hg hfg
    have hh : t ⟨f,hf⟩ = t ⟨g,hg⟩ := by simpa only [T,dif_pos hf,dif_pos hg] using hfg
    exact congrArg Subtype.val (ht hh)
  have hd : (fun f : (G.deleteEdges {e.val}).edgeSet => T f.val) = restrictTimes G e t := by
    rw [←hTG,restrictTimes_from_global]
  have hh := edge_after_threshold G T hT e b
  rw [hcoords,hd] at hh
  simpa only [hTG] using hh ha

lemma arrival_ne_cutoff {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ) :
    ∀ᵐ t ∂arrivalLaw G, t e ≠ edgeCutoff G e b (restrictTimes G e t) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  let ν := arrivalLaw (G.deleteEdges {e.val})
  haveI := arrival_probability (G.deleteEdges {e.val})
  have hset : MeasurableSet {z : ℝ × Times (G.deleteEdges {e.val}) | z.1 = edgeCutoff G e b z.2} :=
    measurableSet_eq_fun measurable_fst ((measurable_edgeCutoff G e b).comp measurable_snd)
  have hzero : (μ.prod ν) {z : ℝ × Times (G.deleteEdges {e.val}) | z.1 = edgeCutoff G e b z.2} = 0 := by
    rw [Measure.prod_apply_symm hset]
    simp only [Set.preimage_setOf_eq,Set.setOf_eq_eq_singleton,MeasureTheory.measure_singleton,lintegral_zero]
  have hh : ∀ᵐ z ∂μ.prod ν, z.1 ≠ edgeCutoff G e b z.2 := by
    simpa only [ae_iff,not_not] using hzero
  exact (edge_product_preserving G e).quasiMeasurePreserving.ae hh

lemma refreshEdge_history {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b < 1) :
    ∀ᵐ w ∂(arrivalLaw G).prod (arrivalLaw G), history G b (refreshEdge G e b w).1 = history G b w.1 := by
  haveI := arrival_probability G
  have hfst := measurePreserving_fst (μ:=arrivalLaw G) (ν:=arrivalLaw G)
  have hsnd := measurePreserving_snd (μ:=arrivalLaw G) (ν:=arrivalLaw G)
  have hinj := hfst.quasiMeasurePreserving.ae (arrival_injective G)
  have hnew := (refreshEdge_preserving G e b hb hb1).quasiMeasurePreserving.ae hinj
  filter_upwards [hinj,hnew,hsnd.quasiMeasurePreserving.ae (arrival_positive G),
    hfst.quasiMeasurePreserving.ae (arrival_ne_cutoff G e b)] with w hw hn hu hne
  let a := edgeCutoff G e b (restrictTimes G e w.1)
  have hformula := refreshEdge_eq_update G e b w
  have hr : restrictTimes G e (refreshEdge G e b w).1 = restrictTimes G e w.1 := by
    change restrictTimes G e (insertTime G e (_,restrictTimes G e w.1)) = _
    exact restrictTimes_insertTime G e _
  by_cases hx : w.1 e < a
  · have heq : (refreshEdge G e b w).1 = w.1 := by
      rw [hformula]
      change w.1 e < edgeCutoff G e b (restrictTimes G e w.1) at hx
      simp only [refreshPair,hx,↓reduceIte,Function.update_eq_self]
    rw [heq]
  · have hxa : a < w.1 e := lt_of_le_of_ne (le_of_not_gt hx) hne.symm
    have hold := history_after_cutoff G e b w.1 hw hxa
    have hval : (refreshEdge G e b w).1 e = a+(1-a)*w.2 e := by
      rw [hformula]
      change ¬w.1 e < edgeCutoff G e b (restrictTimes G e w.1) at hx
      simp only [Function.update_self,refreshPair,hx,↓reduceIte]
      rfl
    have hab : a ≤ b := lowerTime_le b _ e.val
    have hnewa : edgeCutoff G e b (restrictTimes G e (refreshEdge G e b w).1) < (refreshEdge G e b w).1 e := by
      rw [hr,hval]
      change a < a+(1-a)*w.2 e
      nlinarith [hu e]
    rw [history_after_cutoff G e b _ hn hnewa,hr,←hold]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma edge_acceptance_cutoff {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ)
    (t : Times G) (ht : Function.Injective t) :
    e.val ∈ shadowAt G t b ↔ t e < b ∧ t e ≤ edgeCutoff G e b (restrictTimes G e t) := by
  let T : Edge n → ℝ := fun f => if h : f ∈ G.edgeSet then t ⟨f,h⟩ else 0
  have hcoords (f : G.edgeSet) : T f.val = t f := by simp [T,f.property]
  have hTG : (fun f : G.edgeSet => T f.val) = t := funext hcoords
  have hT : Set.InjOn T G.edgeSet := by
    intro f hf g hg hfg
    have hh : t ⟨f,hf⟩ = t ⟨g,hg⟩ := by simpa only [T,dif_pos hf,dif_pos hg] using hfg
    exact congrArg Subtype.val (ht hh)
  have hd : (fun f : (G.deleteEdges {e.val}).edgeSet => T f.val) = restrictTimes G e t := by
    rw [←hTG,restrictTimes_from_global]
  have hh := edge_acceptance_threshold G T hT e b
  simpa only [hcoords,hTG,hd,edgeCutoff] using hh

lemma refreshEdge_first {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ) :
    ∀ᵐ w ∂(arrivalLaw G).prod (arrivalLaw G),
      (refreshEdge G e b w).1 = Function.update w.1 e (residualSample G b (history G b w.1) w.2 e) := by
  haveI := arrival_probability G
  have hfst := measurePreserving_fst (μ:=arrivalLaw G) (ν:=arrivalLaw G)
  filter_upwards [hfst.quasiMeasurePreserving.ae (arrival_injective G),
    hfst.quasiMeasurePreserving.ae (arrival_ne_cutoff G e b)] with w hw hne
  rw [refreshEdge_eq_update]
  apply congrArg (Function.update w.1 e)
  let a := edgeCutoff G e b (restrictTimes G e w.1)
  by_cases hx : w.1 e < a
  · have he : e.val ∈ (history G b w.1).accepted := by
      apply (edge_acceptance_cutoff G e b w.1 hw).mpr
      exact ⟨hx.trans_le (lowerTime_le b _ e.val),le_of_lt hx⟩
    rw [residualSample,if_pos he]
    change w.1 e < edgeCutoff G e b (restrictTimes G e w.1) at hx
    simp only [refreshPair,hx,↓reduceIte]
    change e.val ∈ shadowAt G w.1 b at he
    simp only [History.time,history,e.property,↓reduceDIte,he,↓reduceIte]
  · have hxa : a < w.1 e := lt_of_le_of_ne (le_of_not_gt hx) hne.symm
    have he : e.val ∉ (history G b w.1).accepted := by
      intro he
      exact not_le_of_gt hxa ((edge_acceptance_cutoff G e b w.1 hw).mp he).2
    rw [residualSample,if_neg he,history_after_cutoff G e b w.1 hw hxa]
    change ¬w.1 e < edgeCutoff G e b (restrictTimes G e w.1) at hx
    simp only [refreshPair,hx,↓reduceIte]
    rfl

lemma refreshEdge_other_first {n : ℕ} (G : SimpleGraph (Fin n)) (e f : G.edgeSet) (b : ℝ)
    (w : Times G × Times G) (hfe : f ≠ e) : (refreshEdge G e b w).1 f = w.1 f := by
  rw [refreshEdge_eq_update]
  exact Function.update_of_ne hfe _ _

lemma refreshEdge_other_second {n : ℕ} (G : SimpleGraph (Fin n)) (e f : G.edgeSet) (b : ℝ)
    (w : Times G × Times G) (hfe : f ≠ e) : (refreshEdge G e b w).2 f = w.2 f := by
  rw [refreshEdge_eq_update]
  exact Function.update_of_ne hfe _ _

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def refreshList {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (l : List G.edgeSet)
    (w : Times G × Times G) : Times G × Times G := l.foldl (fun w e => refreshEdge G e b w) w

lemma refreshList_preserving {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b < 1) (l : List G.edgeSet) :
    MeasurePreserving (refreshList G b l) ((arrivalLaw G).prod (arrivalLaw G)) ((arrivalLaw G).prod (arrivalLaw G)) := by
  induction l with
  | nil => exact MeasurePreserving.id _
  | cons e l ih => exact ih.comp (refreshEdge_preserving G e b hb hb1)

lemma refreshList_coordinates {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b < 1) (l : List G.edgeSet) (hl : l.Nodup) :
    ∀ᵐ w ∂(arrivalLaw G).prod (arrivalLaw G),
      history G b (refreshList G b l w).1 = history G b w.1 ∧
      (∀ f, f ∉ l → (refreshList G b l w).1 f = w.1 f ∧ (refreshList G b l w).2 f = w.2 f) ∧
      (∀ f ∈ l, (refreshList G b l w).1 f = residualSample G b (history G b w.1) w.2 f) := by
  induction l with
  | nil => exact Filter.Eventually.of_forall (fun w => ⟨rfl,fun f hf => ⟨rfl,rfl⟩,by simp⟩)
  | cons e l ih =>
    have hn := List.nodup_cons.mp hl
    have ht := (refreshEdge_preserving G e b hb hb1).quasiMeasurePreserving.ae (ih hn.2)
    filter_upwards [refreshEdge_history G e b hb hb1,refreshEdge_first G e b,ht] with w hh hfirst htail
    change history G b (refreshList G b l (refreshEdge G e b w)).1 = history G b w.1 ∧ _
    refine ⟨htail.1.trans hh,?_,?_⟩
    · intro f hf
      have hfe : f ≠ e := by intro h; subst f; exact hf (List.mem_cons_self)
      have hfl : f ∉ l := fun h => hf (List.mem_cons_of_mem _ h)
      exact ⟨(htail.2.1 f hfl).1.trans (refreshEdge_other_first G e f b w hfe),
        (htail.2.1 f hfl).2.trans (refreshEdge_other_second G e f b w hfe)⟩
    · intro f hf
      change (refreshList G b l (refreshEdge G e b w)).1 f = _
      rcases List.mem_cons.mp hf with hfe | hf
      · subst f
        rw [(htail.2.1 e hn.1).1,hfirst,Function.update_self]
      · have hfe : f ≠ e := by intro h; subst f; exact hn.1 hf
        have hu := refreshEdge_other_second G e f b w hfe
        have heq := htail.2.2 f hf
        rw [hh] at heq
        simpa only [residualSample,hu] using heq

lemma refreshAll_coordinates {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b < 1) :
    ∀ᵐ w ∂(arrivalLaw G).prod (arrivalLaw G),
      history G b (refreshList G b (Finset.univ.toList) w).1 = history G b w.1 ∧
      (refreshList G b (Finset.univ.toList) w).1 = residualSample G b (history G b w.1) w.2 := by
  filter_upwards [refreshList_coordinates G b hb hb1 Finset.univ.toList (Finset.nodup_toList _)] with w hw
  refine ⟨hw.1,?_⟩
  funext f
  exact hw.2.2 f (by simp)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma refreshPair_preserving_le (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    MeasurePreserving (refreshPair a)
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1)))
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
  by_cases halt : a < 1
  · exact refreshPair_preserving a ha halt
  have heq : a = 1 := le_antisymm ha1 (le_of_not_gt halt)
  subst a
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  haveI : IsProbabilityMeasure μ := ⟨by dsimp [μ]; simp⟩
  have hlt : ∀ᵐ x ∂μ, x < 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (show ∀ᵐ x ∂μ, x ≠ 1 from by simp only [ae_iff,not_not,Set.setOf_eq_eq_singleton,measure_singleton])] with x hx hn
    exact lt_of_le_of_ne hx.2 hn
  have hprod := (measurePreserving_fst (μ:=μ) (ν:=μ)).quasiMeasurePreserving.ae hlt
  apply (MeasurePreserving.id (μ.prod μ)).congr
    (measurable_refreshPair.comp (measurable_const.prodMk measurable_id))
  filter_upwards [hprod] with z hz
  change z = refreshPair 1 z
  simp only [refreshPair,hz,↓reduceIte,id_eq]

lemma refreshEdge_preserving_le {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    MeasurePreserving (refreshEdge G e b) ((arrivalLaw G).prod (arrivalLaw G))
      ((arrivalLaw G).prod (arrivalLaw G)) := by
  let J := G.deleteEdges {e.val}
  let ν := arrivalLaw J
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  haveI := arrival_probability G
  haveI := arrival_probability J
  have hm : Measurable (fun z : (Times J × Times J) × (ℝ × ℝ) =>
      refreshPair (edgeCutoff G e b z.1.1) z.2) :=
    measurable_refreshPair.comp (((measurable_edgeCutoff G e b).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hnonneg : ∀ᵐ r ∂ν, 0 ≤ edgeCutoff G e b r := by
    filter_upwards [arrival_positive J] with r hr
    exact lowerTime_history_nonneg J b hb r (fun f => le_of_lt (hr f)) e.val
  have hprod := (measurePreserving_fst (μ:=ν) (ν:=ν)).quasiMeasurePreserving.ae hnonneg
  have hskew := (MeasurePreserving.id (ν.prod ν)).skew_product hm
    (hprod.mono fun z hz => (refreshPair_preserving_le (edgeCutoff G e b z.1) hz
      ((lowerTime_le b _ e.val).trans hb1)).map_eq)
  exact (MeasurePreserving.symm (jointEdgeSplit G e) (jointEdgeSplit_preserving G e)).comp
    (hskew.comp (jointEdgeSplit_preserving G e))

lemma refreshEdge_history_le {n : ℕ} (G : SimpleGraph (Fin n)) (e : G.edgeSet) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ᵐ w ∂(arrivalLaw G).prod (arrivalLaw G), history G b (refreshEdge G e b w).1 = history G b w.1 := by
  haveI := arrival_probability G
  have hfst := measurePreserving_fst (μ:=arrivalLaw G) (ν:=arrivalLaw G)
  have hsnd := measurePreserving_snd (μ:=arrivalLaw G) (ν:=arrivalLaw G)
  have hinj := hfst.quasiMeasurePreserving.ae (arrival_injective G)
  have hnew := (refreshEdge_preserving_le G e b hb hb1).quasiMeasurePreserving.ae hinj
  filter_upwards [hinj,hnew,hsnd.quasiMeasurePreserving.ae (arrival_positive G),
    hfst.quasiMeasurePreserving.ae (arrival_ne_cutoff G e b),
    hfst.quasiMeasurePreserving.ae (arrival_lt_one G)] with w hw hn hu hne hlt
  let a := edgeCutoff G e b (restrictTimes G e w.1)
  have hformula := refreshEdge_eq_update G e b w
  have hr : restrictTimes G e (refreshEdge G e b w).1 = restrictTimes G e w.1 := by
    change restrictTimes G e (insertTime G e (_,restrictTimes G e w.1)) = _
    exact restrictTimes_insertTime G e _
  by_cases hx : w.1 e < a
  · have heq : (refreshEdge G e b w).1 = w.1 := by
      rw [hformula]
      change w.1 e < edgeCutoff G e b (restrictTimes G e w.1) at hx
      simp only [refreshPair,hx,↓reduceIte,Function.update_eq_self]
    rw [heq]
  · have hxa : a < w.1 e := lt_of_le_of_ne (le_of_not_gt hx) hne.symm
    have hold := history_after_cutoff G e b w.1 hw hxa
    have hval : (refreshEdge G e b w).1 e = a+(1-a)*w.2 e := by
      rw [hformula]
      change ¬w.1 e < edgeCutoff G e b (restrictTimes G e w.1) at hx
      simp only [Function.update_self,refreshPair,hx,↓reduceIte]
      rfl
    have hab : a ≤ b := lowerTime_le b _ e.val
    have ha1 : a < 1 := hxa.trans (hlt e)
    have hnewa : edgeCutoff G e b (restrictTimes G e (refreshEdge G e b w).1) < (refreshEdge G e b w).1 e := by
      rw [hr,hval]
      change a < a+(1-a)*w.2 e
      nlinarith [hu e]
    rw [history_after_cutoff G e b _ hn hnewa,hr,←hold]


end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma refreshList_preserving_le {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (l : List G.edgeSet) :
    MeasurePreserving (refreshList G b l) ((arrivalLaw G).prod (arrivalLaw G)) ((arrivalLaw G).prod (arrivalLaw G)) := by
  induction l with
  | nil => exact MeasurePreserving.id _
  | cons e l ih => exact ih.comp (refreshEdge_preserving_le G e b hb hb1)

lemma refreshList_coordinates_le {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (l : List G.edgeSet) (hl : l.Nodup) :
    ∀ᵐ w ∂(arrivalLaw G).prod (arrivalLaw G),
      history G b (refreshList G b l w).1 = history G b w.1 ∧
      (∀ f, f ∉ l → (refreshList G b l w).1 f = w.1 f ∧ (refreshList G b l w).2 f = w.2 f) ∧
      (∀ f ∈ l, (refreshList G b l w).1 f = residualSample G b (history G b w.1) w.2 f) := by
  induction l with
  | nil => exact Filter.Eventually.of_forall (fun w => ⟨rfl,fun f hf => ⟨rfl,rfl⟩,by simp⟩)
  | cons e l ih =>
    have hn := List.nodup_cons.mp hl
    have ht := (refreshEdge_preserving_le G e b hb hb1).quasiMeasurePreserving.ae (ih hn.2)
    filter_upwards [refreshEdge_history_le G e b hb hb1,refreshEdge_first G e b,ht] with w hh hfirst htail
    change history G b (refreshList G b l (refreshEdge G e b w)).1 = history G b w.1 ∧ _
    refine ⟨htail.1.trans hh,?_,?_⟩
    · intro f hf
      have hfe : f ≠ e := by intro h; subst f; exact hf (List.mem_cons_self)
      have hfl : f ∉ l := fun h => hf (List.mem_cons_of_mem _ h)
      exact ⟨(htail.2.1 f hfl).1.trans (refreshEdge_other_first G e f b w hfe),
        (htail.2.1 f hfl).2.trans (refreshEdge_other_second G e f b w hfe)⟩
    · intro f hf
      change (refreshList G b l (refreshEdge G e b w)).1 f = _
      rcases List.mem_cons.mp hf with hfe | hf
      · subst f
        rw [(htail.2.1 e hn.1).1,hfirst,Function.update_self]
      · have hfe : f ≠ e := by intro h; subst f; exact hn.1 hf
        have hu := refreshEdge_other_second G e f b w hfe
        have heq := htail.2.2 f hf
        rw [hh] at heq
        simpa only [residualSample,hu] using heq

lemma refreshAll_coordinates_le {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ᵐ w ∂(arrivalLaw G).prod (arrivalLaw G),
      history G b (refreshList G b (Finset.univ.toList) w).1 = history G b w.1 ∧
      (refreshList G b (Finset.univ.toList) w).1 = residualSample G b (history G b w.1) w.2 := by
  filter_upwards [refreshList_coordinates_le G b hb hb1 Finset.univ.toList (Finset.nodup_toList _)] with w hw
  refine ⟨hw.1,?_⟩
  funext f
  exact hw.2.2 f (by simp)


end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def sampledResidualLaw {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (h : History n) : Measure (Times G) :=
  (arrivalLaw G).map (residualSample G b h)

lemma sampledResidual_probability {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (h : History n) :
    IsProbabilityMeasure (sampledResidualLaw G b h) := by
  haveI := arrival_probability G
  have hm : Measurable (residualSample G b h) := (measurable_residualSample G b).comp measurable_prodMk_left
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

lemma measurable_sampledResidualLaw {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ)
    (A : Set (Times G)) (hA : MeasurableSet A) :
    Measurable (fun h : History n => sampledResidualLaw G b h A) := by
  haveI := arrival_probability G
  have hm := measurable_measure_prodMk_left (ν:=arrivalLaw G) ((measurable_residualSample G b) hA)
  convert! hm using 1
  funext h
  rw [sampledResidualLaw,Measure.map_apply]
  · rfl
  · exact (measurable_residualSample G b).comp measurable_prodMk_left
  · exact hA

lemma history_resampling_law_le {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ((arrivalLaw G).prod (arrivalLaw G)).map
      (fun w : Times G × Times G => (history G b w.1,residualSample G b (history G b w.1) w.2)) =
      (arrivalLaw G).map (fun t => (history G b t,t)) := by
  haveI := arrival_probability G
  let μ := (arrivalLaw G).prod (arrivalLaw G)
  let g : Times G → History n × Times G := fun t => (history G b t,t)
  let f : Times G × Times G → History n × Times G := fun w => g w.1
  let T := refreshList G b Finset.univ.toList
  have hg : Measurable g := (measurable_history G b).prodMk measurable_id
  have hf : Measurable f := hg.comp measurable_fst
  have hT := refreshList_preserving_le G b hb hb1 Finset.univ.toList
  have hgood := refreshAll_coordinates_le G b hb hb1
  calc
    _ = μ.map (f ∘ T) := by
      apply Measure.map_congr
      filter_upwards [hgood] with w hw
      exact (Prod.ext hw.1 hw.2).symm
    _ = (μ.map T).map f := (Measure.map_map hf hT.measurable).symm
    _ = μ.map f := by rw [hT.map_eq]
    _ = ((arrivalLaw G).map (fun t => (history G b t,t))) := by
      have hh := Measure.map_map hg (measurable_fst : Measurable (Prod.fst : Times G × Times G → Times G)) (μ:=μ)
      rw [(measurePreserving_fst (μ:=arrivalLaw G) (ν:=arrivalLaw G)).map_eq] at hh
      exact hh.symm

lemma history_sampled_disintegration {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (S : Set (History n)) (hS : MeasurableSet S) (A : Set (Times G)) (hA : MeasurableSet A) :
    arrivalLaw G (A ∩ (history G b) ⁻¹' S) =
      ∫⁻ h in S, sampledResidualLaw G b h A ∂historyLaw G b := by
  haveI := arrival_probability G
  let q : Times G × Times G → History n × Times G :=
    fun w => (history G b w.1,residualSample G b (history G b w.1) w.2)
  have hh : Measurable (fun w : Times G × Times G => history G b w.1) :=
    (measurable_history G b).comp measurable_fst
  have hpair : Measurable (fun w : Times G × Times G => (history G b w.1,w.2)) := hh.prodMk measurable_snd
  have hr0 := (measurable_residualSample G b).comp hpair
  have hr : Measurable (fun w : Times G × Times G => residualSample G b (history G b w.1) w.2) := by
    convert! hr0 using 1
  have hq : Measurable q := hh.prodMk hr
  have hg : Measurable (fun t : Times G => (history G b t,t)) := by
    convert! (measurable_history G b).prodMk measurable_id using 1
  have heq := congrArg (fun m : Measure (History n × Times G) => m (S ×ˢ A)) (history_resampling_law_le G b hb hb1)
  rw [Measure.map_apply hq (hS.prod hA),
    Measure.map_apply hg (hS.prod hA)] at heq
  have hleft : (fun t : Times G => (history G b t,t)) ⁻¹' (S ×ˢ A) = A ∩ (history G b) ⁻¹' S := by
    ext t
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_inter_iff]
    tauto
  rw [hleft] at heq
  have hinter (t : Times G) :
      arrivalLaw G ((fun u : Times G => q (t,u)) ⁻¹' (S ×ˢ A)) =
        S.indicator (fun h => sampledResidualLaw G b h A) (history G b t) := by
    have huf : Measurable (fun u : Times G => (history G b t,u)) := measurable_const.prodMk measurable_id
    have hu0 := (measurable_residualSample G b).comp huf
    have hu : Measurable (residualSample G b (history G b t)) := by
      convert! hu0 using 1
    have hr : sampledResidualLaw G b (history G b t) A =
        arrivalLaw G ((residualSample G b (history G b t)) ⁻¹' A) := by
      rw [sampledResidualLaw,Measure.map_apply hu hA]
    by_cases ht : history G b t ∈ S
    · rw [Set.indicator_of_mem ht,hr]
      congr 1
      ext u
      simp only [q,Set.mem_preimage,Set.mem_prod,ht,true_and]
    · rw [Set.indicator_of_notMem ht]
      have hempty : (fun u : Times G => q (t,u)) ⁻¹' (S ×ˢ A) = ∅ := by
        ext u
        simp only [q,Set.mem_preimage,Set.mem_prod,ht,false_and,Set.mem_empty_iff_false]
      rw [hempty,measure_empty]
  have hp : ((arrivalLaw G).prod (arrivalLaw G)) (q ⁻¹' (S ×ˢ A)) =
      ∫⁻ t, S.indicator (fun h => sampledResidualLaw G b h A) (history G b t) ∂arrivalLaw G := by
    rw [Measure.prod_apply (hq (hS.prod hA))]
    apply lintegral_congr
    exact hinter
  have hm : Measurable (S.indicator (fun h => sampledResidualLaw G b h A)) :=
    (measurable_sampledResidualLaw G b A hA).indicator hS
  have hmap := lintegral_map' (μ:=arrivalLaw G) hm.aemeasurable (measurable_history G b).aemeasurable
  rw [←lintegral_indicator hS,historyLaw,hmap]
  exact heq.symm.trans hp

lemma residual_sample_map_valid {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (h : History n)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime b h e.val < 1) :
    (arrivalLaw G).map (residualSample G b h) = residualLaw G b h := by
  let f : G.edgeSet → ℝ → ℝ := fun e u =>
    if e.val ∈ h.accepted then h.time e.val else lowerTime b h e.val + (1-lowerTime b h e.val)*u
  have hf (e : G.edgeSet) : Measurable (f e) := by
    dsimp only [f]
    split_ifs
    · exact measurable_const
    · exact measurable_const.add (measurable_const.mul measurable_id)
  have hmap (e : G.edgeSet) :
      (volume.restrict (Set.Icc (0:ℝ) 1)).map (f e) =
      if e.val ∈ h.accepted then Measure.dirac (h.time e.val)
      else (ENNReal.ofReal (1-lowerTime b h e.val))⁻¹ • volume.restrict (Set.Ioo (lowerTime b h e.val) 1) := by
    dsimp only [f]
    by_cases he : e.val ∈ h.accepted
    · simp only [he,↓reduceIte]
      rw [Measure.map_const]
      norm_num [Measure.restrict_apply_univ,Real.volume_Icc]
    · simp only [he,↓reduceIte]
      exact uniform_affine_map _ (hvalid e he)
  haveI (e : G.edgeSet) : IsFiniteMeasure ((volume.restrict (Set.Icc (0:ℝ) 1)).map (f e)) := inferInstance
  have hh := Measure.pi_map_pi (fun e => (hf e).aemeasurable (μ:=volume.restrict (Set.Icc (0:ℝ) 1)))
  change (Measure.pi (fun _ : G.edgeSet => volume.restrict (Set.Icc (0:ℝ) 1))).map (fun u e => f e (u e)) = _ at hh
  convert! hh.trans (congrArg Measure.pi (funext hmap)) using 1


end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma rejected_full_lower_lt {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G)
    (ht : Function.Injective t) (hlt : ∀ e, t e < 1) (e : G.edgeSet)
    (he : e.val ∉ (history G 1 t).accepted) : lowerTime 1 (history G 1 t) e.val < 1 := by
  have hcut : edgeCutoff G e 1 (restrictTimes G e t) < t e := by
    apply lt_of_not_ge
    intro hh
    exact he ((edge_acceptance_cutoff G e 1 t ht).mpr ⟨hlt e,hh⟩)
  rw [history_after_cutoff G e 1 t ht hcut]
  exact hcut.trans (hlt e)

lemma full_history_valid {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ᵐ h ∂historyLaw G 1, ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1 := by
  have hmeas : MeasurableSet {h : History n | ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1} := by
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro e
    have hmem : MeasurableSet {h : History n | e.val ∈ h.accepted} :=
      (measurableSet_mem_finset e.val).preimage measurable_fst
    have hlt : MeasurableSet {h : History n | lowerTime 1 h e.val < 1} :=
      measurableSet_lt (measurable_lowerTime 1 e.val) measurable_const
    have heq : {h : History n | e.val ∉ h.accepted → lowerTime 1 h e.val < 1} =
        {h : History n | e.val ∈ h.accepted} ∪ {h : History n | lowerTime 1 h e.val < 1} := by
      ext h
      simp only [Set.mem_setOf_eq,Set.mem_union]
      tauto
    rw [heq]
    exact hmem.union hlt
  apply (ae_map_iff (measurable_history G 1).aemeasurable hmeas).mpr
  filter_upwards [arrival_injective G,arrival_lt_one G] with t ht hlt
  intro e he
  exact rejected_full_lower_lt G t ht hlt e he

lemma full_history_residual_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ᵐ h ∂historyLaw G 1, sampledResidualLaw G 1 h = residualLaw G 1 h := by
  filter_upwards [full_history_valid G] with h hh
  exact residual_sample_map_valid G 1 h hh

lemma full_history_disintegration {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Set (History n)) (hS : MeasurableSet S) (A : Set (Times G)) (hA : MeasurableSet A) :
    arrivalLaw G (A ∩ (history G 1) ⁻¹' S) = ∫⁻ h in S, residualLaw G 1 h A ∂historyLaw G 1 := by
  have hh := history_sampled_disintegration G 1 (by norm_num) le_rfl S hS A hA
  rw [hh]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (full_history_residual_eq G)] with h heq
  rw [heq]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical ProbabilityTheory
namespace FengLiYangMatching.General
noncomputable section

lemma residual_history_support {n : ℕ} (G : SimpleGraph (Fin n)) (a b p : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8) (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3) :
    ∀ᵐ h ∂historyLaw G b, ∀ᵐ t ∂residualLaw G b h, history G b t = h := by
  have h41 := lemma_4_1 G a b p ha hab hb hp0 hp2
  let κ : Kernel (History n) (Times G) := ⟨residualLaw G b,Measure.measurable_of_measurable_coe _ h41.2.1⟩
  have hb1 : b < 1 := hb.trans_lt (by norm_num)
  haveI : IsMarkovKernel κ := ⟨fun h => residual_probability G b hb1 h⟩
  haveI := arrival_probability G
  haveI : IsProbabilityMeasure (historyLaw G b) :=
    Measure.isProbabilityMeasure_map h41.1.aemeasurable
  have hg : Measurable (fun t : Times G => (history G b t,t)) := by
    convert! h41.1.prodMk measurable_id using 1
  have hcomp : (historyLaw G b) ⊗ₘ κ = (arrivalLaw G).map (fun t => (history G b t,t)) := by
    apply Measure.ext_prod
    intro S A hS hA
    rw [Measure.compProd_apply_prod hS hA,Measure.map_apply hg (hS.prod hA)]
    have hset : (fun t : Times G => (history G b t,t)) ⁻¹' (S ×ˢ A) = A ∩ (history G b) ⁻¹' S := by
      ext t
      simp only [Set.mem_preimage,Set.mem_prod,Set.mem_inter_iff]
      tauto
    rw [hset]
    exact (h41.2.2.2 S hS A hA).symm
  have hdiag : MeasurableSet {z : History n × Times G | history G b z.2 = z.1} :=
    measurableSet_eq_fun (h41.1.comp measurable_snd) measurable_fst
  have hgood : ∀ᵐ z ∂(historyLaw G b) ⊗ₘ κ, history G b z.2 = z.1 := by
    rw [hcomp]
    exact (ae_map_iff hg.aemeasurable hdiag).mpr (Filter.Eventually.of_forall (fun t => rfl))
  exact Measure.ae_ae_of_ae_compProd hgood

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma residual_ae_property {n : ℕ} (G : SimpleGraph (Fin n)) (a b p : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8) (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3)
    (P : Times G → Prop) (hP : MeasurableSet {t | P t}) (hAE : ∀ᵐ t ∂arrivalLaw G, P t) :
    ∀ᵐ h ∂historyLaw G b, ∀ᵐ t ∂residualLaw G b h, P t := by
  have h41 := lemma_4_1 G a b p ha hab hb hp0 hp2
  have hbad : MeasurableSet {t | ¬P t} := hP.compl
  have hzero : arrivalLaw G {t | ¬P t} = 0 := ae_iff.mp hAE
  have hdis := h41.2.2.2 Set.univ MeasurableSet.univ {t | ¬P t} hbad
  simp only [Set.preimage_univ,Set.inter_univ,Measure.restrict_univ,hzero] at hdis
  have hz : ∀ᵐ h ∂historyLaw G b, residualLaw G b h {t | ¬P t} = 0 :=
    (lintegral_eq_zero_iff (h41.2.1 _ hbad)).mp hdis.symm
  exact hz.mono (fun h hh => ae_iff.mpr hh)

lemma measurableSet_injective_times {n : ℕ} (G : SimpleGraph (Fin n)) :
    MeasurableSet {t : Times G | Function.Injective t} := by
  change MeasurableSet {t : Times G | ∀ e f, t e = t f → e = f}
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro e
  apply MeasurableSet.iInter
  intro f
  by_cases hef : e = f
  · simp only [hef,implies_true,Set.setOf_true,MeasurableSet.univ]
  · simpa only [hef,imp_false,Set.compl_setOf] using
      (measurableSet_eq_fun (measurable_pi_apply e) (measurable_pi_apply f)).compl

lemma residual_injective {n : ℕ} (G : SimpleGraph (Fin n)) (a b p : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8) (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3) :
    ∀ᵐ h ∂historyLaw G b, ∀ᵐ t ∂residualLaw G b h, Function.Injective t :=
  residual_ae_property G a b p ha hab hb hp0 hp2 Function.Injective (measurableSet_injective_times G) (arrival_injective G)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical ProbabilityTheory
namespace FengLiYangMatching.General
noncomputable section

lemma sampled_history_support {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ᵐ h ∂historyLaw G b, ∀ᵐ t ∂sampledResidualLaw G b h, history G b t = h := by
  have hhist := measurable_history G b
  let κ : Kernel (History n) (Times G) := ⟨sampledResidualLaw G b,Measure.measurable_of_measurable_coe _ (fun A hA => measurable_sampledResidualLaw G b A hA)⟩
  haveI : IsMarkovKernel κ := ⟨fun h => sampledResidual_probability G b h⟩
  haveI := arrival_probability G
  haveI : IsProbabilityMeasure (historyLaw G b) :=
    Measure.isProbabilityMeasure_map hhist.aemeasurable
  have hg : Measurable (fun t : Times G => (history G b t,t)) := by
    convert! hhist.prodMk measurable_id using 1
  have hcomp : (historyLaw G b) ⊗ₘ κ = (arrivalLaw G).map (fun t => (history G b t,t)) := by
    apply Measure.ext_prod
    intro S A hS hA
    rw [Measure.compProd_apply_prod hS hA,Measure.map_apply hg (hS.prod hA)]
    have hset : (fun t : Times G => (history G b t,t)) ⁻¹' (S ×ˢ A) = A ∩ (history G b) ⁻¹' S := by
      ext t
      simp only [Set.mem_preimage,Set.mem_prod,Set.mem_inter_iff]
      tauto
    rw [hset]
    exact (history_sampled_disintegration G b hb hb1 S hS A hA).symm
  have hdiag : MeasurableSet {z : History n × Times G | history G b z.2 = z.1} :=
    measurableSet_eq_fun (hhist.comp measurable_snd) measurable_fst
  have hgood : ∀ᵐ z ∂(historyLaw G b) ⊗ₘ κ, history G b z.2 = z.1 := by
    rw [hcomp]
    exact (ae_map_iff hg.aemeasurable hdiag).mpr (Filter.Eventually.of_forall (fun t => rfl))
  exact Measure.ae_ae_of_ae_compProd hgood


end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma sampled_residual_ae_property {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (P : Times G → Prop)
    (hP : MeasurableSet {t | P t}) (hAE : ∀ᵐ t ∂arrivalLaw G, P t) :
    ∀ᵐ h ∂historyLaw G b, ∀ᵐ t ∂sampledResidualLaw G b h, P t := by
  have hbad : MeasurableSet {t | ¬P t} := hP.compl
  have hzero : arrivalLaw G {t | ¬P t} = 0 := ae_iff.mp hAE
  have hdis := history_sampled_disintegration G b hb hb1 Set.univ MeasurableSet.univ {t | ¬P t} hbad
  simp only [Set.preimage_univ,Set.inter_univ,Measure.restrict_univ,hzero] at hdis
  have hz : ∀ᵐ h ∂historyLaw G b, sampledResidualLaw G b h {t | ¬P t} = 0 :=
    (lintegral_eq_zero_iff (measurable_sampledResidualLaw G b _ hbad)).mp hdis.symm
  exact hz.mono (fun h hh => ae_iff.mpr hh)

lemma full_residual_probability {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ᵐ h ∂historyLaw G 1, IsProbabilityMeasure (residualLaw G 1 h) := by
  filter_upwards [full_history_residual_eq G] with h hh
  rw [←hh]
  exact sampledResidual_probability G 1 h

lemma full_residual_support {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ᵐ h ∂historyLaw G 1, ∀ᵐ t ∂residualLaw G 1 h, history G 1 t = h := by
  filter_upwards [full_history_residual_eq G,sampled_history_support G 1 (by norm_num) le_rfl] with h heq hh
  rw [←heq]
  exact hh

lemma full_residual_injective {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ᵐ h ∂historyLaw G 1, ∀ᵐ t ∂residualLaw G 1 h, Function.Injective t := by
  have hh := sampled_residual_ae_property G 1 (by norm_num) le_rfl Function.Injective
    (measurableSet_injective_times G) (arrival_injective G)
  filter_upwards [full_history_residual_eq G,hh] with h heq hreg
  rw [←heq]
  exact hreg

lemma full_residual_times {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ᵐ h ∂historyLaw G 1, ∀ᵐ t ∂residualLaw G 1 h, ∀ e, 0 < t e ∧ t e < 1 := by
  have hm : MeasurableSet {t : Times G | ∀ e, 0 < t e ∧ t e < 1} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun e =>
      (measurableSet_lt measurable_const (measurable_pi_apply e)).inter
        (measurableSet_lt (measurable_pi_apply e) measurable_const))
  have hAE : ∀ᵐ t ∂arrivalLaw G, ∀ e, 0 < t e ∧ t e < 1 := by
    filter_upwards [arrival_positive G,arrival_lt_one G] with t h0 h1
    exact fun e => ⟨h0 e,h1 e⟩
  have hh := sampled_residual_ae_property G 1 (by norm_num) le_rfl _ hm hAE
  filter_upwards [full_history_residual_eq G,hh] with h heq hreg
  rw [←heq]
  exact hreg

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def graphOfEdges {n : ℕ} (E : EdgeSet n) : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (E : Set (Edge n))

lemma mem_graphOfEdges {n : ℕ} (E : EdgeSet n) (hE : ∀ e ∈ E, ¬e.IsDiag) (e : Edge n) :
    e ∈ (graphOfEdges E).edgeSet ↔ e ∈ E := by
  rw [graphOfEdges,SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_sdiff,Finset.mem_coe,Sym2.mem_diagSet]
  exact ⟨And.left,fun he => ⟨he,hE e he⟩⟩

lemma graphEdges_graphOfEdges {n : ℕ} (E : EdgeSet n) (hE : ∀ e ∈ E, ¬e.IsDiag) :
    graphEdges (graphOfEdges E) = E := by
  ext e
  simp only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and,mem_graphOfEdges E hE]

lemma clockState_graph_history {n : ℕ} (G : SimpleGraph (Fin n)) (v : Edge n → ℝ)
    (hv : Set.InjOn v (graphEdges G)) (s : ℝ) :
    clockOpenState (graphEdges G) v s = shadowAt G (fun e => v e.val) s := by
  have hinj : Function.Injective (fun e : G.edgeSet => v e.val) := by
    intro e f hef
    apply Subtype.ext
    exact hv (by simpa [graphEdges] using e.property) (by simpa [graphEdges] using f.property) hef
  have hh := execution_orderFor G (fun e => v e.val) hinj (graphEdges G) Subset.rfl
  have htimes : ∀ e ∈ graphEdges G, edgeTimes G (fun e => v e.val) e = v e := by
    intro e he
    exact edgeTimes_val G _ (⟨e,by simpa [graphEdges] using he⟩ : G.edgeSet)
  have horder : orderFor (graphEdges G) (fun e => edgeTimes G (fun e => v e.val) e.val) =
      orderFor (graphEdges G) (fun e => v e.val) := by
    congr 1
    funext e
    exact htimes e.val e.property
  rw [horder] at hh
  have hfilter : (executionList G (fun e => v e.val)).filter (fun e => e ∈ graphEdges G) = executionList G (fun e => v e.val) := by
    apply List.filter_eq_self.mpr
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    simpa [graphEdges] using f.property
  rw [hfilter] at hh
  unfold clockOpenState clockOpenPrefix
  rw [hh]
  exact (shadowAt_values G v s).symm

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma clock_edge_accepted {n : ℕ} (E : EdgeSet n) (hE : ∀ e ∈ E, ¬e.IsDiag)
    (v : Edge n → ℝ) (hv : Set.InjOn v E) (e : Edge n) (he : e ∈ E)
    (hf : free (clockOpenState E v (v e)) e) : e ∈ greedy (orderFor E (fun e => v e.val)) := by
  let G := graphOfEdges E
  have hGE : graphEdges G = E := graphEdges_graphOfEdges E hE
  have hinj : Set.InjOn v G.edgeSet := by
    intro e he f hf hef
    exact hv ((mem_graphOfEdges E hE e).mp he) ((mem_graphOfEdges E hE f).mp hf) hef
  have heG : e ∈ G.edgeSet := (mem_graphOfEdges E hE e).mpr he
  have hshadow := (shadow_member_iff G v hinj (v e+1) (⟨e,heG⟩ : G.edgeSet)).mpr
    ⟨by linarith,by
      rw [←shadowAt_delete_prefix G v e hinj (v e) le_rfl]
      have hc := clockState_graph_history G v (by rw [hGE]; exact hv) (v e)
      rw [hGE] at hc
      rw [←hc]
      exact hf⟩
  have hc := clockState_graph_history G v (by rw [hGE]; exact hv) (v e+1)
  rw [hGE] at hc
  rw [←hc] at hshadow
  have hh := greedy_filter_time (orderFor E (fun e => v e.val)) v (orderFor_pairwise E v) (v e+1)
  change e ∈ greedy ((orderFor E (fun e => v e.val)).filter (fun f => v f < v e+1)) at hshadow
  rw [hh] at hshadow
  exact (Finset.mem_filter.mp hshadow).1

lemma clock_partner_matched {n : ℕ} (E : EdgeSet n) (hE : ∀ e ∈ E, ¬e.IsDiag)
    (v : Edge n → ℝ) (hv : Set.InjOn v E) (y w : Fin n) (he : s(y,w) ∈ E)
    (hw : w ∉ covered (clockOpenState E v (v s(y,w)))) :
    y ∈ covered (greedy (orderFor E (fun e => v e.val))) := by
  by_contra hy
  have hh := greedy_filter_time (orderFor E (fun e => v e.val)) v (orderFor_pairwise E v) (v s(y,w))
  have hy' : y ∉ covered (clockOpenState E v (v s(y,w))) := by
    intro h
    apply hy
    have hsub : clockOpenState E v (v s(y,w)) ⊆ greedy (orderFor E (fun e => v e.val)) := by
      unfold clockOpenState clockOpenPrefix
      rw [hh]
      exact Finset.filter_subset _ _
    exact covered_mono hsub h
  have hf : free (clockOpenState E v (v s(y,w))) s(y,w) := by
    intro a ha
    rcases Sym2.mem_iff.mp ha with rfl | rfl
    · exact hy'
    · exact hw
  have hacc := clock_edge_accepted E hE v hv s(y,w) he hf
  apply hy
  simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨s(y,w),hacc,by simp⟩

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma greedy_cover_delete_eq {n : ℕ} (x : Fin n) (l : List (Edge n)) (hl : ∀ e ∈ l, ¬ e.IsDiag)
    (hx : x ∉ covered (greedy l)) : covered (greedy l) = covered (greedy (l.filter (fun e => x ∉ e))) := by
  rcases greedy_coupling x l hl with hh | ⟨u,(⟨hh,hu⟩ | ⟨hh,hu⟩)⟩
  · exact hh
  · exact (hx (by rw [hh]; simp)).elim
  · exact (hx (by rw [hh]; simp)).elim

lemma count_singleton {n : ℕ} (x : Fin n) (F : EdgeSet n) :
    count {x} F = if x ∈ covered F then 1 else 0 := by
  by_cases hx : x ∈ covered F <;> simp [count,Finset.singleton_inter,hx]

lemma count_nonneg {n : ℕ} (A : Finset (Fin n)) (F : EdgeSet n) : 0 ≤ count A F := by unfold count; positivity

lemma filter_endpoint_deletion {n : ℕ} (x : Fin n) (σ : List (Edge n)) (B F : EdgeSet n)
    (hB : ∀ e ∈ B, x ∉ e) (hF : ∀ e ∈ F, x ∈ e) :
    ((σ.filter (fun e => e ∈ B ∨ e ∈ F)).filter (fun e => x ∉ e)) = σ.filter (fun e => e ∈ B) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  by_cases hb : e ∈ B
  · have hx := hB e hb
    simp [hb,hx]
  · by_cases hf : e ∈ F
    · have hx := hF e hf
      simp [hb,hf,hx]
    · simp [hb,hf]

lemma filter_reference_deletion {n : ℕ} (σ : List (Edge n)) (B F : EdgeSet n) (ref : Edge n)
    (hb : ref ∉ B) (hf : ref ∉ F) :
    ((σ.filter (fun e => e ∈ B ∨ e ∈ insert ref F)).filter (fun e => e ≠ ref)) =
      σ.filter (fun e => e ∈ B ∨ e ∈ F) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  by_cases hr : e = ref
  · subst e; simp [hb,hf]
  · simp [hr]

lemma one_reference_coin_bound {n : ℕ} (x y : Fin n) (hxy : x ≠ y)
    (σ : List (Edge n)) (hσ : ∀ e ∈ σ, ¬ e.IsDiag) (href : s(x,y) ∈ σ)
    (B F : EdgeSet n) (hB : ∀ e ∈ B, x ∉ e) (hF : ∀ e ∈ F, x ∈ e)
    (hnot : s(x,y) ∉ F) (q : ℝ) (hq : 3/5 ≤ q) (hq1 : q ≤ 1) :
    q*(3*count {x} (greedy (σ.filter (fun e => e ∈ B ∨ e ∈ insert s(x,y) F)))+
      2*count {y} (greedy (σ.filter (fun e => e ∈ B ∨ e ∈ insert s(x,y) F))))+
    (1-q)*(3*count {x} (greedy (σ.filter (fun e => e ∈ B ∨ e ∈ F)))+
      2*count {y} (greedy (σ.filter (fun e => e ∈ B ∨ e ∈ F))))+
    count {y} (greedy (σ.filter (fun e => e ∈ B))) ≥ 3 := by
  let l := σ.filter (fun e => e ∈ B ∨ e ∈ insert s(x,y) F)
  let l0 := σ.filter (fun e => e ∈ B ∨ e ∈ F)
  let base := σ.filter (fun e => e ∈ B)
  let C := greedy l
  let C0 := greedy l0
  let M := greedy base
  have hl : ∀ e ∈ l, ¬ e.IsDiag := fun e he => hσ e (List.mem_of_mem_filter he)
  have hl0 : ∀ e ∈ l0, ¬ e.IsDiag := fun e he => hσ e (List.mem_of_mem_filter he)
  have hplusF : ∀ e ∈ insert s(x,y) F, x ∈ e := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · simp
    · exact hF e he
  have hdel : l.filter (fun e => x ∉ e) = base := filter_endpoint_deletion x σ B _ hB hplusF
  have hdel0 : l0.filter (fun e => x ∉ e) = base := filter_endpoint_deletion x σ B F hB hF
  have hsame (hx : x ∉ covered C) : covered C = covered M := by
    have hh := greedy_cover_delete_eq x l hl hx
    rw [hdel] at hh
    exact hh
  have hsame0 (hx : x ∉ covered C0) : covered C0 = covered M := by
    have hh := greedy_cover_delete_eq x l0 hl0 hx
    rw [hdel0] at hh
    exact hh
  have hrefB : s(x,y) ∉ B := fun he => hB _ he (by simp)
  have hremove : l.filter (fun e => e ≠ s(x,y)) = l0 := filter_reference_deletion σ B F s(x,y) hrefB hnot
  have hunchanged (he : s(x,y) ∉ C) : C = C0 := by
    have hh := greedy_remove_unselected l s(x,y) he
    rw [hremove] at hh
    exact hh
  have hxmono : x ∈ covered C0 → x ∈ covered C := by
    intro hx0
    by_contra hx
    have he : s(x,y) ∉ C := fun he => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,s(x,y),he,by simp⟩)
    exact hx (hunchanged he ▸ hx0)
  have hfreeboth (hx : x ∉ covered C0) (hy : y ∉ covered M) : x ∈ covered C ∧ y ∈ covered C := by
    have hy0 : y ∉ covered C0 := by rw [hsame0 hx]; exact hy
    have he : s(x,y) ∈ C := by
      by_contra he
      have hCC := hunchanged he
      have hblock := greedy_blocks_seen l s(x,y) (List.mem_filter.mpr ⟨href,by simp⟩)
      apply hblock
      change free C s(x,y)
      rw [hCC]
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,s(x,y),he,by simp⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,s(x,y),he,by simp⟩⟩
  change q*(3*count {x} C+2*count {y} C)+(1-q)*(3*count {x} C0+2*count {y} C0)+count {y} M ≥ 3
  simp only [count_singleton]
  by_cases hyM : y ∈ covered M
  · by_cases hx : x ∈ covered C <;> by_cases hx0 : x ∈ covered C0
    · split_ifs <;> nlinarith
    · have hy0 : y ∈ covered C0 := by rw [hsame0 hx0]; exact hyM
      simp only [hx,hx0,hyM,hy0,↓reduceIte]
      split_ifs <;> nlinarith
    · exact (hx (hxmono hx0)).elim
    · have hy : y ∈ covered C := by rw [hsame hx]; exact hyM
      have hy0 : y ∈ covered C0 := by rw [hsame0 hx0]; exact hyM
      simp only [hx,hx0,hyM,hy,hy0,↓reduceIte]
      ring_nf
      norm_num
  · by_cases hx0 : x ∈ covered C0
    · have hx := hxmono hx0
      simp only [hx,hx0,hyM,↓reduceIte]
      split_ifs <;> nlinarith
    · obtain ⟨hx,hy⟩ := hfreeboth hx0 hyM
      have hy0 : y ∉ covered C0 := by rw [hsame0 hx0]; exact hyM
      simp only [hx,hy,hx0,hy0,hyM,↓reduceIte]
      linarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma greedy_fold_skip_unselected {n : ℕ} (l : List (Edge n)) (F : EdgeSet n) (P : Edge n → Prop)
    [DecidablePred P]
    (h : ∀ e ∈ l, P e → e ∉ l.foldl (fun F e => if free F e then insert e F else F) F) :
    l.foldl (fun F e => if free F e then insert e F else F) F =
      (l.filter (fun e => ¬P e)).foldl (fun F e => if free F e then insert e F else F) F := by
  induction l generalizing F with
  | nil => rfl
  | cons e l ih =>
    by_cases hP : P e
    · have hf : ¬free F e := by
        intro hf
        apply h e List.mem_cons_self hP
        simp only [List.foldl_cons,hf,↓reduceIte]
        exact greedy_fold_mono l (insert e F) (Finset.mem_insert_self _ _)
      have hh := ih F (fun f hf' hPf => by
        have hh := h f (List.mem_cons_of_mem _ hf') hPf
        simpa only [List.foldl_cons,hf,↓reduceIte] using hh)
      simpa [List.filter_cons,hP,hf] using hh
    · have hh := ih (if free F e then insert e F else F) (fun f hf hPf => h f (List.mem_cons_of_mem _ hf) hPf)
      simpa [List.filter_cons,hP] using hh

lemma greedy_skip_unselected {n : ℕ} (l : List (Edge n)) (P : Edge n → Prop) [DecidablePred P]
    (h : ∀ e ∈ l, P e → e ∉ greedy l) : greedy l = greedy (l.filter (fun e => ¬P e)) :=
  greedy_fold_skip_unselected l ∅ P h

lemma greedy_no_selected_extras {n : ℕ} (σ : List (Edge n)) (B F : EdgeSet n) (X : Finset (Fin n))
    (hF : ∀ e ∈ F, ∃ x ∈ X, x ∈ e)
    (hX : ∀ x ∈ X, x ∉ covered (greedy (σ.filter (fun e => e ∈ B ∨ e ∈ F)))) :
    greedy (σ.filter (fun e => e ∈ B ∨ e ∈ F)) = greedy (σ.filter (fun e => e ∈ B)) := by
  have hh := greedy_skip_unselected (σ.filter (fun e => e ∈ B ∨ e ∈ F)) (fun e => e ∉ B) (by
    intro e he hnB heC
    have hmem := of_decide_eq_true (List.mem_filter.mp he).2
    have heF : e ∈ F := hmem.resolve_left hnB
    obtain ⟨x,hx,hxe⟩ := hF e heF
    exact hX x hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,heC,hxe⟩))
  rw [hh]
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  by_cases hB : e ∈ B <;> simp [hB]

lemma localRun_no_endpoints {n : ℕ} (d : Local n) (hd : d.Valid) (σ : List (Edge n))
    (r : EdgeSet n) (hr : r ⊆ d.potential)
    (h1 : d.x1 ∉ covered (localRun d σ r)) (h2 : d.x2 ∉ covered (localRun d σ r)) :
    localRun d σ r = baseRun d σ := by
  apply greedy_no_selected_extras σ d.base r {d.x1,d.x2}
  · intro e he
    obtain ⟨x,hx,y,hy,hxy⟩ := hd.2.2.2.2.2.2 e (hr he)
    exact ⟨x,hx,by rw [hxy]; simp⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h1
    · exact Finset.mem_singleton.mp hx ▸ h2

lemma greedy_insert_unchanged {n : ℕ} (σ : List (Edge n)) (B F : EdgeSet n) (e : Edge n)
    (heB : e ∉ B) (heF : e ∉ F) (he : e ∉ greedy (σ.filter (fun f => f ∈ B ∨ f ∈ insert e F))) :
    greedy (σ.filter (fun f => f ∈ B ∨ f ∈ insert e F)) = greedy (σ.filter (fun f => f ∈ B ∨ f ∈ F)) := by
  rw [greedy_remove_unselected _ e he,filter_reference_deletion σ B F e heB heF]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def clockGreedy {n : ℕ} (E : EdgeSet n) (v : Edge n → ℝ) : EdgeSet n := greedy (orderFor E (fun e => v e.val))

lemma orderFor_subset {α : Type*} [DecidableEq α] (E F : Finset α) (hFE : F ⊆ E)
    (v : α → ℝ) (hv : Set.InjOn v F) :
    orderFor F (fun e => v e.val) = (orderFor E (fun e => v e.val)).filter (fun e => e ∈ F) := by
  have heq : E.filter (fun e => e ∈ F) = F := by ext e; simp only [Finset.mem_filter]; exact ⟨And.right,fun h => ⟨hFE h,h⟩⟩
  have hh := orderFor_filter_sorted E v (fun e => e ∈ F) (by rw [heq]; exact hv)
  rw [heq] at hh
  exact hh

lemma clockGreedy_update_ignored {n : ℕ} (E : EdgeSet n) (e : Edge n) (he : e ∉ E)
    (v : Edge n → ℝ) (u : ℝ) : clockGreedy E (Function.update v e u) = clockGreedy E v := by
  apply congrArg (fun t : E → ℝ => greedy (orderFor E t))
  funext f
  have hne : f.val ≠ e := fun hfe => he (hfe ▸ f.property)
  exact Function.update_of_ne hne u v

lemma clockOpenPrefix_sorted {n : ℕ} (E : EdgeSet n) (v : Edge n → ℝ) (t : ℝ)
    (hv : Set.InjOn v (E.filter (fun e => v e < t))) :
    clockOpenPrefix E v t = orderFor (E.filter (fun e => v e < t)) (fun e => v e.val) :=
  (orderFor_filter_sorted E v _ hv).symm

lemma clockOpenState_insert_before {n : ℕ} (E : EdgeSet n) (e : Edge n)
    (v : Edge n → ℝ) (hv : Set.InjOn v E) :
    clockOpenState (insert e E) v (v e) = clockOpenState E v (v e) := by
  have heq : (insert e E).filter (fun f => v f < v e) = E.filter (fun f => v f < v e) := by
    ext f
    by_cases hfe : f=e
    · subst f; simp
    · simp [hfe]
  have hi : Set.InjOn v ((insert e E).filter (fun f => v f < v e)) := by
    rw [heq]
    exact hv.mono (Finset.filter_subset _ _)
  unfold clockOpenState
  rw [clockOpenPrefix_sorted _ v _ hi,clockOpenPrefix_sorted E v _ (hv.mono (Finset.filter_subset _ _)),heq]

lemma clockGreedy_insert_unselected {n : ℕ} (E : EdgeSet n) (e : Edge n) (he : e ∉ E)
    (v : Edge n → ℝ) (hv : Set.InjOn v E) (huns : e ∉ clockGreedy (insert e E) v) :
    clockGreedy (insert e E) v = clockGreedy E v := by
  have hh := greedy_remove_unselected (orderFor (insert e E) (fun f => v f.val)) e huns
  have horder := orderFor_subset (insert e E) E (Finset.subset_insert _ _) v hv
  have hf : (orderFor (insert e E) (fun f => v f.val)).filter (fun f => f ≠ e) =
      (orderFor (insert e E) (fun f => v f.val)).filter (fun f => f ∈ E) := by
    apply List.filter_congr
    intro f hf
    have hm := (mem_permLists (insert e E) _).mp (orderFor_mem (insert e E) (fun f => v f.val))
    have hmem : f ∈ insert e E := by rw [←hm.2]; exact List.mem_toFinset.mpr hf
    apply Bool.decide_congr
    simp only [Finset.mem_insert] at hmem
    grind
  rw [hf,←horder] at hh
  exact hh

lemma clockGreedy_insert_endpoint {n : ℕ} (E : EdgeSet n) (e : Edge n) (he : e ∉ E)
    (v : Edge n → ℝ) (hv : Set.InjOn v E) (x : Fin n) (hx : x ∈ e)
    (hmatched : x ∈ covered (clockGreedy E v)) : x ∈ covered (clockGreedy (insert e E) v) := by
  by_cases hacc : e ∈ clockGreedy (insert e E) v
  · simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨e,hacc,hx⟩
  · rw [clockGreedy_insert_unselected E e he v hv hacc]
    exact hmatched

lemma clockGreedy_no_extras {n : ℕ} (B F : EdgeSet n) (x : Fin n) (v : Edge n → ℝ)
    (hv : Set.InjOn v (B ∪ F : EdgeSet n)) (hF : ∀ e ∈ F, x ∈ e)
    (hx : x ∉ covered (clockGreedy (B ∪ F) v)) : clockGreedy (B ∪ F) v = clockGreedy B v := by
  let σ := orderFor (B ∪ F) (fun e => v e.val)
  have hsame : σ.filter (fun e => e ∈ B ∨ e ∈ F) = σ := by
    apply List.filter_eq_self.mpr
    intro e he
    have hm := (mem_permLists (B ∪ F) _).mp (orderFor_mem (B ∪ F) (fun e => v e.val))
    have hmem : e ∈ B ∪ F := by rw [←hm.2]; exact List.mem_toFinset.mpr he
    simpa only [decide_eq_true_eq,Finset.mem_union] using hmem
  have hh := greedy_no_selected_extras σ B F {x} (fun e he => ⟨x,by simp,hF e he⟩)
    (by
      intro y hy
      have hyx : y=x := Finset.mem_singleton.mp hy
      subst y
      rwa [hsame])
  rw [hsame,←orderFor_subset (B ∪ F) B Finset.subset_union_left v (hv.mono (fun e he => Finset.mem_union_left F he))] at hh
  exact hh

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma clockOpenState_full_filter {n : ℕ} (E : EdgeSet n) (v : Edge n → ℝ) (t : ℝ) :
    clockOpenState E v t = (clockGreedy E v).filter (fun e => v e < t) :=
  greedy_filter_time (orderFor E (fun e => v e.val)) v (orderFor_pairwise E v) t

lemma clockOpenState_eq_of_full {n : ℕ} (E F : EdgeSet n) (v : Edge n → ℝ)
    (h : clockGreedy E v = clockGreedy F v) (t : ℝ) : clockOpenState E v t = clockOpenState F v t := by
  rw [clockOpenState_full_filter,clockOpenState_full_filter,h]

lemma reference_early_selected {n : ℕ} (B F : EdgeSet n) (x y : Fin n) (hxy : x ≠ y)
    (hloop : ∀ e ∈ B ∪ F, ¬e.IsDiag) (hF : ∀ e ∈ F, x ∈ e)
    (v : Edge n → ℝ) (hv : Set.InjOn v (insert s(x,y) (B ∪ F) : EdgeSet n))
    (hx : x ∉ covered (clockGreedy (B ∪ F) v))
    (hy : y ∉ covered (clockOpenState B v (v s(x,y)))) :
    s(x,y) ∈ clockGreedy (insert s(x,y) (B ∪ F)) v := by
  have hi := hv.mono (Finset.subset_insert _ _)
  have hsame := clockGreedy_no_extras B F x v hi hF hx
  have hprefix : clockOpenState (insert s(x,y) (B ∪ F)) v (v s(x,y)) = clockOpenState B v (v s(x,y)) := by
    rw [clockOpenState_insert_before (B ∪ F) s(x,y) v hi,clockOpenState_eq_of_full _ _ v hsame]
  apply clock_edge_accepted (insert s(x,y) (B ∪ F)) ?_ v hv s(x,y) (Finset.mem_insert_self _ _) ?_
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · simpa only [Sym2.isDiag_iff_proj_eq] using hxy
    · exact hloop e he
  · rw [hprefix]
    have hxB : x ∉ covered (clockGreedy B v) := by rwa [←hsame]
    have hxPre : x ∉ covered (clockOpenState B v (v s(x,y))) := by
      rw [clockOpenState_full_filter]
      exact fun h => hxB (covered_mono (Finset.filter_subset _ _) h)
    intro a ha
    rcases Sym2.mem_iff.mp ha with rfl | rfl
    · exact hxPre
    · exact hy

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma free_union_iff {n : ℕ} (E D : EdgeSet n) (e : Edge n) :
    free (E ∪ D) e ↔ free E e ∧ free D e := by
  simp only [free,covered_union,Finset.mem_union,not_or]
  aesop

def eligible {n : ℕ} (E : EdgeSet n) (R : Finset (Fin n)) (e : Edge n) : Prop :=
  free E e ∧ ¬(∀ v, v ∈ e → v ∈ R)

lemma late_step_decompose {n : ℕ} (a b : ℝ) (hab : a ≤ b) (S : State n)
    (E D : EdgeSet n) (R : Finset (Fin n)) (hact : S.actual = E ∪ D) (hres : S.reserved = R)
    (e : Edge n) (t : ℝ) (c : Bool) (ht : b ≤ t) :
    (step a b S e t c).actual = E ∪ (if eligible E R e ∧ free D e then insert e D else D) := by
  rw [(step_late_rule a b hab S e t c ht).2,hact,hres,free_union_iff]
  unfold eligible
  have hcond : (free E e ∧ free D e) ∧ ¬(∀ v, v ∈ e → v ∈ R) ↔
      (free E e ∧ ¬(∀ v, v ∈ e → v ∈ R)) ∧ free D e := by tauto
  by_cases hc : (free E e ∧ ¬(∀ v, v ∈ e → v ∈ R)) ∧ free D e
  · rw [if_pos (hcond.mpr hc),if_pos hc,Finset.union_insert]
  · rw [if_neg (mt hcond.mp hc),if_neg hc]

lemma late_fold_decompose {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (hl : ∀ e ∈ l, b ≤ T e) (S : State n)
    (E D : EdgeSet n) (R : Finset (Fin n)) (hact : S.actual = E ∪ D) (hres : S.reserved = R) :
    (l.foldl (fun S e => step a b S e (T e) (C e)) S).reserved = R ∧
    (l.foldl (fun S e => step a b S e (T e) (C e)) S).actual =
      E ∪ ((l.filter (fun e => eligible E R e)).foldl (fun D e => if free D e then insert e D else D) D) := by
  induction l generalizing S D with
  | nil => exact ⟨hres,hact⟩
  | cons e l ih =>
    let D' := if eligible E R e ∧ free D e then insert e D else D
    have hact' := late_step_decompose a b hab S E D R hact hres e (T e) (C e) (hl e (by simp))
    have hres' := (step_late_rule a b hab S e (T e) (C e) (hl e (by simp))).1.trans hres
    have hh := ih (fun f hf => hl f (List.mem_cons_of_mem _ hf)) (step a b S e (T e) (C e)) D' hact' hres'
    by_cases he : eligible E R e
    · simpa [List.filter_cons,D',he] using hh
    · simpa [List.filter_cons,D',he] using hh

lemma late_actual_decompose {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (hl : l.Pairwise (fun e f => T e ≤ T f)) :
    ∃ before after : List (Edge n), before ++ after = l ∧
      (∀ e ∈ before, T e < b) ∧ (∀ e ∈ after, b ≤ T e) ∧
      (runEdges a b T C l).reserved = (runEdges a b T C before).reserved ∧
      (runEdges a b T C l).actual = (runEdges a b T C before).actual ∪
        greedy (after.filter (fun e => eligible (runEdges a b T C before).actual (runEdges a b T C before).reserved e)) := by
  obtain ⟨after,hs,ha⟩ := threshold_split l T hl b
  let before := l.filter (fun e => T e < b)
  let S := runEdges a b T C before
  have heq : runEdges a b T C l = after.foldl (fun S e => step a b S e (T e) (C e)) S := by
    rw [←hs]
    simp only [runEdges,List.foldl_append]
    rfl
  have hh := late_fold_decompose a b hab T C after ha S S.actual ∅ S.reserved (by simp) rfl
  refine ⟨before,after,hs,?_,ha,?_,?_⟩
  · intro e he
    exact of_decide_eq_true (List.mem_filter.mp he).2
  · rw [heq]; exact hh.1
  · rw [heq]; exact hh.2

lemma runEdges_recovery_greedy {n : ℕ} (a b : ℝ) (hab : a ≤ b) (T : Edge n → ℝ) (C : Edge n → Bool)
    (l : List (Edge n)) (hl : l.Pairwise (fun e f => T e ≤ T f)) :
    (runEdges a b T C l).actual.filter (fun e => b ≤ T e) =
      greedy (l.filter fun e => b ≤ T e ∧ eligible
        ((runEdges a b T C l).actual.filter (fun f => T f < b))
        (runEdges a b T C l).reserved e) := by
  obtain ⟨before,after,heq,hbefore,hafter,hres,hact⟩ := late_actual_decompose a b hab T C l hl
  let E := (runEdges a b T C before).actual
  let D := greedy (after.filter (fun e => eligible E (runEdges a b T C before).reserved e))
  have hE (e : Edge n) (he : e ∈ E) : T e < b :=
    hbefore e (List.mem_toFinset.mp (runEdges_seen a b T C before he))
  have hD (e : Edge n) (he : e ∈ D) : b ≤ T e :=
    hafter e (List.mem_of_mem_filter (List.mem_toFinset.mp (greedy_seen _ he)))
  have hpre : (runEdges a b T C l).actual.filter (fun f => T f < b) = E := by
    rw [hact,Finset.filter_union]
    have hEf : E.filter (fun f => T f < b) = E := Finset.filter_eq_self.mpr hE
    have hDf : D.filter (fun f => T f < b) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he ht
      exact not_lt_of_ge (hD e he) ht
    change E.filter _ ∪ D.filter _ = E
    rw [hEf,hDf,Finset.union_empty]
  have hpost : (runEdges a b T C l).actual.filter (fun f => b ≤ T f) = D := by
    rw [hact,Finset.filter_union]
    have hEf : E.filter (fun f => b ≤ T f) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he ht
      exact not_le_of_gt (hE e he) ht
    have hDf : D.filter (fun f => b ≤ T f) = D := Finset.filter_eq_self.mpr hD
    change E.filter _ ∪ D.filter _ = D
    rw [hEf,hDf,Finset.empty_union]
  rw [hpost,hpre,hres,←heq,List.filter_append]
  have hbf : before.filter (fun e => b ≤ T e ∧ eligible E (runEdges a b T C before).reserved e) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    exact fun hh => not_le_of_gt (hbefore e he) (of_decide_eq_true hh).1
  have haf : after.filter (fun e => b ≤ T e ∧ eligible E (runEdges a b T C before).reserved e) =
      after.filter (fun e => eligible E (runEdges a b T C before).reserved e) := by
    apply List.filter_congr
    intro e he
    simp [hafter e he]
  rw [hbf,haf,List.nil_append]


end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma reserved_subset_early {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b) (w : Sample G) :
    (execution G a b w).reserved ⊆ covered (early a (history G b w.1)) := by
  rw [early_history_eq G w.1 a b hab,execution_runEdges_eq,runEdges_reserved a b hab]
  have hh := shadowAt_filter_time G (edgeTimes G w.1) a b hab
  have hT : (fun e : G.edgeSet => edgeTimes G w.1 e.val) = w.1 := funext (edgeTimes_val G w.1)
  rw [hT,←execution_shadow_eq G a b hab w,execution_runEdges_eq] at hh
  rw [hh]
  apply covered_mono
  intro e he
  obtain ⟨he,hte,hcoin⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨he,hte⟩

lemma Y_disjoint_early {n : ℕ} (a : ℝ) (h : History n) : Disjoint (Yset h) (covered (early a h)) := by
  rw [Finset.disjoint_left]
  intro v hvY hvA
  exact (Finset.mem_sdiff.mp hvY).2 (covered_mono (Finset.filter_subset _ _) hvA)

lemma recovery_edge_types {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b)
    (w : Sample G) (e : Edge n) (he : e ∈ recovery G a b w) :
    (∃ x y, e = s(x,y) ∧ x ∈ (execution G a b w).reserved ∧ y ∈ Yset (history G b w.1)) ∨
      (∀ v, v ∈ e → v ∈ Yset (history G b w.1)) := by
  rw [recovery_filter_eq] at he
  obtain ⟨he,ht⟩ := Finset.mem_filter.mp he
  rw [execution_runEdges_eq] at he
  have hh := runEdges_recovery_types a b hab (edgeTimes G w.1) (edgeCoins G w.2) (executionList G w.1)
    (execution_list_order G w.1) (execution_list_loopless G w.1) e he ht
  rw [←execution_runEdges_eq,execution_shadow_eq G a b hab w] at hh
  simpa only [Yset,history,History.accepted,Finset.mem_sdiff,Finset.mem_univ,true_and] using hh

lemma recovery_inter_early {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b) (w : Sample G) :
    ((covered (early a (history G b w.1)) ∩ covered (recovery G a b w)).card:ℝ) = ZXY G a b w := by
  let A := covered (early a (history G b w.1))
  let Y := Yset (history G b w.1)
  let D := recovery G a b w
  let P : Edge n → Prop := fun e => ∃ x y, e = s(x,y) ∧ x ∈ (execution G a b w).reserved ∧ y ∈ Y
  have hD : IsMatching D := matching_subset _ _ (execution_matching G a b hab w) (Finset.filter_subset _ _)
  have hcard : (A ∩ covered D).card = (D.filter P).card := by
    rw [matching_inter_count D hD A,Finset.card_filter]
    apply Finset.sum_congr rfl
    intro e he
    rcases recovery_edge_types G a b hab w e he with hxy | hyy
    · obtain ⟨x,y,rfl,hx,hy⟩ := hxy
      have hP : P s(x,y) := ⟨x,y,rfl,hx,hy⟩
      have hxA : x ∈ A := reserved_subset_early G a b hab w hx
      have hyA : y ∉ A := fun hyA => Finset.disjoint_left.mp (Y_disjoint_early a (history G b w.1)) hy hyA
      rw [if_pos hP,pair_inter_of_cross A x y hxA hyA]
      exact Finset.card_singleton _
    · have hnP : ¬P e := by
        rintro ⟨x,y,hxy,hx,hy⟩
        have hxY := hyy x (by rw [hxy]; simp)
        exact Finset.disjoint_left.mp (Y_disjoint_early a (history G b w.1)) hxY (reserved_subset_early G a b hab w hx)
      rw [if_neg hnP]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvA,hve⟩ := Finset.mem_inter.mp hv
      exact Finset.disjoint_left.mp (Y_disjoint_early a (history G b w.1))
        (hyy v (by simpa only [covered_singleton,Sym2.mem_toFinset] using hve)) hvA
  change ((A ∩ covered D).card:ℝ) = ((D.filter P).card:ℝ)
  exact_mod_cast hcard

lemma recovery_inter_Y {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b) (w : Sample G) :
    ((Yset (history G b w.1) ∩ covered (recovery G a b w)).card:ℝ) = ZXY G a b w + 2*ZYY G a b w := by
  let Y := Yset (history G b w.1)
  let D := recovery G a b w
  let P : Edge n → Prop := fun e => ∃ x y, e = s(x,y) ∧ x ∈ (execution G a b w).reserved ∧ y ∈ Y
  let Q : Edge n → Prop := fun e => ∀ v, v ∈ e → v ∈ Y
  have hD : IsMatching D := matching_subset _ _ (execution_matching G a b hab w) (Finset.filter_subset _ _)
  have hpoint (e : Edge n) (he : e ∈ D) :
      (Y ∩ covered {e}).card = (if P e then 1 else 0)+2*(if Q e then 1 else 0) := by
    rcases recovery_edge_types G a b hab w e he with hxy | hyy
    · obtain ⟨x,y,rfl,hx,hy⟩ := hxy
      have hP : P s(x,y) := ⟨x,y,rfl,hx,hy⟩
      have hxY : x ∉ Y := fun hxY => (Finset.mem_sdiff.mp hxY).2 (execution_reserved_subset G a b hab w hx)
      have hnQ : ¬Q s(x,y) := fun hh => hxY (hh x (by simp))
      have heq : covered {s(x,y)} = covered {s(y,x)} := by rw [Sym2.eq_swap]
      rw [if_pos hP,if_neg hnQ,heq,pair_inter_of_cross Y y x hy hxY]
      simp
    · have hQ : Q e := hyy
      have hnP : ¬P e := by
        rintro ⟨x,y,hxy,hx,hy⟩
        exact (Finset.mem_sdiff.mp (hyy x (by rw [hxy]; simp))).2 (execution_reserved_subset G a b hab w hx)
      rw [if_neg hnP,if_pos hQ]
      have heq : Y ∩ covered {e} = covered {e} := Finset.inter_eq_right.mpr (by
        intro v hv
        exact hyy v (by simpa only [covered_singleton,Sym2.mem_toFinset] using hv))
      rw [heq,covered_singleton,Sym2.card_toFinset_of_not_isDiag e (hD.1 e he)]
  have hsum := Finset.sum_congr rfl hpoint
  rw [←matching_inter_count D hD Y,Finset.sum_add_distrib,←Finset.mul_sum,
    ←Finset.card_filter P D,←Finset.card_filter Q D] at hsum
  change ((Y ∩ covered D).card:ℝ) = ((D.filter P).card:ℝ)+2*((D.filter Q).card:ℝ)
  exact_mod_cast hsum

lemma sum_Nhat {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b) (w : Sample G) :
    (∑ e ∈ early a (history G b w.1), Nhat G a b e w) = ZXY G a b w := by
  have hA : IsMatching (early a (history G b w.1)) :=
    matching_subset _ _ (shadowAt_matching G w.1 b) (Finset.filter_subset _ _)
  have hh := matching_inter_count _ hA (covered (recovery G a b w))
  have hr := congrArg (fun k : ℕ => (k:ℝ)) hh
  simp only [Nat.cast_sum] at hr
  rw [Finset.inter_comm,recovery_inter_early G a b hab w] at hr
  simpa only [Nhat,Finset.inter_comm] using hr.symm

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma matching_filter_cover_disjoint {n : ℕ} (S : EdgeSet n) (hS : IsMatching S)
    (P : Edge n → Prop) : Disjoint (covered (S.filter P)) (covered (S.filter (fun e => ¬P e))) := by
  rw [Finset.disjoint_left]
  intro v hv hw
  obtain ⟨e,he,hve⟩ := (show ∃ e ∈ S.filter P, v ∈ e from by simpa [covered] using hv)
  obtain ⟨f,hf,hvf⟩ := (show ∃ f ∈ S.filter (fun e => ¬P e), v ∈ f from by simpa [covered] using hw)
  obtain ⟨he,hPe⟩ := Finset.mem_filter.mp he
  obtain ⟨hf,hPf⟩ := Finset.mem_filter.mp hf
  exact hS.2 e he f hf (by intro h; exact hPf (h ▸ hPe)) v hve hvf

lemma runEdges_early_reserved_disjoint {n : ℕ} (a b : ℝ) (hab : a ≤ b)
    (T : Edge n → ℝ) (C : Edge n → Bool) (l : List (Edge n))
    (hM : IsMatching (runEdges a b T C l).shadow) :
    Disjoint (covered ((runEdges a b T C l).actual.filter (fun e => T e < b)))
      (runEdges a b T C l).reserved := by
  rw [runEdges_before a b hab,runEdges_reserved a b hab]
  have ht : ∀ e ∈ (runEdges a b T C l).shadow, T e < b := by
    intro e he
    rw [runEdges_shadow a b hab] at he
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp (greedy_seen _ he))).2
  have hf : ((runEdges a b T C l).shadow.filter (fun f => T f < b ∧ ¬ (T f < a ∧ C f = true))) =
      ((runEdges a b T C l).shadow.filter (fun f => ¬ (T f < a ∧ C f = true))) := by
    apply Finset.filter_congr
    intro e he
    simp only [ht e he,true_and]
  rw [hf]
  convert! (matching_filter_cover_disjoint _ hM (fun f => T f < a ∧ C f = true)).symm using 1 <;> (ext v; simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and])

lemma execution_early_reserved_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ)
    (hab : a ≤ b) (w : Sample G) :
    Disjoint (covered ((execution G a b w).actual.filter (fun e => edgeTimes G w.1 e < b)))
      (execution G a b w).reserved := by
  have hM := shadowAt_matching G w.1 b
  rw [←execution_shadow_eq G a b hab w,execution_runEdges_eq] at hM
  have hh := runEdges_early_reserved_disjoint a b hab (edgeTimes G w.1) (edgeCoins G w.2)
    (executionList G w.1) hM
  rw [←execution_runEdges_eq] at hh
  exact hh

lemma eligible_partition_iff {n : ℕ} (E : EdgeSet n) (R Y : Finset (Fin n))
    (hd : Disjoint (covered E) R)
    (hY : ∀ v, v ∈ Y ↔ v ∉ covered E ∧ v ∉ R) (e : Edge n) :
    eligible E R e ↔ (∀ v, v ∈ e → v ∈ Y) ∨ ∃ x y, e = s(x,y) ∧ x ∈ R ∧ y ∈ Y := by
  induction e using Sym2.inductionOn with | hf x y =>
    constructor
    · rintro ⟨hf,hR⟩
      have hx := hf x (by simp)
      have hy := hf y (by simp)
      by_cases hxR : x ∈ R
      · have hyR : y ∉ R := by
          intro hyR
          apply hR
          intro z hz
          rcases Sym2.mem_iff.mp hz with hz | hz
          · exact hz ▸ hxR
          · exact hz ▸ hyR
        exact Or.inr ⟨x,y,rfl,hxR,(hY y).mpr ⟨hy,hyR⟩⟩
      · by_cases hyR : y ∈ R
        · exact Or.inr ⟨y,x,Sym2.eq_swap,hyR,(hY x).mpr ⟨hx,hxR⟩⟩
        · exact Or.inl (by
            intro z hz
            rcases Sym2.mem_iff.mp hz with hz | hz
            · exact hz ▸ (hY x).mpr ⟨hx,hxR⟩
            · exact hz ▸ (hY y).mpr ⟨hy,hyR⟩)
    · rintro (hyy | ⟨u,v,heq,hu,hv⟩)
      · refine ⟨?_,?_⟩
        · intro z hz; exact ((hY z).mp (hyy z hz)).1
        · intro hR; exact ((hY x).mp (hyy x (by simp))).2 (hR x (by simp))
      · refine ⟨?_,?_⟩
        · intro z hz
          rw [heq] at hz
          rcases Sym2.mem_iff.mp hz with hz | hz
          · exact hz ▸ (fun hh => Finset.disjoint_left.mp hd hh hu)
          · exact hz ▸ ((hY v).mp hv).1
        · intro hR
          have hv' : v ∈ s(x,y) := by rw [heq]; simp
          exact ((hY v).mp hv).2 (hR v hv')

def recoveryGraph {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) : EdgeSet n :=
  (graphEdges G).filter fun f => (b ≤ edgeTimes G w.1 f) ∧
    ((∀ v, v ∈ f → v ∈ Yset (history G b w.1)) ∨ ∃ x y, f = s(x,y) ∧
      x ∈ (execution G a b w).reserved ∧ y ∈ Yset (history G b w.1))

lemma recovery_eq_coupledRun {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ)
    (hab : a ≤ b) (w : Sample G) : recovery G a b w = coupledRun G (recoveryGraph G a b w) w := by
  let E := (execution G a b w).actual.filter (fun e => edgeTimes G w.1 e < b)
  let R := (execution G a b w).reserved
  have hpart : covered (shadowAt G w.1 b) = covered E ∪ R := by
    have hh := runEdges_cover_partition a b hab (edgeTimes G w.1) (edgeCoins G w.2) (executionList G w.1)
    rw [←execution_runEdges_eq,execution_shadow_eq G a b hab w] at hh
    exact hh
  have hY (v : Fin n) : v ∈ Yset (history G b w.1) ↔ v ∉ covered E ∧ v ∉ R := by
    simp only [Yset,history,History.accepted,Finset.mem_sdiff,Finset.mem_univ,true_and,hpart,
      Finset.mem_union,not_or]
  have hd := execution_early_reserved_disjoint G a b hab w
  have hgreedy := runEdges_recovery_greedy a b hab (edgeTimes G w.1) (edgeCoins G w.2)
    (executionList G w.1) (execution_list_order G w.1)
  rw [←execution_runEdges_eq,←recovery_filter_eq] at hgreedy
  rw [hgreedy]
  unfold coupledRun
  apply congrArg greedy
  apply List.filter_congr
  intro e he
  have heG : e ∈ graphEdges G := by
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using f.property
  have hi := eligible_partition_iff E R (Yset (history G b w.1)) hd hY e
  change decide (b ≤ edgeTimes G w.1 e ∧ eligible E R e) = decide (e ∈ recoveryGraph G a b w)
  congr 1
  simp only [recoveryGraph,Finset.mem_filter,heG,true_and]
  exact propext (and_congr_right (fun _ => hi))

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma execution_reserved_eq {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b) (w : Sample G) :
    (execution G a b w).reserved = covered ((early a (history G b w.1)).filter
      (fun f => ∃ hf : f ∈ G.edgeSet, w.2 ⟨f,hf⟩ = true)) := by
  have hh := runEdges_reserved a b hab (edgeTimes G w.1) (edgeCoins G w.2) (executionList G w.1)
  rw [←execution_runEdges_eq,execution_shadow_eq G a b hab w] at hh
  rw [hh]
  apply congrArg covered
  rw [←execution_shadow_eq G a b hab w,execution_runEdges_eq]
  rw [early_history_eq G w.1 a b hab]
  have htime := shadowAt_filter_time G (edgeTimes G w.1) a b hab
  have hT : (fun f : G.edgeSet => edgeTimes G w.1 f.val) = w.1 := funext (edgeTimes_val G w.1)
  rw [hT] at htime
  rw [htime]
  ext f
  have hfG : f ∈ shadowAt G w.1 b → f ∈ G.edgeSet := by
    intro hf
    simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using shadowAt_subset_graph G w.1 b hf
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hf,ht,hc⟩
    have hfg := hfG (by rw [←execution_shadow_eq G a b hab w,execution_runEdges_eq]; exact hf)
    exact ⟨⟨by rw [←execution_shadow_eq G a b hab w,execution_runEdges_eq]; exact hf,ht⟩,
      hfg,by simpa only [edgeCoins,dif_pos hfg] using hc⟩
  · rintro ⟨⟨hf,ht⟩,hfg,hc⟩
    refine ⟨?_,ht,?_⟩
    · rw [←execution_runEdges_eq,execution_shadow_eq G a b hab w]; exact hf
    · simpa only [edgeCoins,dif_pos hfg] using hc

lemma reserved_other_split {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b)
    (w : Sample G) (e : G.edgeSet) (he : e.val ∈ early a (history G b w.1)) :
    (execution G a b w).reserved = otherX G a (history G b w.1) e.val w ∪
      (if w.2 e = true then covered {e.val} else ∅) := by
  rw [execution_reserved_eq G a b hab]
  have hsplit : ((early a (history G b w.1)).filter (fun f => ∃ hf : f ∈ G.edgeSet, w.2 ⟨f,hf⟩ = true)) =
      ((early a (history G b w.1)).filter (fun f => f ≠ e.val ∧ ∃ hf : f ∈ G.edgeSet, w.2 ⟨f,hf⟩ = true)) ∪
        (if w.2 e = true then {e.val} else ∅) := by
    ext f
    by_cases hfe : f = e.val
    · subst f
      simp only [Finset.mem_filter,he,true_and,ne_eq,not_true_eq_false,false_and,Finset.mem_union,false_or]
      by_cases hc : w.2 e = true <;> simp [hc]
    · by_cases hc : w.2 e = true <;> simp [Finset.mem_filter,hfe,hc]
  rw [hsplit,covered_union]
  by_cases hc : w.2 e = true <;> simp [hc,otherX,covered]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma otherX_avoids {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b)
    (w : Sample G) (e : Edge n) (he : e ∈ early a (history G b w.1)) :
    ∀ v, v ∈ e → v ∉ otherX G a (history G b w.1) e w := by
  have hM : IsMatching (early a (history G b w.1)) := by
    rw [early_history_eq G w.1 a b hab]
    exact shadowAt_matching G w.1 a
  intro v hv hO
  obtain ⟨f,hf,hvf⟩ := (show ∃ f ∈ (early a (history G b w.1)).filter
      (fun f => f ≠ e ∧ ∃ hf : f ∈ G.edgeSet, w.2 ⟨f,hf⟩ = true), v ∈ f from by
    simpa only [otherX,covered,Finset.mem_filter,Finset.mem_univ,true_and] using hO)
  obtain ⟨hf,hne,hcoin⟩ := Finset.mem_filter.mp hf
  exact hM.2 f hf e he hne v hvf hv

lemma Yset_avoids_early {n : ℕ} (a : ℝ) (h : History n) (e : Edge n) (he : e ∈ early a h) :
    ∀ v, v ∈ e → v ∉ Yset h := by
  intro v hv hY
  exact (Finset.mem_sdiff.mp hY).2 (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,e,(Finset.mem_filter.mp he).1,hv⟩)

lemma recovery_type_avoids {n : ℕ} (e f : Edge n) (O Y : Finset (Fin n))
    (hO : ∀ v, v ∈ e → v ∉ O) (hY : ∀ v, v ∈ e → v ∉ Y)
    (hf : (∀ v, v ∈ f → v ∈ Y) ∨ ∃ x y, f = s(x,y) ∧ x ∈ O ∧ y ∈ Y) :
    ∀ v, v ∈ e → v ∉ f := by
  intro v hv hvf
  rcases hf with hyy | ⟨x,y,rfl,hx,hy⟩
  · exact hY v hv (hyy v hvf)
  · rcases Sym2.mem_iff.mp hvf with h | h
    · exact hO v hv (h ▸ hx)
    · exact hY v hv (h ▸ hy)

lemma background_no_exclusion {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b)
    (w : Sample G) (e : Edge n) (he : e ∈ early a (history G b w.1)) :
    background G a b (history G b w.1) e w = (lateGraph G b w).filter (fun f =>
      (∀ v, v ∈ f → v ∈ Yset (history G b w.1)) ∨
        ∃ x y, f = s(x,y) ∧ x ∈ otherX G a (history G b w.1) e w ∧ y ∈ Yset (history G b w.1)) := by
  rw [background_data_eq]
  change (lateGraph G b w).filter (fun f => (∀ v, v ∈ e → v ∉ f) ∧
    ((∀ v, v ∈ f → v ∈ Yset (history G b w.1)) ∨ ∃ x y, f = s(x,y) ∧
      x ∈ otherX G a (history G b w.1) e w ∧ y ∈ Yset (history G b w.1))) = _
  apply Finset.filter_congr
  intro f hf
  constructor
  · exact And.right
  · intro htype
    exact ⟨recovery_type_avoids e f _ _ (otherX_avoids G a b hab w e he) (Yset_avoids_early a _ e he) htype,htype⟩

lemma recoveryGraph_late {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) :
    recoveryGraph G a b w = (lateGraph G b w).filter (fun f =>
      (∀ v, v ∈ f → v ∈ Yset (history G b w.1)) ∨ ∃ x y, f = s(x,y) ∧
        x ∈ (execution G a b w).reserved ∧ y ∈ Yset (history G b w.1)) := by
  ext f
  change (f ∈ (graphEdges G).filter (fun f => b ≤ edgeTimes G w.1 f ∧
    ((∀ v, v ∈ f → v ∈ Yset (history G b w.1)) ∨ ∃ x y, f = s(x,y) ∧
      x ∈ (execution G a b w).reserved ∧ y ∈ Yset (history G b w.1)))) ↔ _
  have hl : f ∈ lateGraph G b w ↔ f ∈ graphEdges G ∧ ∃ hf : f ∈ G.edgeSet, b ≤ w.1 ⟨f,hf⟩ := Finset.mem_filter
  simp only [Finset.mem_filter,hl]
  by_cases hfg : f ∈ graphEdges G
  · have hfg' : f ∈ G.edgeSet := by simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hfg
    have ht : (∃ hf : f ∈ G.edgeSet, b ≤ w.1 ⟨f,hf⟩) ↔ b ≤ edgeTimes G w.1 f := by
      rw [edgeTimes_val G w.1 (⟨f,hfg'⟩ : G.edgeSet)]
      exact ⟨fun hh => hh.2,fun hh => ⟨hfg',hh⟩⟩
    rw [ht]
    exact ⟨fun hh => ⟨⟨hh.1,hh.2.1⟩,hh.2.2⟩,fun hh => ⟨hh.1.1,hh.1.2,hh.2⟩⟩
  · simp only [hfg,false_and]

lemma recoveryGraph_coin {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (hab : a ≤ b)
    (w : Sample G) (e : G.edgeSet) (he : e.val ∈ early a (history G b w.1)) :
    recoveryGraph G a b w = if w.2 e = true then augmented G a b (history G b w.1) e.val w
      else background G a b (history G b w.1) e.val w := by
  have hres := reserved_other_split G a b hab w e he
  have hB := background_no_exclusion G a b hab w e.val he
  rw [recoveryGraph_late]
  by_cases hc : w.2 e = true
  · rw [if_pos hc]
    rw [if_pos hc] at hres
    have hA := augmented_data_eq G a b (history G b w.1) e.val w
    rw [hA]
    change _ = backgroundFromData (history G b w.1) e.val (backgroundData G a b (history G b w.1) e.val w) ∪
      (lateGraph G b w).filter (fun f => ∃ x y, f = s(x,y) ∧ x ∈ e.val ∧ y ∈ Yset (history G b w.1))
    rw [←background_data_eq,hB]
    ext f
    simp only [Finset.mem_filter,Finset.mem_union,hres]
    have hcross : (∃ x y, f = s(x,y) ∧ x ∈ otherX G a (history G b w.1) e.val w ∪ covered {e.val} ∧ y ∈ Yset (history G b w.1)) ↔
      (∃ x y, f = s(x,y) ∧ x ∈ otherX G a (history G b w.1) e.val w ∧ y ∈ Yset (history G b w.1)) ∨
      (∃ x y, f = s(x,y) ∧ x ∈ e.val ∧ y ∈ Yset (history G b w.1)) := by
      constructor
      · rintro ⟨x,y,hxy,hx,hy⟩
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Or.inl ⟨x,y,hxy,hx,hy⟩
        · exact Or.inr ⟨x,y,hxy,by simpa only [covered_singleton,Sym2.mem_toFinset] using hx,hy⟩
      · rintro (⟨x,y,hxy,hx,hy⟩ | ⟨x,y,hxy,hx,hy⟩)
        · exact ⟨x,y,hxy,Finset.mem_union_left _ hx,hy⟩
        · exact ⟨x,y,hxy,Finset.mem_union_right _ (by simpa only [covered_singleton,Sym2.mem_toFinset] using hx),hy⟩
    simp only [Finset.mem_union] at hcross
    rw [hcross]
    constructor
    · rintro ⟨hL,hyy | hO | hE⟩
      · exact Or.inl ⟨hL,Or.inl hyy⟩
      · exact Or.inl ⟨hL,Or.inr hO⟩
      · exact Or.inr ⟨hL,hE⟩
    · rintro (⟨hL,hyy | hO⟩ | ⟨hL,hE⟩)
      · exact ⟨hL,Or.inl hyy⟩
      · exact ⟨hL,Or.inr (Or.inl hO)⟩
      · exact ⟨hL,Or.inr (Or.inr hE)⟩
  · rw [if_neg hc]
    rw [if_neg hc,Finset.union_empty] at hres
    rw [hB,hres]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma matchTime_free_vertex {n : ℕ} (b : ℝ) (h : History n) (v : Fin n)
    (hv : v ∉ covered h.accepted) : matchTime b h v = b := by
  apply le_antisymm
  · exact ((le_matchTime_iff (matchTime b h v) b h v).mp le_rfl).1
  · apply (le_matchTime_iff b b h v).mpr
    refine ⟨le_rfl,?_⟩
    intro e he hve
    exact (hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,he,hve⟩)).elim

lemma matchTime_accepted_vertex {n : ℕ} (b : ℝ) (h : History n) (hm : IsMatching h.accepted)
    (e : Edge n) (he : e ∈ h.accepted) (hte : h.time e ≤ b) (v : Fin n) (hv : v ∈ e) :
    matchTime b h v = h.time e := by
  apply le_antisymm
  · exact ((le_matchTime_iff (matchTime b h v) b h v).mp le_rfl).2 e he hv
  · apply (le_matchTime_iff (h.time e) b h v).mpr
    refine ⟨hte,?_⟩
    intro f hf hvf
    have hfe : f = e := by
      by_contra hne
      exact hm.2 f hf e he hne v hvf hv
    rw [hfe]

lemma lowerTime_cross_edge {n : ℕ} (b : ℝ) (h : History n) (hm : IsMatching h.accepted)
    (e : Edge n) (he : e ∈ h.accepted) (hte : h.time e ≤ b)
    (x y : Fin n) (hx : x ∈ e) (hy : y ∈ Yset h) :
    lowerTime b h s(x,y) = h.time e := by
  apply le_antisymm
  · have hh := (le_lowerTime_iff (lowerTime b h s(x,y)) b h s(x,y)).mp le_rfl
    exact hh.2 x (by simp) e he hx
  · apply (le_lowerTime_iff (h.time e) b h s(x,y)).mpr
    refine ⟨hte,?_⟩
    intro v hv f hf hvf
    rcases Sym2.mem_iff.mp hv with hv | hv
    · have hfe : f = e := by
        by_contra hne
        exact hm.2 f hf e he hne x (hv ▸ hvf) hx
      rw [hfe]
    · exact ((Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,f,hf,hv ▸ hvf⟩)).elim

lemma cross_edge_unaccepted {n : ℕ} (h : History n) (x y : Fin n) (hy : y ∈ Yset h) :
    s(x,y) ∉ h.accepted := by
  intro he
  exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,s(x,y),he,by simp⟩)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma clockGreedy_congr {n : ℕ} (E : EdgeSet n) (v w : Edge n → ℝ)
    (h : ∀ e ∈ E, v e = w e) : clockGreedy E v = clockGreedy E w := by
  apply congrArg (fun t : E → ℝ => greedy (orderFor E t))
  funext e
  exact h e.val e.property

lemma clockOpenState_congr {n : ℕ} (E : EdgeSet n) (v w : Edge n → ℝ)
    (h : ∀ e ∈ E, v e = w e) (t : ℝ) : clockOpenState E v t = clockOpenState E w t := by
  have heq : (fun e : E => v e.val) = (fun e : E => w e.val) := funext (fun e => h e.val e.property)
  unfold clockOpenState clockOpenPrefix
  rw [heq]
  congr 1
  apply List.filter_congr
  intro e he
  have hm := (mem_permLists E _).mp (orderFor_mem E (fun e => w e.val))
  have heE : e ∈ E := by rw [←hm.2]; exact List.mem_toFinset.mpr he
  rw [h e heE]

lemma clockOpenState_update_ignored {n : ℕ} (E : EdgeSet n) (e : Edge n) (he : e ∉ E)
    (v : Edge n → ℝ) (u t : ℝ) : clockOpenState E (Function.update v e u) t = clockOpenState E v t := by
  apply clockOpenState_congr
  intro f hf
  have hne : f ≠ e := fun hfe => he (hfe ▸ hf)
  exact Function.update_of_ne hne u v

lemma history_before_match_free {n : ℕ} (h : History n) (y : Fin n) (t : ℝ)
    (ht : t ≤ matchTime 1 h y) : y ∉ covered (h.accepted.filter (fun e => h.time e < t)) := by
  intro hy
  obtain ⟨e,he,hye⟩ : ∃ e ∈ h.accepted.filter (fun e => h.time e < t), y ∈ e := by simpa [covered] using hy
  have hm := Finset.mem_filter.mp he
  have hh := ((le_matchTime_iff (matchTime 1 h y) 1 h y).mp le_rfl).2 e hm.1 hye
  exact (not_lt_of_ge (ht.trans hh)) hm.2

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma measurable_clockGreedy {n : ℕ} (E : EdgeSet n) : Measurable (clockGreedy E) := by
  letI : MeasurableSpace (Equiv.Perm (Fin (Fintype.card E))) := ⊤
  letI : MeasurableSingletonClass (Equiv.Perm (Fin (Fintype.card E))) := ⟨fun _ => trivial⟩
  let enum := (Fintype.equivFin E).symm
  have hs : Measurable (fun t : Edge n → ℝ => Tuple.sort (fun i => t (enum i).val)) := by
    apply measurable_to_countable'
    intro π
    exact (sort_fiber_measurable π).preimage (measurable_pi_iff.mpr (fun i => measurable_pi_apply (enum i).val))
  exact (measurable_of_finite (fun π => greedy (enumerationOrder E enum π))).comp hs

lemma update_injective_ae {n : ℕ} (E : EdgeSet n) (e : Edge n) (he : e ∉ E)
    (v : Edge n → ℝ) (hv : Set.InjOn v E) (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ u ∂μ, Set.InjOn (Function.update v e u) (insert e E : EdgeSet n) := by
  have hall : ∀ᵐ u ∂μ, ∀ f : Edge n, u ≠ v f := ae_all_iff.mpr (fun f => by
    simp only [ae_iff,not_not,Set.setOf_eq_eq_singleton,measure_singleton])
  filter_upwards [hall] with u hu
  intro f hf g hg hfg
  by_cases hfe : f=e
  · subst f
    by_cases hge : g=e
    · exact hge.symm
    · simp only [Function.update_self,Function.update_of_ne hge] at hfg
      exact (hu g hfg).elim
  · by_cases hge : g=e
    · subst g
      simp only [Function.update_self,Function.update_of_ne hfe] at hfg
      exact (hu f hfg.symm).elim
    · have hfE : f ∈ E := (Finset.mem_insert.mp hf).resolve_left hfe
      have hgE : g ∈ E := (Finset.mem_insert.mp hg).resolve_left hge
      simp only [Function.update_of_ne hfe,Function.update_of_ne hge] at hfg
      exact hv hfE hgE hfg

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def referenceScore {n : ℕ} (x y : Fin n) (q : ℝ) (C C0 : EdgeSet n) : ℝ :=
  q*(3*count {x} C+2*count {y} C)+(1-q)*(3*count {x} C0+2*count {y} C0)

lemma referenceScore_xmatched {n : ℕ} (x y : Fin n) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (C C0 : EdgeSet n) (hx : x ∈ covered C) (hx0 : x ∈ covered C0) :
    3 ≤ referenceScore x y q C C0 := by
  simp only [referenceScore,count_singleton,hx,hx0,↓reduceIte]
  split_ifs <;> nlinarith

lemma referenceScore_ymatched {n : ℕ} (x y : Fin n) (q : ℝ) (hq : 0 ≤ q)
    (C C0 : EdgeSet n) (hx0 : x ∉ covered C0) (hy : y ∈ covered C) (hy0 : y ∈ covered C0)
    (u τ : ℝ) (hearly : u < τ → x ∈ covered C) :
    2+3*q*(if u < τ then 1 else 0) ≤ referenceScore x y q C C0 := by
  simp only [referenceScore,count_singleton,hx0,hy,hy0,↓reduceIte]
  by_cases hu : u < τ
  · have hx := hearly hu
    simp [hu,hx]
    ring_nf
    exact le_rfl
  · simp only [hu,↓reduceIte,mul_zero,add_zero]
    split_ifs <;> nlinarith

lemma referenceScore_unmatched_selected {n : ℕ} (x y : Fin n) (q : ℝ)
    (C C0 : EdgeSet n) (hx0 : x ∉ covered C0) (hy0 : y ∉ covered C0)
    (hx : x ∈ covered C) (hy : y ∈ covered C) : referenceScore x y q C C0 = 5*q := by
  simp only [referenceScore,count_singleton,hx0,hy0,hx,hy,↓reduceIte]
  ring

lemma uniform_before_real (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (volume.restrict (Set.Icc (0:ℝ) 1)).real (Set.Iio τ) = τ := by
  have hset : Set.Iio τ ∩ Set.Icc (0:ℝ) 1 = Set.Ico 0 τ := by
    ext u
    simp only [Set.mem_inter_iff,Set.mem_Iio,Set.mem_Icc,Set.mem_Ico]
    constructor
    · exact fun h => ⟨h.2.1,h.1⟩
    · intro h
      exact ⟨h.2,h.1,h.2.le.trans hτ1⟩
  rw [Measure.real,Measure.restrict_apply measurableSet_Iio,hset,Real.volume_Ico,sub_zero,ENNReal.toReal_ofReal hτ]

lemma uniform_before_integral (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (∫ u, (if u < τ then (1:ℝ) else 0) ∂volume.restrict (Set.Icc (0:ℝ) 1)) = τ := by
  have heq : (fun u : ℝ => if u < τ then (1:ℝ) else 0) = (Set.Iio τ).indicator (fun _ => (1:ℝ)) := by
    ext u
    simp only [Set.indicator_apply,Set.mem_Iio]
  rw [heq,integral_indicator measurableSet_Iio,integral_const]
  simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one] using uniform_before_real τ hτ hτ1

lemma reference_threshold_integral (q τ : ℝ) (hq : (1/3:ℝ) ≤ q) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (f : ℝ → ℝ) (hf : Integrable f (volume.restrict (Set.Icc (0:ℝ) 1)))
    (hbound : ∀ᵐ u ∂volume.restrict (Set.Icc (0:ℝ) 1), 2+3*q*(if u < τ then 1 else 0) ≤ f u) :
    2+τ ≤ ∫ u, f u ∂volume.restrict (Set.Icc (0:ℝ) 1) := by
  let μ := volume.restrict (Set.Icc (0:ℝ) 1)
  haveI : IsProbabilityMeasure μ := ⟨by dsimp [μ]; simp⟩
  have hi : Integrable (fun u : ℝ => if u < τ then (1:ℝ) else 0) μ := by
    have hS : MeasurableSet {u : ℝ | u < τ} := measurableSet_lt measurable_id measurable_const
    convert! (integrable_const (1:ℝ) (μ:=μ)).indicator hS using 1
  have hsum : Integrable (fun u : ℝ => 2+3*q*(if u < τ then 1 else 0)) μ := (integrable_const 2).add (hi.const_mul (3*q))
  have hh := integral_mono_ae hsum hf hbound
  rw [integral_add (integrable_const 2) (hi.const_mul (3*q)),integral_const_mul,uniform_before_integral τ hτ hτ1] at hh
  have hc : (∫ _ : ℝ, (2:ℝ) ∂μ) = 2 := by simp
  change (∫ _ : ℝ, (2:ℝ) ∂μ)+3*q*τ ≤ _ at hh
  rw [hc] at hh
  nlinarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma reference_clock_average {n : ℕ} (B F : EdgeSet n) (x y : Fin n) (hxy : x ≠ y)
    (hloop : ∀ e ∈ B ∪ F, ¬e.IsDiag) (hF : ∀ e ∈ F, x ∈ e)
    (href : s(x,y) ∉ B ∪ F) (v : Edge n → ℝ) (hv : Set.InjOn v (B ∪ F : EdgeSet n))
    (h : History n) (hfull : clockGreedy B v = h.accepted)
    (hcut : ∀ t, clockOpenState B v t = h.accepted.filter (fun e => h.time e < t))
    (hτ0 : 0 ≤ matchTime 1 h y) (q : ℝ) (hq : (3/5:ℝ) ≤ q) (hq1 : q ≤ 1) :
    2+matchTime 1 h y ≤ ∫ u, referenceScore x y q
      (clockGreedy (insert s(x,y) (B ∪ F)) (Function.update v s(x,y) u))
      (clockGreedy (B ∪ F) (Function.update v s(x,y) u))
      ∂volume.restrict (Set.Icc (0:ℝ) 1) := by
  let μ := volume.restrict (Set.Icc (0:ℝ) 1)
  haveI : IsProbabilityMeasure μ := ⟨by dsimp [μ]; simp⟩
  let C := fun u => clockGreedy (insert s(x,y) (B ∪ F)) (Function.update v s(x,y) u)
  let C0 := fun u => clockGreedy (B ∪ F) (Function.update v s(x,y) u)
  let f := fun u => referenceScore x y q (C u) (C0 u)
  have hi : Integrable f μ := integrable_finite_comp μ (fun u => (C u,C0 u))
    (((measurable_clockGreedy _).comp (measurable_update v)).prodMk ((measurable_clockGreedy _).comp (measurable_update v)))
    (fun z => referenceScore x y q z.1 z.2)
  have hreg := update_injective_ae (B ∪ F) s(x,y) href v hv μ
  have hC0 (u : ℝ) : C0 u = clockGreedy (B ∪ F) v := clockGreedy_update_ignored _ _ href v u
  have hnotB : s(x,y) ∉ B := fun he => href (Finset.mem_union_left F he)
  have hbase (u t : ℝ) : clockOpenState B (Function.update v s(x,y) u) t =
      h.accepted.filter (fun e => h.time e < t) := by
    rw [clockOpenState_update_ignored B s(x,y) hnotB v u t,hcut t]
  have hτ1 : matchTime 1 h y ≤ 1 := ((le_matchTime_iff (matchTime 1 h y) 1 h y).mp le_rfl).1
  by_cases hx0 : x ∈ covered (clockGreedy (B ∪ F) v)
  · have hb : ∀ᵐ u ∂μ, 3 ≤ f u := by
      filter_upwards [hreg] with u hu
      have hx0' : x ∈ covered (C0 u) := by rw [hC0 u]; exact hx0
      have hx : x ∈ covered (C u) := clockGreedy_insert_endpoint _ _ href _ (hu.mono (Finset.subset_insert _ _)) x (by simp) hx0'
      exact referenceScore_xmatched x y q (by linarith) hq1 _ _ hx hx0'
    have hh := integral_mono_ae (integrable_const (3:ℝ)) hi hb
    have hc : (∫ _ : ℝ, (3:ℝ) ∂μ) = 3 := by simp
    rw [hc] at hh
    exact (by linarith : 2+matchTime 1 h y ≤ 3).trans hh
  · have hsame := (clockGreedy_no_extras B F x v hv hF hx0).trans hfull
    have hx0' (u : ℝ) : x ∉ covered (C0 u) := by rw [hC0 u]; exact hx0
    have hC0h (u : ℝ) : C0 u = h.accepted := (hC0 u).trans hsame
    have hearly (u : ℝ) (hu : Set.InjOn (Function.update v s(x,y) u) (insert s(x,y) (B ∪ F) : EdgeSet n))
        (hut : u ≤ matchTime 1 h y) : s(x,y) ∈ C u := by
      apply reference_early_selected B F x y hxy hloop hF _ hu (hx0' u)
      rw [Function.update_self,hbase u u]
      exact history_before_match_free h y u hut
    by_cases hy : y ∈ covered h.accepted
    · apply reference_threshold_integral q (matchTime 1 h y) (by linarith) hτ0 hτ1 f hi
      filter_upwards [hreg] with u hu
      have hy0 : y ∈ covered (C0 u) := by rw [hC0h u]; exact hy
      have hyC : y ∈ covered (C u) := clockGreedy_insert_endpoint _ _ href _ (hu.mono (Finset.subset_insert _ _)) y (by simp) hy0
      apply referenceScore_ymatched x y q (by linarith) _ _ (hx0' u) hyC hy0 u (matchTime 1 h y)
      intro hut
      have hacc := hearly u hu hut.le
      simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨s(x,y),hacc,by simp⟩
    · have hτ : matchTime 1 h y = 1 := matchTime_free_vertex 1 h y hy
      have hlt : ∀ᵐ u ∂μ, u < 1 := by
        filter_upwards [ae_restrict_mem measurableSet_Icc,
          (show ∀ᵐ u ∂μ, u ≠ 1 from by simp only [μ,ae_iff,not_not,Set.setOf_eq_eq_singleton,measure_singleton])] with u hu hne
        exact lt_of_le_of_ne hu.2 hne
      have hb : ∀ᵐ u ∂μ, 3 ≤ f u := by
        filter_upwards [hreg,hlt] with u hu hut
        have hacc := hearly u hu (by rw [hτ]; exact hut.le)
        have hxC : x ∈ covered (C u) := by simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨s(x,y),hacc,by simp⟩
        have hyC : y ∈ covered (C u) := by simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨s(x,y),hacc,by simp⟩
        have hy0 : y ∉ covered (C0 u) := by rw [hC0h u]; exact hy
        have heq := referenceScore_unmatched_selected x y q (C u) (C0 u) (hx0' u) hy0 hxC hyC
        change 3 ≤ referenceScore x y q (C u) (C0 u)
        rw [heq]
        linarith
      have hh := integral_mono_ae (integrable_const (3:ℝ)) hi hb
      have hc : (∫ _ : ℝ, (3:ℝ) ∂μ) = 3 := by simp
      rw [hc] at hh
      rw [hτ]
      norm_num
      exact hh

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma finite_pi_scalars {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : ι → ENNReal)
    [∀ i, SigmaFinite (c i • μ i)] :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  apply (Measure.pi_eq (μ:=fun i => c i • μ i) _)
  intro s hs
  simp only [Measure.smul_apply,smul_eq_mul,Measure.pi_pi,Finset.prod_mul_distrib]

lemma finite_pi_projection {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (A : Finset ι) :
    (Measure.pi μ).map (fun t : ι → ℝ => fun i : A => t i.val) =
      (∏ i : {i : ι // i ∉ A}, μ i.val Set.univ) • Measure.pi (fun i : A => μ i.val) := by
  letI : Fintype {i : ι // i ∈ A} := Subtype.fintype _
  have hp := measurePreserving_piEquivPiSubtypeProd μ (fun i => i ∈ A)
  have hmap : (Measure.pi μ).map (fun t : ι → ℝ => fun i : A => t i.val) =
      ((Measure.pi (fun i : A => μ i.val)).prod (Measure.pi (fun i : {i : ι // i ∉ A} => μ i.val))).map Prod.fst := by
    rw [←hp.map_eq,Measure.map_map measurable_fst hp.measurable]
    rfl
  rw [hmap,Measure.map_fst_prod]
  congr 1
  · exact Measure.pi_univ _
  · congr 2
    exact Subsingleton.elim _ _

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def fillCoordinates {ι : Type*} [Fintype ι] (A : Finset ι)
    (z : (A → ℝ) × (ι → ℝ)) : ι → ℝ :=
  fun i => if hi : i ∈ A then z.1 ⟨i,hi⟩ else z.2 i

def fillLaw {ι : Type*} [Fintype ι] (A : Finset ι) (μ : A → Measure ℝ) (ν : ι → Measure ℝ) : ι → Measure ℝ :=
  fun i => if hi : i ∈ A then μ ⟨i,hi⟩ else ν i

lemma fillCoordinates_preserving {ι : Type*} [Fintype ι] (A : Finset ι)
    (μ : A → Measure ℝ) (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    MeasurePreserving (fillCoordinates A) ((Measure.pi μ).prod (Measure.pi ν)) (Measure.pi (fillLaw A μ ν)) := by
  letI : Fintype {i : ι // i ∈ A} := Subtype.fintype _
  let ρ := fillLaw A μ ν
  haveI (i : ι) : IsProbabilityMeasure (ρ i) := by
    dsimp only [ρ,fillLaw]
    split_ifs <;> infer_instance
  have hs := measurePreserving_piEquivPiSubtypeProd ρ (fun i => i ∈ A)
  have hinv := MeasurePreserving.symm (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun i => i ∈ A)) hs
  have hρA : Measure.pi (fun i : {i : ι // i ∈ A} => ρ i.val) = Measure.pi μ := by
    congr 1
    funext i
    simp [ρ,fillLaw,i.property]
  have hρC : Measure.pi (fun i : {i : ι // i ∉ A} => ρ i.val) = Measure.pi (fun i : {i : ι // i ∉ A} => ν i.val) := by
    congr 1
    funext i
    simp [ρ,fillLaw,i.property]
  rw [hρA,hρC] at hinv
  have hproj := (measurePreserving_snd (μ:=Measure.pi (fun i : {i : ι // i ∈ A} => ν i.val))
    (ν:=Measure.pi (fun i : {i : ι // i ∉ A} => ν i.val))).comp
    (measurePreserving_piEquivPiSubtypeProd ν (fun i => i ∈ A))
  have hh := hinv.comp ((MeasurePreserving.id (Measure.pi μ)).prod hproj)
  convert! hh using 1
  congr 2
  exact Subsingleton.elim _ _

lemma fillCoordinates_on {ι : Type*} [Fintype ι] (A : Finset ι)
    (z : (A → ℝ) × (ι → ℝ)) (i : A) : fillCoordinates A z i.val = z.1 i := by
  simp [fillCoordinates,i.property]

lemma fillCoordinates_off {ι : Type*} [Fintype ι] (A : Finset ι)
    (z : (A → ℝ) × (ι → ℝ)) (i : ι) (hi : i ∉ A) : fillCoordinates A z i = z.2 i := by
  simp [fillCoordinates,hi]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section
set_option maxHeartbeats 2000000

lemma full_resampling_preserving {n : ℕ} (G : SimpleGraph (Fin n)) :
    MeasurePreserving (fun w : Times G × Times G => residualSample G 1 (history G 1 w.1) w.2)
      ((arrivalLaw G).prod (arrivalLaw G)) (arrivalLaw G) := by
  haveI := arrival_probability G
  have hm : Measurable (fun w : Times G × Times G => residualSample G 1 (history G 1 w.1) w.2) := by
    have hpair : Measurable (fun w : Times G × Times G => (history G 1 w.1,w.2)) :=
      ((measurable_history G 1).comp measurable_fst).prodMk measurable_snd
    have hr := (measurable_residualSample G 1).comp hpair
    convert! hr using 1
  refine ⟨hm,?_⟩
  have hh := congrArg (fun μ : Measure (History n × Times G) => μ.map Prod.snd)
    (history_resampling_law_le G 1 (by norm_num) le_rfl)
  have hq : Measurable (fun w : Times G × Times G => (history G 1 w.1,residualSample G 1 (history G 1 w.1) w.2)) := by
    convert! (((measurable_history G 1).comp measurable_fst).prodMk hm) using 1
  have hg : Measurable (fun t : Times G => (history G 1 t,t)) := by
    convert! (measurable_history G 1).prodMk measurable_id using 1
  rw [Measure.map_map measurable_snd hq,Measure.map_map measurable_snd hg] at hh
  simp only [Function.comp_def] at hh
  change _ = (arrivalLaw G).map id at hh
  rw [Measure.map_id] at hh
  exact hh

lemma full_history_integral_sampled {n : ℕ} (G : SimpleGraph (Fin n))
    (f : Times G → ℝ) (hf : Measurable f) (hi : Integrable f (arrivalLaw G)) :
    (∫ t, f t ∂arrivalLaw G) = ∫ h, ∫ t, f t ∂sampledResidualLaw G 1 h ∂historyLaw G 1 := by
  haveI := arrival_probability G
  have hp := full_resampling_preserving G
  have hi' := hp.integrable_comp_of_integrable hi
  have hsplit := integral_prod _ hi'
  have hmean : Measurable (fun h : History n => ∫ u, f (residualSample G 1 h u) ∂arrivalLaw G) := by
    exact (hf.comp (measurable_residualSample G 1)).stronglyMeasurable.integral_prod_right'.measurable
  have hm (h : History n) : (∫ t, f t ∂sampledResidualLaw G 1 h) = ∫ u, f (residualSample G 1 h u) ∂arrivalLaw G := by
    rw [sampledResidualLaw]
    exact integral_map ((measurable_residualSample G 1).comp measurable_prodMk_left).aemeasurable hf.aestronglyMeasurable
  simp_rw [hm]
  rw [historyLaw,integral_map (measurable_history G 1).aemeasurable hmean.aestronglyMeasurable]
  calc
    _ = ∫ w, f (residualSample G 1 (history G 1 w.1) w.2) ∂(arrivalLaw G).prod (arrivalLaw G) :=
      by
        have hh := integral_map hp.measurable.aemeasurable (hf.aestronglyMeasurable (μ:=((arrivalLaw G).prod (arrivalLaw G)).map _))
        rw [hp.map_eq] at hh
        exact hh
    _ = _ := hsplit

lemma full_history_integral {n : ℕ} (G : SimpleGraph (Fin n))
    (f : Times G → ℝ) (hf : Measurable f) (hi : Integrable f (arrivalLaw G)) :
    (∫ t, f t ∂arrivalLaw G) = ∫ h, ∫ t, f t ∂residualLaw G 1 h ∂historyLaw G 1 := by
  rw [full_history_integral_sampled G f hf hi]
  apply integral_congr_ae
  filter_upwards [full_history_residual_eq G] with h hh
  rw [hh]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

def refVertices {n : ℕ} (M : EdgeSet n) (a : ℝ) (h : History n) : Finset (Fin n) :=
  (early a h).biUnion (references M h)

lemma references_disjoint {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (a : ℝ) (h : History n)
    (hB : IsMatching h.accepted) (e : Edge n) (he : e ∈ early a h)
    (f : Edge n) (hf : f ∈ early a h) (hne : e ≠ f) : Disjoint (references M h e) (references M h f) := by
  rw [Finset.disjoint_left]
  intro y hye hyf
  obtain ⟨_,x,hxe,hxy⟩ := Finset.mem_filter.mp hye
  obtain ⟨_,z,hzf,hzy⟩ := Finset.mem_filter.mp hyf
  have hopt : s(x,y) = s(z,y) := by
    by_contra hn
    exact hM.2 _ hxy _ hzy hn y (by simp) (by simp)
  have hxz : x = z := by
    rcases Sym2.eq_iff.mp hopt with hh | hh
    · exact hh.1
    · exact hh.1.trans hh.2
  exact hB.2 e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 hne x hxe (hxz ▸ hzf)

lemma refVertices_subset_Y {n : ℕ} (M : EdgeSet n) (a : ℝ) (h : History n) :
    refVertices M a h ⊆ Yset h := by
  intro y hy
  obtain ⟨e,he,hy⟩ := Finset.mem_biUnion.mp hy
  exact (Finset.mem_filter.mp hy).1

lemma refVertices_eq {n : ℕ} (M : EdgeSet n) (a : ℝ) (h : History n) :
    refVertices M a h = Yset h ∩ covered (M1Y M a h) := by
  ext y
  constructor
  · intro hy
    obtain ⟨e,he,hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨hyY,x,hxe,hxyM⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_inter.mpr ⟨hyY,?_⟩
    have hxA : x ∈ covered (early a h) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,he,hxe⟩
    have hxy : s(x,y) ∈ M1Y M a h := Finset.mem_filter.mpr ⟨hxyM,x,y,rfl,hxA,hyY⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,s(x,y),hxy,by simp⟩
  · intro hy
    obtain ⟨hyY,hyCov⟩ := Finset.mem_inter.mp hy
    obtain ⟨f,hf,hyf⟩ := (Finset.mem_filter.mp hyCov).2
    obtain ⟨hfM,x,z,hfxz,hxA,hzY⟩ := Finset.mem_filter.mp hf
    have hxB : x ∈ covered h.accepted := covered_mono (Finset.filter_subset _ _) hxA
    have hxy : y ≠ x := by
      intro hh
      apply (Finset.mem_sdiff.mp hyY).2
      exact hh ▸ hxB
    have hyz : y = z := by
      rw [hfxz,Sym2.mem_iff] at hyf
      exact hyf.resolve_left hxy
    subst z
    obtain ⟨e,he,hxe⟩ := (Finset.mem_filter.mp hxA).2
    apply Finset.mem_biUnion.mpr
    refine ⟨e,he,Finset.mem_filter.mpr ⟨hyY,x,hxe,?_⟩⟩
    exact hfxz ▸ hfM

lemma M1Y_cross {n : ℕ} (M : EdgeSet n) (a : ℝ) (h : History n) (e : Edge n) (he : e ∈ M1Y M a h) :
    ∃ x y, e = s(x,y) ∧ x ∈ Yset h ∧ y ∉ Yset h := by
  obtain ⟨_,x,y,rfl,hxA,hyY⟩ := Finset.mem_filter.mp he
  refine ⟨y,x,Sym2.eq_swap,hyY,?_⟩
  intro hxY
  exact (Finset.mem_sdiff.mp hxY).2 (covered_mono (Finset.filter_subset _ _) hxA)

lemma reference_union_count {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (a : ℝ) (h : History n)
    (hB : IsMatching h.accepted) (Q : Finset (Fin n)) :
    (refVertices M a h ∩ Q).card = ∑ e ∈ early a h, (references M h e ∩ Q).card := by
  rw [refVertices,Finset.biUnion_inter,Finset.card_biUnion]
  intro e he f hf hne
  change Disjoint (references M h e ∩ Q) (references M h f ∩ Q)
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact Finset.disjoint_left.mp (references_disjoint M hM a h hB e he f hf hne)
    (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv').1

lemma reference_card_sum {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (a : ℝ) (h : History n)
    (hB : IsMatching h.accepted) :
    (∑ e ∈ early a h, (references M h e).card) = (M1Y M a h).card := by
  have hh := reference_union_count M hM a h hB Finset.univ
  simp only [Finset.inter_univ] at hh
  rw [refVertices_eq] at hh
  rw [matching_cross_count (M1Y M a h) (matching_subset M _ hM (Finset.filter_subset _ _))
    (Yset h) (M1Y_cross M a h)] at hh
  exact hh.symm

lemma refVertices_disjoint_MYY {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (a : ℝ) (h : History n) :
    Disjoint (refVertices M a h) (covered (MYY M h)) := by
  rw [Finset.disjoint_left]
  intro y hyr hyM
  rw [refVertices_eq] at hyr
  obtain ⟨hyY,hyC⟩ := Finset.mem_inter.mp hyr
  obtain ⟨e,he,hye⟩ := (Finset.mem_filter.mp hyC).2
  obtain ⟨f,hf,hyf⟩ := (Finset.mem_filter.mp hyM).2
  have heM := (Finset.mem_filter.mp he).1
  have hfM := (Finset.mem_filter.mp hf).1
  have hef : e ≠ f := by
    intro hh
    obtain ⟨_,x,z,heq,hxA,hzY⟩ := Finset.mem_filter.mp he
    have hxE : x ∈ e := by rw [heq]; simp
    have hxY := (Finset.mem_filter.mp hf).2 x (hh ▸ hxE)
    exact (Finset.mem_sdiff.mp hxY).2 (covered_mono (Finset.filter_subset _ _) hxA)
  exact hM.2 e heM f hfM hef y hye hyf

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def experimentData {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (h : History n)
    (e : Edge n) (B : EdgeSet n) : Local n := {
  base := B
  potential := (graphEdges G).filter (fun f => ∃ x y, f = s(x,y) ∧ x ∈ e ∧ y ∈ Yset h)
  x1 := e.out.1
  x2 := e.out.2
  Y := Yset h
  marked := references M h e }

lemma edge_out_mem_iff {n : ℕ} (e : Edge n) (x : Fin n) :
    x ∈ e ↔ x ∈ ({e.out.1,e.out.2} : Finset (Fin n)) := by
  have he : s(e.out.1,e.out.2) = e := by rw [Sym2.mk,e.out_eq]
  conv_lhs => rw [←he,Sym2.mem_iff]
  simp only [Finset.mem_insert,Finset.mem_singleton]

lemma reference_partner_injection {n : ℕ} (M : EdgeSet n) (hM : IsMatching M)
    (h : History n) (e : Edge n) : ∃ f : references M h e → Fin n,
      Function.Injective f ∧ ∀ y, f y ∈ e ∧ s(f y,y.val) ∈ M := by
  choose f hf using (fun y : references M h e => (Finset.mem_filter.mp y.property).2)
  refine ⟨f,?_,hf⟩
  intro y z heq
  apply Subtype.ext
  have hopt : s(f y,y.val) = s(f z,z.val) := by
    by_contra hn
    exact hM.2 _ (hf y).2 _ (hf z).2 hn (f y) (by simp) (by rw [heq]; simp)
  rw [heq] at hopt
  rcases Sym2.eq_iff.mp hopt with hh | hh
  · exact hh.2
  · exact hh.2.trans hh.1

lemma reference_card_le_two {n : ℕ} (M : EdgeSet n) (hM : IsMatching M) (h : History n) (e : Edge n) :
    (references M h e).card ≤ 2 := by
  obtain ⟨f,hinj,hf⟩ := reference_partner_injection M hM h e
  let g : references M h e → ({e.out.1,e.out.2} : Finset (Fin n)) :=
    fun y => ⟨f y,(edge_out_mem_iff e (f y)).mp (hf y).1⟩
  have hg : Function.Injective g := fun y z hyz => hinj (congrArg Subtype.val hyz)
  have hc := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_coe] at hc
  exact hc.trans (by by_cases hh : e.out.1 = e.out.2 <;> simp [hh])

lemma experiment_partners {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (h : History n) (e : Edge n) (B : EdgeSet n) :
    (experimentData G M h e B).Partners := by
  obtain ⟨f,hinj,hf⟩ := reference_partner_injection M hM h e
  refine ⟨f,hinj,?_⟩
  intro y
  refine ⟨(edge_out_mem_iff e (f y)).mp (hf y).1,?_⟩
  exact Finset.mem_filter.mpr ⟨hMG (hf y).2,f y,y.val,rfl,(hf y).1,(Finset.mem_filter.mp y.property).1⟩

lemma experiment_valid {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (a : ℝ) (h : History n) (e : Edge n)
    (he : e ∈ early a h) (hdiag : ¬e.IsDiag) (B : EdgeSet n)
    (hB : B ⊆ graphEdges G) (havoid : ∀ f ∈ B, ∀ v, v ∈ e → v ∉ f) :
    (experimentData G M h e B).Valid := by
  have heq : s(e.out.1,e.out.2) = e := by rw [Sym2.mk,e.out_eq]
  have hne : e.out.1 ≠ e.out.2 := by
    intro hh
    apply hdiag
    rw [←heq,Sym2.mk_isDiag_iff]
    exact hh
  refine ⟨hne,?_,Yset_avoids_early a h e he _ (Sym2.out_fst_mem e),
    Yset_avoids_early a h e he _ (Sym2.out_snd_mem e),Finset.filter_subset _ _,
    reference_card_le_two M hM h e,?_⟩
  · intro f hf
    exact ⟨G.not_isDiag_of_mem_edgeSet (by simpa only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hB hf),
      havoid f hf _ (Sym2.out_fst_mem e),havoid f hf _ (Sym2.out_snd_mem e)⟩
  · intro f hf
    obtain ⟨hfg,x,y,hxy,hx,hy⟩ := Finset.mem_filter.mp hf
    exact ⟨x,(edge_out_mem_iff e x).mp hx,y,hy,hxy⟩

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def residualCoordinate {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (h : History n) (f : G.edgeSet) : Measure ℝ :=
  if f.val ∈ h.accepted then Measure.dirac (h.time f.val) else tailLaw (lowerTime b h f.val)

lemma residualLaw_pi {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (h : History n) :
    residualLaw G b h = Measure.pi (residualCoordinate G b h) := rfl

lemma residualCoordinate_probability {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : b < 1)
    (h : History n) (f : G.edgeSet) : IsProbabilityMeasure (residualCoordinate G b h f) := by
  unfold residualCoordinate
  split_ifs
  · infer_instance
  · exact tailLaw_probability _ ((lowerTime_le b h f.val).trans_lt hb)

lemma residualCoordinate_cross {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (h : History n)
    (hm : IsMatching h.accepted) (e : Edge n) (he : e ∈ h.accepted) (hte : h.time e ≤ b)
    (f : G.edgeSet) (hf : ∃ x y, f.val = s(x,y) ∧ x ∈ e ∧ y ∈ Yset h) :
    residualCoordinate G b h f = tailLaw (h.time e) := by
  obtain ⟨x,y,hf,hx,hy⟩ := hf
  have hn : f.val ∉ h.accepted := by rw [hf]; exact cross_edge_unaccepted h x y hy
  rw [residualCoordinate,if_neg hn,hf,lowerTime_cross_edge b h hm e he hte x y hx hy]

lemma residualCoordinate_potential {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (b : ℝ)
    (h : History n) (hm : IsMatching h.accepted) (e : Edge n) (he : e ∈ h.accepted) (hte : h.time e ≤ b)
    (B : EdgeSet n) (f : G.edgeSet) (hf : f.val ∈ (experimentData G M h e B).potential) :
    residualCoordinate G b h f = tailLaw (h.time e) :=
  residualCoordinate_cross G b h hm e he hte f (Finset.mem_filter.mp hf).2

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def graphEdgeEquiv {n : ℕ} (G : SimpleGraph (Fin n)) : (graphEdges G) ≃ G.edgeSet where
  toFun e := ⟨e.val,by simpa [graphEdges] using e.property⟩
  invFun e := ⟨e.val,by simpa [graphEdges] using e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def graphTimesEquiv {n : ℕ} (G : SimpleGraph (Fin n)) : Times G ≃ᵐ ((graphEdges G) → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : G.edgeSet => ℝ) (graphEdgeEquiv G)).symm

def fillGraphTimes {n : ℕ} (G : SimpleGraph (Fin n)) (z : Times G × (Edge n → ℝ)) : Edge n → ℝ :=
  fillCoordinates (graphEdges G) (graphTimesEquiv G z.1,z.2)

def liftedCoordinate {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n) : Edge n → Measure ℝ :=
  fillLaw (graphEdges G) (fun e => residualCoordinate G 1 h (graphEdgeEquiv G e))
    (fun _ => volume.restrict (Set.Icc (0:ℝ) 1))

lemma residualCoordinate_probability_valid {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1) (e : G.edgeSet) :
    IsProbabilityMeasure (residualCoordinate G 1 h e) := by
  unfold residualCoordinate
  split_ifs with he
  · infer_instance
  · exact tailLaw_probability _ (hvalid e he)

lemma fillGraphTimes_preserving {n : ℕ} (G : SimpleGraph (Fin n)) (μ : G.edgeSet → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (ν : Edge n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] :
    MeasurePreserving (fillGraphTimes G) ((Measure.pi μ).prod (Measure.pi ν))
      (Measure.pi (fillLaw (graphEdges G) (fun e => μ (graphEdgeEquiv G e)) ν)) := by
  have hp := MeasurePreserving.symm _ (measurePreserving_piCongrLeft μ (graphEdgeEquiv G))
  have hf := fillCoordinates_preserving (graphEdges G) (fun e => μ (graphEdgeEquiv G e)) ν
  exact hf.comp (hp.prod (MeasurePreserving.id _))

lemma fillGraphTimes_residual {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1) :
    MeasurePreserving (fillGraphTimes G)
      ((residualLaw G 1 h).prod (Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))))
      (Measure.pi (liftedCoordinate G h)) := by
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by norm_num [Measure.restrict_apply_univ]⟩
  haveI (e : G.edgeSet) := residualCoordinate_probability_valid G h hvalid e
  exact fillGraphTimes_preserving G (residualCoordinate G 1 h) (fun _ => volume.restrict (Set.Icc (0:ℝ) 1))

lemma fillGraphTimes_uniform {n : ℕ} (G : SimpleGraph (Fin n)) :
    MeasurePreserving (fillGraphTimes G)
      ((arrivalLaw G).prod (Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))))
      (Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))) := by
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by norm_num [Measure.restrict_apply_univ]⟩
  have hp := fillGraphTimes_preserving G (fun _ => volume.restrict (Set.Icc (0:ℝ) 1))
    (fun _ => volume.restrict (Set.Icc (0:ℝ) 1))
  have heq : fillLaw (graphEdges G) (fun _ => volume.restrict (Set.Icc (0:ℝ) 1))
      (fun _ => volume.restrict (Set.Icc (0:ℝ) 1)) = fun _ => volume.restrict (Set.Icc (0:ℝ) 1) := by
    funext e
    simp [fillLaw]
  rw [heq] at hp
  exact hp

lemma fillGraphTimes_on {n : ℕ} (G : SimpleGraph (Fin n)) (z : Times G × (Edge n → ℝ)) (e : G.edgeSet) :
    fillGraphTimes G z e.val = z.1 e := by
  have he : e.val ∈ graphEdges G := by simpa [graphEdges] using e.property
  simp only [fillGraphTimes,fillCoordinates,he,↓reduceDIte]
  rfl

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def historyClosed {n : ℕ} (h : History n) (s : ℝ) : EdgeSet n := h.accepted.filter (fun e => h.time e ≤ s)

lemma history_hole_unaccepted {n : ℕ} (h : History n) (hm : IsMatching h.accepted)
    (s : ℝ) (w a : Fin n) (hw : w ∉ covered (historyClosed h s))
    (ha : a ∈ covered (historyClosed h s)) : s(w,a) ∉ h.accepted := by
  obtain ⟨e,he,hae⟩ : ∃ e ∈ historyClosed h s, a ∈ e := by simpa [covered] using ha
  intro href
  have heh := (Finset.mem_filter.mp he).1
  have heq : e = s(w,a) := by
    by_contra hne
    exact hm.2 e heh s(w,a) href hne a hae (by simp)
  apply hw
  simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨e,he,by rw [heq]; simp⟩

lemma history_hole_lower {n : ℕ} (h : History n) (s : ℝ) (w a : Fin n)
    (ha : a ∈ covered (historyClosed h s)) : lowerTime 1 h s(w,a) ≤ s := by
  obtain ⟨e,he,hae⟩ : ∃ e ∈ historyClosed h s, a ∈ e := by simpa [covered] using ha
  have heh := Finset.mem_filter.mp he
  have hh := (le_lowerTime_iff (lowerTime 1 h s(w,a)) 1 h s(w,a)).mp le_rfl
  exact (hh.2 a (by simp) e heh.1 hae).trans heh.2

lemma uniform_eq_tail_zero : volume.restrict (Set.Icc (0:ℝ) 1) = tailLaw 0 := by
  have hh := tailLaw_map_uniform 0 (by norm_num)
  have heq : (fun u : ℝ => (0:ℝ)+(1-0)*u) = id := by funext u; simp
  rw [heq,Measure.map_id] at hh
  exact hh

lemma lifted_hole_coordinate {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (hm : IsMatching h.accepted) (s : ℝ) (hs : 0 ≤ s) (z w a : Fin n)
    (hz : ∀ e ∈ G.edgeSet, z ∉ e) (hw : w ∉ covered (historyClosed h s))
    (ha : a ∈ insert z (covered (historyClosed h s))) :
    ∃ l, l ≤ s ∧ liftedCoordinate G h s(w,a) = tailLaw l := by
  by_cases he : s(w,a) ∈ graphEdges G
  · have haD : a ∈ covered (historyClosed h s) := by
      rcases Finset.mem_insert.mp ha with rfl | hh
      · have heG : s(w,a) ∈ G.edgeSet := by simpa [graphEdges] using he
        exact (hz s(w,a) heG (by simp)).elim
      · exact hh
    refine ⟨lowerTime 1 h s(w,a),history_hole_lower h s w a haD,?_⟩
    simp only [liftedCoordinate,fillLaw,he,↓reduceDIte,residualCoordinate]
    change (if s(w,a) ∈ h.accepted then Measure.dirac (h.time s(w,a)) else tailLaw (lowerTime 1 h s(w,a))) = _
    rw [if_neg (history_hole_unaccepted h hm s w a hw haD)]
  · refine ⟨0,hs,?_⟩
    simp only [liftedCoordinate,fillLaw,he,↓reduceDIte]
    exact uniform_eq_tail_zero

end
end FengLiYangMatching.General
open MeasureTheory ProbabilityTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma pi_pair_map {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (e f : ι) (hef : e ≠ f) :
    (Measure.pi μ).map (fun t => (t e,t f)) = (μ e).prod (μ f) := by
  have hi := (iIndepFun_pi (μ:=μ) (X:=fun _ => id) (fun _ => aemeasurable_id)).indepFun hef
  have hh := (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply e).aemeasurable (measurable_pi_apply f).aemeasurable).mp hi
  rw [(measurePreserving_eval μ e).map_eq,(measurePreserving_eval μ f).map_eq] at hh
  exact hh

lemma pi_pair_neq {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (e f : ι) (hef : e ≠ f)
    (hdiag : ((μ e).prod (μ f)) {z : ℝ × ℝ | z.1=z.2} = 0) :
    ∀ᵐ t ∂Measure.pi μ, t e ≠ t f := by
  apply ae_iff.mpr
  have hh := Measure.map_apply ((measurable_pi_apply e).prodMk (measurable_pi_apply f))
    (measurableSet_eq_fun measurable_fst measurable_snd) (μ:=Measure.pi μ)
  rw [pi_pair_map μ e f hef,hdiag] at hh
  simpa using hh.symm

lemma pi_pair_neq_atomless {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (e f : ι) (hef : e ≠ f) [NullSingletonClass (μ f)] :
    ∀ᵐ t ∂Measure.pi μ, t e ≠ t f := by
  apply pi_pair_neq μ e f hef
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  simp

lemma pi_injective_mixed {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (A : Finset ι) (time : ι → ℝ)
    (hdirac : ∀ i ∈ A, μ i = Measure.dirac (time i))
    (hatom : ∀ i ∉ A, NullSingletonClass (μ i)) (htime : Set.InjOn time A) :
    ∀ᵐ t ∂Measure.pi μ, Function.Injective t := by
  have hp : ∀ e f : ι, e ≠ f → ∀ᵐ t ∂Measure.pi μ, t e ≠ t f := by
    intro e f hef
    by_cases hf : f ∈ A
    · by_cases he : e ∈ A
      · apply pi_pair_neq μ e f hef
        rw [hdirac e he,hdirac f hf,Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
        have hne : time e ≠ time f := fun h => hef (htime he hf h)
        simp [hne]
      · haveI := hatom e he
        exact (pi_pair_neq_atomless μ f e hef.symm).mono (fun t h => h.symm)
    · haveI := hatom f hf
      exact pi_pair_neq_atomless μ e f hef
  have hall : ∀ᵐ t ∂Measure.pi μ, ∀ e f : ι, e ≠ f → t e ≠ t f :=
    ae_all_iff.mpr (fun e => ae_all_iff.mpr (fun f => by
      by_cases hef : e=f
      · simp [hef]
      · exact (hp e f hef).mono (fun t ht _ => ht)))
  filter_upwards [hall] with t ht
  intro e f hef
  by_contra hne
  exact ht e f hne hef

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma full_history_regular {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ᵐ h ∂historyLaw G 1, IsMatching h.accepted ∧ h.accepted ⊆ graphEdges G ∧
      (∀ e ∈ h.accepted, 0 < h.time e ∧ h.time e < 1) ∧ Set.InjOn h.time h.accepted := by
  filter_upwards [full_residual_probability G,full_residual_support G,full_residual_injective G,full_residual_times G]
    with h hp hs hi ht
  haveI := hp
  obtain ⟨t,hth,hti,htt⟩ := (hs.and (hi.and ht)).exists
  have hsub : h.accepted ⊆ graphEdges G := by rw [←hth]; exact shadowAt_subset_graph G t 1
  have hEG (e : Edge n) (he : e ∈ h.accepted) : e ∈ G.edgeSet := by simpa [graphEdges] using hsub he
  have hcoord (e : Edge n) (he : e ∈ h.accepted) : h.time e = t ⟨e,hEG e he⟩ := by
    have heA : e ∈ shadowAt G t 1 := by
      change e ∈ (history G 1 t).accepted
      rw [hth]
      exact he
    rw [←hth]
    simp only [history,History.time,hEG e he,heA,↓reduceDIte,↓reduceIte]
  refine ⟨?_,hsub,?_,?_⟩
  · rw [←hth]; exact shadowAt_matching G t 1
  · intro e he
    rw [hcoord e he]
    exact htt _
  · intro e he f hf hef
    rw [hcoord e he,hcoord f hf] at hef
    exact congrArg Subtype.val (hti hef)

lemma liftedCoordinate_probability {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1) (e : Edge n) :
    IsProbabilityMeasure (liftedCoordinate G h e) := by
  unfold liftedCoordinate fillLaw
  split_ifs
  · exact residualCoordinate_probability_valid G h hvalid _
  · constructor
    norm_num [Measure.restrict_apply_univ]

lemma liftedCoordinate_dirac {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (hsub : h.accepted ⊆ graphEdges G) (e : Edge n) (he : e ∈ h.accepted) :
    liftedCoordinate G h e = Measure.dirac (h.time e) := by
  have heG := hsub he
  simp only [liftedCoordinate,fillLaw,heG,↓reduceDIte,residualCoordinate]
  change (if e ∈ h.accepted then Measure.dirac (h.time e) else tailLaw (lowerTime 1 h e)) = _
  rw [if_pos he]

lemma liftedCoordinate_atomless {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (e : Edge n) (he : e ∉ h.accepted) : NullSingletonClass (liftedCoordinate G h e) := by
  by_cases heG : e ∈ graphEdges G
  · simp only [liftedCoordinate,fillLaw,heG,↓reduceDIte,residualCoordinate]
    change NullSingletonClass (if e ∈ h.accepted then Measure.dirac (h.time e) else tailLaw (lowerTime 1 h e))
    rw [if_neg he]
    exact tailLaw_atomless _
  · simp only [liftedCoordinate,fillLaw,heG,↓reduceDIte]
    infer_instance

lemma lifted_injective {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1)
    (hsub : h.accepted ⊆ graphEdges G) (htime : Set.InjOn h.time h.accepted) :
    ∀ᵐ v ∂Measure.pi (liftedCoordinate G h), Function.Injective v := by
  haveI (e : Edge n) := liftedCoordinate_probability G h hvalid e
  exact pi_injective_mixed (liftedCoordinate G h) h.accepted h.time
    (liftedCoordinate_dirac G h hsub) (liftedCoordinate_atomless G h) htime

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma clock_full_eq {n : ℕ} (H : EdgeSet n) (v : Edge n → ℝ) (hv : ∀ e ∈ H, v e < 1) :
    clockOpenState H v 1 = greedy (orderFor H (fun e => v e.val)) := by
  unfold clockOpenState clockOpenPrefix
  congr 1
  apply List.filter_eq_self.mpr
  intro e he
  have hm := (mem_permLists H _).mp (orderFor_mem H (fun e => v e.val))
  exact decide_eq_true (hv e (by rw [←hm.2]; exact List.mem_toFinset.mpr he))

lemma clock_history_cutoffs {n : ℕ} (H : EdgeSet n) (h : History n) (v : Edge n → ℝ)
    (hv : ∀ e ∈ H, v e < 1) (hfull : clockOpenState H v 1 = h.accepted)
    (htime : ∀ e ∈ h.accepted, h.time e = v e) :
    (∀ t, clockState H v t = h.accepted.filter (fun e => h.time e ≤ t)) ∧
    (∀ t, clockOpenState H v t = h.accepted.filter (fun e => h.time e < t)) := by
  rw [clock_full_eq H v hv] at hfull
  constructor
  · intro t
    have hh := greedy_filter_le_time (orderFor H (fun e => v e.val)) v (orderFor_pairwise H v) t
    unfold clockState clockPrefix
    rw [hh,hfull]
    apply Finset.filter_congr
    intro e he
    rw [htime e he]
  · intro t
    have hh := greedy_filter_time (orderFor H (fun e => v e.val)) v (orderFor_pairwise H v) t
    unfold clockOpenState clockOpenPrefix
    rw [hh,hfull]
    apply Finset.filter_congr
    intro e he
    rw [htime e he]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma preserving_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hp : MeasurePreserving f μ ν)
    (P : β → Prop) (hP : ∀ᵐ y ∂ν, P y) : ∀ᵐ x ∂μ, P (f x) := by
  have hh := Measure.tendsto_ae_map (μ:=μ) hp.measurable.aemeasurable
  rw [hp.map_eq] at hh
  exact hh.eventually hP

def graphRestriction {n : ℕ} (G : SimpleGraph (Fin n)) (v : Edge n → ℝ) : Times G := fun e => v e.val

lemma measurable_graphRestriction {n : ℕ} (G : SimpleGraph (Fin n)) : Measurable (graphRestriction G) :=
  measurable_pi_iff.mpr (fun e => measurable_pi_apply e.val)

lemma lifted_history_support {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1)
    (hs : ∀ᵐ t ∂residualLaw G 1 h, history G 1 t = h) :
    ∀ᵐ v ∂Measure.pi (liftedCoordinate G h), history G 1 (graphRestriction G v) = h := by
  haveI (e : G.edgeSet) := residualCoordinate_probability_valid G h hvalid e
  haveI : IsProbabilityMeasure (residualLaw G 1 h) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (residualCoordinate G 1 h)))
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by norm_num [Measure.restrict_apply_univ]⟩
  have hp := fillGraphTimes_residual G h hvalid
  have hm : MeasurableSet {v : Edge n → ℝ | history G 1 (graphRestriction G v) = h} :=
    measurableSet_eq_fun ((measurable_history G 1).comp (measurable_graphRestriction G)) measurable_const
  rw [←hp.map_eq]
  apply (ae_map_iff hp.measurable.aemeasurable hm).mpr
  have hh := preserving_ae (measurePreserving_fst (μ:=residualLaw G 1 h)
    (ν:=Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1)))) _ hs
  filter_upwards [hh] with z hz
  have heq : graphRestriction G (fillGraphTimes G z) = z.1 := funext (fillGraphTimes_on G z)
  rw [heq]
  exact hz

lemma lifted_times {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1)
    (hsub : h.accepted ⊆ graphEdges G) (htime : ∀ e ∈ h.accepted, 0 < h.time e ∧ h.time e < 1) :
    ∀ᵐ v ∂Measure.pi (liftedCoordinate G h), ∀ e, 0 < v e ∧ v e < 1 := by
  haveI (e : Edge n) := liftedCoordinate_probability G h hvalid e
  have hcoord (e : Edge n) : ∀ᵐ x ∂liftedCoordinate G h e, 0 < x ∧ x < 1 := by
    by_cases he : e ∈ h.accepted
    · rw [liftedCoordinate_dirac G h hsub e he]
      simpa only [ae_dirac_eq,Filter.eventually_pure] using htime e he
    · by_cases heG : e ∈ graphEdges G
      · have hlo : 0 ≤ lowerTime 1 h e := by
          apply (le_lowerTime_iff 0 1 h e).mpr
          exact ⟨by norm_num,fun _ _ f hf _ => (htime f hf).1.le⟩
        simp only [liftedCoordinate,fillLaw,heG,↓reduceDIte,residualCoordinate]
        change ∀ᵐ x ∂(if e ∈ h.accepted then Measure.dirac (h.time e) else tailLaw (lowerTime 1 h e)), 0 < x ∧ x < 1
        rw [if_neg he]
        unfold tailLaw
        exact (Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioo) _).mono (fun x hx => ⟨hlo.trans_lt hx.1,hx.2⟩)
      · simp only [liftedCoordinate,fillLaw,heG,↓reduceDIte]
        have h0 : ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), (0:ℝ) < x := by
          filter_upwards [ae_restrict_mem measurableSet_Icc,(show ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), x ≠ 0 from by simp only [ae_iff,not_not,Set.setOf_eq_eq_singleton,measure_singleton])] with x hx hne
          exact lt_of_le_of_ne hx.1 hne.symm
        have h1 : ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), x < 1 := by
          filter_upwards [ae_restrict_mem measurableSet_Icc,(show ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), x ≠ 1 from by simp only [ae_iff,not_not,Set.setOf_eq_eq_singleton,measure_singleton])] with x hx hne
          exact lt_of_le_of_ne hx.2 hne
        exact h0.and h1
  exact ae_all_iff.mpr (fun e => Measure.tendsto_eval_ae_ae.eventually (hcoord e))

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma preserving_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {g : α → β} (hp : MeasurePreserving g μ ν)
    (f : β → ℝ) (hf : Measurable f) : (∫ x, f (g x) ∂μ) = ∫ y, f y ∂ν := by
  have hh := integral_map hp.measurable.aemeasurable (hf.aestronglyMeasurable (μ:=μ.map g))
  rw [hp.map_eq] at hh
  exact hh.symm

lemma lifted_integral {n : ℕ} (G : SimpleGraph (Fin n)) (f : (Edge n → ℝ) → ℝ)
    (hf : Measurable f) (C : ℝ) (hbound : ∀ v, ‖f v‖ ≤ C) :
    (∫ v, f v ∂Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))) =
      ∫ h, ∫ v, f v ∂Measure.pi (liftedCoordinate G h) ∂historyLaw G 1 := by
  haveI := arrival_probability G
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by norm_num [Measure.restrict_apply_univ]⟩
  let ν := Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))
  let F : Times G → ℝ := fun t => ∫ u, f (fillGraphTimes G (t,u)) ∂ν
  have hp := fillGraphTimes_uniform G
  have hif : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hbound)
  have hijoint := hp.integrable_comp_of_integrable hif
  have hFm : Measurable F := (hf.comp hp.measurable).stronglyMeasurable.integral_prod_right'.measurable
  have hFi : Integrable F (arrivalLaw G) := hijoint.integral_prod_left
  have heq : (∫ v, f v ∂ν) = ∫ t, F t ∂arrivalLaw G := by
    rw [←preserving_integral hp f hf]
    exact integral_prod _ hijoint
  rw [heq,full_history_integral G F hFm hFi]
  apply integral_congr_ae
  filter_upwards [full_history_valid G] with h hh
  haveI (e : Edge n) := liftedCoordinate_probability G h hh e
  haveI (e : G.edgeSet) := residualCoordinate_probability_valid G h hh e
  haveI : IsProbabilityMeasure (residualLaw G 1 h) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (residualCoordinate G 1 h)))
  have hp' := fillGraphTimes_residual G h hh
  have hif' : Integrable f (Measure.pi (liftedCoordinate G h)) := Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hbound)
  have hi' := hp'.integrable_comp_of_integrable hif'
  calc
    _ = ∫ z, f (fillGraphTimes G z) ∂(residualLaw G 1 h).prod ν := (integral_prod _ hi').symm
    _ = _ := preserving_integral hp' f hf

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma coordinate_refresh_preserving {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (e : ι) :
    MeasurePreserving (fun z : (ι → ℝ) × ℝ => Function.update z.1 e z.2)
      ((Measure.pi μ).prod (μ e)) (Measure.pi μ) := by
  have hs := realSplit_preserving μ e
  have hp := (measurePreserving_snd (μ:=μ e) (ν:=Measure.pi (fun i : {i : ι // i ≠ e} => μ i.val))).comp hs
  have hswap := Measure.measurePreserving_swap (μ:=Measure.pi (fun i : {i : ι // i ≠ e} => μ i.val)) (ν:=μ e)
  have hinv := MeasurePreserving.symm (realSplit e) hs
  have hh := hinv.comp (hswap.comp (hp.prod (MeasurePreserving.id (μ e))))
  convert! hh using 1
  funext z i
  by_cases hi : i=e <;> simp [realSplit,realInsert,Function.update,hi]

lemma coordinate_refresh_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (e : ι)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f) (hi : Integrable f (Measure.pi μ)) :
    (∫ v, f v ∂Measure.pi μ) = ∫ v, ∫ u, f (Function.update v e u) ∂μ e ∂Measure.pi μ := by
  have hp := coordinate_refresh_preserving μ e
  rw [←preserving_integral hp f hf]
  exact integral_prod _ (hp.integrable_comp_of_integrable hi)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma history_mean_integrable {n : ℕ} (G : SimpleGraph (Fin n)) (f : Times G → ℝ)
    (hf : Measurable f) (C : ℝ) (hb : ∀ t, ‖f t‖ ≤ C) :
    Integrable (fun h => ∫ t, f t ∂residualLaw G 1 h) (historyLaw G 1) := by
  haveI := arrival_probability G
  haveI : IsProbabilityMeasure (historyLaw G 1) := by
    unfold historyLaw
    exact Measure.isProbabilityMeasure_map (measurable_history G 1).aemeasurable
  let m : History n → ℝ := fun h => ∫ u, f (residualSample G 1 h u) ∂arrivalLaw G
  have hm : Measurable m := (hf.comp (measurable_residualSample G 1)).stronglyMeasurable.integral_prod_right'.measurable
  have him : Integrable m (historyLaw G 1) := by
    apply Integrable.of_bound hm.aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun h => by
      simpa using norm_integral_le_of_norm_le_const (μ:=arrivalLaw G) (Filter.Eventually.of_forall (fun u => hb (residualSample G 1 h u))))
  apply him.congr
  filter_upwards [full_history_residual_eq G] with h hh
  rw [←hh,sampledResidualLaw]
  exact (integral_map ((measurable_residualSample G 1).comp measurable_prodMk_left).aemeasurable hf.aestronglyMeasurable).symm

lemma lifted_mean_integrable {n : ℕ} (G : SimpleGraph (Fin n)) (f : (Edge n → ℝ) → ℝ)
    (hf : Measurable f) (C : ℝ) (hb : ∀ v, ‖f v‖ ≤ C) :
    Integrable (fun h => ∫ v, f v ∂Measure.pi (liftedCoordinate G h)) (historyLaw G 1) := by
  haveI := arrival_probability G
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by norm_num [Measure.restrict_apply_univ]⟩
  let ν := Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))
  let F : Times G → ℝ := fun t => ∫ u, f (fillGraphTimes G (t,u)) ∂ν
  have hF : Measurable F := (hf.comp (fillGraphTimes_uniform G).measurable).stronglyMeasurable.integral_prod_right'.measurable
  have hFb (t : Times G) : ‖F t‖ ≤ C := by
    simpa using norm_integral_le_of_norm_le_const (μ:=ν) (Filter.Eventually.of_forall (fun u => hb (fillGraphTimes G (t,u))))
  have hi := history_mean_integrable G F hF C hFb
  apply hi.congr
  filter_upwards [full_history_valid G] with h hh
  haveI (e : Edge n) := liftedCoordinate_probability G h hh e
  haveI (e : G.edgeSet) := residualCoordinate_probability_valid G h hh e
  haveI : IsProbabilityMeasure (residualLaw G 1 h) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (residualCoordinate G 1 h)))
  have hp := fillGraphTimes_residual G h hh
  have hif : Integrable f (Measure.pi (liftedCoordinate G h)) := Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hb)
  have hij := hp.integrable_comp_of_integrable hif
  calc
    _ = ∫ z, f (fillGraphTimes G z) ∂(residualLaw G 1 h).prod ν := (integral_prod _ hij).symm
    _ = _ := preserving_integral hp f hf

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma graphRestriction_preserving {n : ℕ} (G : SimpleGraph (Fin n)) :
    MeasurePreserving (graphRestriction G)
      (Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))) (arrivalLaw G) := by
  haveI := arrival_probability G
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by norm_num [Measure.restrict_apply_univ]⟩
  have hp := fillGraphTimes_uniform G
  refine ⟨measurable_graphRestriction G,?_⟩
  rw [←hp.map_eq,Measure.map_map (measurable_graphRestriction G) hp.measurable]
  have heq : graphRestriction G ∘ fillGraphTimes G = Prod.fst := by
    funext z
    exact funext (fillGraphTimes_on G z)
  rw [heq]
  exact (measurePreserving_fst (μ:=arrivalLaw G)
    (ν:=Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1)))).map_eq

lemma graphHistory_preserving {n : ℕ} (G : SimpleGraph (Fin n)) :
    MeasurePreserving (fun v : Edge n → ℝ => history G 1 (graphRestriction G v))
      (Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))) (historyLaw G 1) := by
  have hh : MeasurePreserving (history G 1) (arrivalLaw G) (historyLaw G 1) := ⟨measurable_history G 1,rfl⟩
  exact hh.comp (graphRestriction_preserving G)

lemma history_matchTime_integrable {n : ℕ} (G : SimpleGraph (Fin n)) (y : Fin n) :
    Integrable (fun h => matchTime 1 h y) (historyLaw G 1) := by
  haveI := arrival_probability G
  haveI : IsProbabilityMeasure (historyLaw G 1) := by
    unfold historyLaw
    exact Measure.isProbabilityMeasure_map (measurable_history G 1).aemeasurable
  apply Integrable.of_bound (measurable_matchTime 1 y).aestronglyMeasurable 1
  filter_upwards [full_history_regular G] with h hr
  have hlo : 0 ≤ matchTime 1 h y := by
    apply (le_matchTime_iff 0 1 h y).mpr
    exact ⟨by norm_num,fun e he _ => (hr.2.2.1 e he).1.le⟩
  have hhi : matchTime 1 h y ≤ 1 := ((le_matchTime_iff (matchTime 1 h y) 1 h y).mp le_rfl).1
  simpa only [Real.norm_eq_abs,abs_of_nonneg hlo] using hhi

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma clock_history {n : ℕ} (G : SimpleGraph (Fin n)) (v : Edge n → ℝ)
    (hv : Set.InjOn v (graphEdges G)) (ht : ∀ e ∈ graphEdges G, v e < 1) :
    clockGreedy (graphEdges G) v = (history G 1 (graphRestriction G v)).accepted ∧
    (∀ t, clockOpenState (graphEdges G) v t =
      (history G 1 (graphRestriction G v)).accepted.filter (fun e => (history G 1 (graphRestriction G v)).time e < t)) := by
  let h := history G 1 (graphRestriction G v)
  have hfull : clockOpenState (graphEdges G) v 1 = h.accepted := clockState_graph_history G v hv 1
  have hcoords (e : Edge n) (he : e ∈ h.accepted) : h.time e = v e := by
    have heA : e ∈ shadowAt G (graphRestriction G v) 1 := he
    have heG : e ∈ G.edgeSet := by simpa [graphEdges] using shadowAt_subset_graph G (graphRestriction G v) 1 heA
    simp only [h,history,History.time,heG,heA,↓reduceDIte,↓reduceIte,graphRestriction]
  refine ⟨?_,(clock_history_cutoffs _ h v ht hfull hcoords).2⟩
  rw [clock_full_eq _ v ht] at hfull
  exact hfull

lemma clock_history_matchTime_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (v : Edge n → ℝ)
    (ht : ∀ e ∈ graphEdges G, 0 ≤ v e) (y : Fin n) :
    0 ≤ matchTime 1 (history G 1 (graphRestriction G v)) y := by
  apply (le_matchTime_iff 0 1 _ y).mpr
  refine ⟨by norm_num,?_⟩
  intro e he hye
  have heA : e ∈ shadowAt G (graphRestriction G v) 1 := he
  have heG : e ∈ G.edgeSet := by simpa [graphEdges] using shadowAt_subset_graph G (graphRestriction G v) 1 heA
  have hh := ht e (shadowAt_subset_graph G _ 1 heA)
  simpa only [history,History.time,heG,heA,↓reduceDIte,↓reduceIte,graphRestriction] using hh

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma uniform_clock_times {ι : Type*} [Fintype ι] :
    ∀ᵐ v ∂Measure.pi (fun _ : ι => volume.restrict (Set.Icc (0:ℝ) 1)), ∀ e, 0 < v e ∧ v e < 1 := by
  apply ae_all_iff.mpr
  intro e
  have hh : ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), 0 < x ∧ x < 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (show ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), x ≠ 0 from by simp only [ae_iff,not_not,Set.setOf_eq_eq_singleton,measure_singleton]),
      (show ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1), x ≠ 1 from by simp only [ae_iff,not_not,Set.setOf_eq_eq_singleton,measure_singleton])]
      with x hx h0 h1
    exact ⟨lt_of_le_of_ne hx.1 h0.symm,lt_of_le_of_ne hx.2 h1⟩
  exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : ι => volume.restrict (Set.Icc (0:ℝ) 1)) (i:=e)).eventually hh

lemma uniform_clock_injective {ι : Type*} [Fintype ι] :
    ∀ᵐ v ∂Measure.pi (fun _ : ι => volume.restrict (Set.Icc (0:ℝ) 1)), Function.Injective v := by
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by simp⟩
  exact iid_real_injective _

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section
set_option maxHeartbeats 1000000

lemma reference_expected {n : ℕ} (B F : EdgeSet n) (x y : Fin n) (hxy : x ≠ y)
    (hloop : ∀ e ∈ B ∪ F, ¬e.IsDiag) (hF : ∀ e ∈ F, x ∈ e)
    (href : s(x,y) ∉ B ∪ F) (q : ℝ) (hq : (3/5:ℝ) ≤ q) (hq1 : q ≤ 1) :
    2+(∫ h, matchTime 1 h y ∂historyLaw (graphOfEdges B) 1) ≤
      ∫ v, referenceScore x y q (clockGreedy (insert s(x,y) (B ∪ F)) v) (clockGreedy (B ∪ F) v)
        ∂Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1)) := by
  let G := graphOfEdges B
  let μ := Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by simp⟩
  let f := fun v => referenceScore x y q (clockGreedy (insert s(x,y) (B ∪ F)) v) (clockGreedy (B ∪ F) v)
  have hm : Measurable (fun v : Edge n → ℝ => (clockGreedy (insert s(x,y) (B ∪ F)) v,clockGreedy (B ∪ F) v)) :=
    (measurable_clockGreedy _).prodMk (measurable_clockGreedy _)
  have hf : Measurable f := by
    have hh := (measurable_of_finite (fun M : EdgeSet n × EdgeSet n => referenceScore x y q M.1 M.2)).comp hm
    convert! hh using 1
  have hi : Integrable f μ := integrable_finite_comp μ (fun v => (clockGreedy (insert s(x,y) (B ∪ F)) v,clockGreedy (B ∪ F) v))
    ((measurable_clockGreedy _).prodMk (measurable_clockGreedy _)) (fun M => referenceScore x y q M.1 M.2)
  have hp := coordinate_refresh_preserving (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1)) s(x,y)
  have hmean : Integrable (fun v => ∫ u, f (Function.update v s(x,y) u) ∂volume.restrict (Set.Icc (0:ℝ) 1)) μ :=
    (hp.integrable_comp_of_integrable hi).integral_prod_left
  have hG := graphHistory_preserving G
  have htau : Integrable (fun v => matchTime 1 (history G 1 (graphRestriction G v)) y) μ :=
    hG.integrable_comp_of_integrable (history_matchTime_integrable G y)
  have hsum : Integrable (fun v => 2+matchTime 1 (history G 1 (graphRestriction G v)) y) μ := (integrable_const 2).add htau
  have hGE : graphEdges G = B := graphEdges_graphOfEdges B (fun e he => hloop e (Finset.mem_union_left F he))
  have hbound : ∀ᵐ v ∂μ, 2+matchTime 1 (history G 1 (graphRestriction G v)) y ≤
      ∫ u, f (Function.update v s(x,y) u) ∂volume.restrict (Set.Icc (0:ℝ) 1) := by
    filter_upwards [uniform_clock_injective (ι:=Edge n),uniform_clock_times (ι:=Edge n)] with v hv hvt
    have hg := clock_history G v hv.injOn (fun e _ => (hvt e).2)
    rw [hGE] at hg
    exact reference_clock_average B F x y hxy hloop hF href v hv.injOn _ hg.1 hg.2
      (clock_history_matchTime_nonneg G v (fun e _ => (hvt e).1.le) y) q hq hq1
  have hleft : (∫ v, 2+matchTime 1 (history G 1 (graphRestriction G v)) y ∂μ) =
      2+∫ h, matchTime 1 h y ∂historyLaw G 1 := by
    rw [integral_add (integrable_const 2) htau]
    have hc : (∫ _ : Edge n → ℝ, (2:ℝ) ∂μ) = 2 := by simp [μ]
    rw [hc,preserving_integral hG (fun h => matchTime 1 h y) (measurable_matchTime 1 y)]
  have hh := integral_mono_ae hsum hmean hbound
  rw [hleft,←coordinate_refresh_integral (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1)) s(x,y) f hf hi] at hh
  exact hh

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma lifted_accepted_coordinates {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1)
    (hsub : h.accepted ⊆ graphEdges G) :
    ∀ᵐ v ∂Measure.pi (liftedCoordinate G h), ∀ e ∈ h.accepted, v e = h.time e := by
  haveI (e : Edge n) := liftedCoordinate_probability G h hvalid e
  apply ae_all_iff.mpr
  intro e
  by_cases he : e ∈ h.accepted
  · have hc : ∀ᵐ x ∂liftedCoordinate G h e, x = h.time e := by
      rw [liftedCoordinate_dirac G h hsub e he,ae_dirac_eq]
      simp
    exact (Measure.tendsto_eval_ae_ae.eventually hc).mono (fun v hv _ => hv)
  · exact Filter.Eventually.of_forall (fun v hv => (he hv).elim)

lemma lifted_cutoffs {n : ℕ} (G : SimpleGraph (Fin n)) (h : History n)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1)
    (hsub : h.accepted ⊆ graphEdges G) (htime : ∀ e ∈ h.accepted, 0 < h.time e ∧ h.time e < 1)
    (hinj : Set.InjOn h.time h.accepted)
    (hsupport : ∀ᵐ t ∂residualLaw G 1 h, history G 1 t = h) :
    ∀ᵐ v ∂Measure.pi (liftedCoordinate G h),
      (∀ t, clockState (graphEdges G) v t = historyClosed h t) ∧
      (∀ t, clockOpenState (graphEdges G) v t = h.accepted.filter (fun e => h.time e < t)) := by
  filter_upwards [lifted_injective G h hvalid hsub hinj,lifted_times G h hvalid hsub htime,
    lifted_history_support G h hvalid hsupport,lifted_accepted_coordinates G h hvalid hsub]
    with v hv hvt hvs hvc
  have hfull : clockOpenState (graphEdges G) v 1 = h.accepted :=
    (clockState_graph_history G v hv.injOn 1).trans (congrArg History.accepted hvs)
  exact clock_history_cutoffs (graphEdges G) h v (fun e _ => (hvt e).2) hfull (fun e he => (hvc e he).symm)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma survival_factor (s t : ℝ) (hs : s < 1) :
    (1-(t-s)/(1-s))*(1-s) = 1-t := by
  rw [sub_mul,one_mul,div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hs))]
  ring

lemma survival_factor_nonneg (s t : ℝ) (hs : s < 1) (ht : t ≤ 1) :
    0 ≤ 1-(t-s)/(1-s) := by
  have h := survival_factor s t hs
  exact (nonneg_of_mul_nonneg_right (by rw [mul_comm,h]; linarith) (sub_pos.mpr hs))

lemma survival_telescope (m : ℕ) (time prob : ℕ → ℝ)
    (hinit : 1-time 0 ≤ prob 0)
    (htime : ∀ j ≤ m, time j < 1)
    (hstep : ∀ j < m, (1-(time (j+1)-time j)/(1-time j))*prob j ≤ prob (j+1)) :
    ∀ j ≤ m, 1-time j ≤ prob j := by
  intro j hj
  induction j with
  | zero => exact hinit
  | succ j ih =>
    have hjm : j < m := by omega
    have hp := ih (by omega)
    have hf := survival_factor_nonneg (time j) (time (j+1)) (htime j (by omega)) (htime (j+1) hj).le
    have hh := mul_le_mul_of_nonneg_left hp hf
    rw [survival_factor _ _ (htime j (by omega))] at hh
    exact hh.trans (hstep j hjm)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma finite_gap_survival (S : Finset ℝ) (T : ℝ) (hT : 0 < T) (hT1 : T < 1)
    (hS : ∀ s ∈ S, 0 < s ∧ s < T) (closed opened : ℝ → ℝ)
    (hzero : 1 ≤ closed 0) (hlink : ∀ s ∈ S, opened s ≤ closed s)
    (hgap : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T →
      (∀ u ∈ S, ¬ (s < u ∧ u < t)) →
      (1-(t-s)/(1-s))*closed s ≤ opened t) :
    1-T ≤ opened T := by
  induction S using Finset.strongInductionOn generalizing T with
  | _ S ih =>
    by_cases hne : S.Nonempty
    · let s := S.max' hne
      have hsS : s ∈ S := S.max'_mem hne
      have hs0 := (hS s hsS).1
      have hsT := (hS s hsS).2
      have hs1 : s < 1 := hsT.trans hT1
      have herase : S.erase s ⊂ S := Finset.erase_ssubset hsS
      have hbefore : ∀ u ∈ S.erase s, 0 < u ∧ u < s := by
        intro u hu
        have hm := Finset.mem_erase.mp hu
        exact ⟨(hS u hm.2).1,lt_of_le_of_ne (S.le_max' u hm.2) hm.1⟩
      have hbound : 1-s ≤ opened s := ih (S.erase s) herase s hs0 hs1 hbefore
        (fun u hu => hlink u (Finset.mem_erase.mp hu).2) (by
          intro a b ha hab hbs hnone
          apply hgap a b ha hab (hbs.trans hsT.le)
          intro u hu hbetween
          by_cases hus : u=s
          · subst u; linarith [hbetween.2]
          · exact hnone u (Finset.mem_erase.mpr ⟨hus,hu⟩) hbetween)
      have hsclosed : 1-s ≤ closed s := hbound.trans (hlink s hsS)
      have hlast := hgap s T hs0.le hsT le_rfl (by
        intro u hu hbetween
        exact (not_lt_of_ge (S.le_max' u hu)) hbetween.1)
      have hm := mul_le_mul_of_nonneg_left hsclosed (survival_factor_nonneg s T hs1 hT1.le)
      rw [survival_factor s T hs1] at hm
      exact hm.trans hlast
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh := hgap 0 T le_rfl hT le_rfl (by simp [he])
      have hm := mul_le_mul_of_nonneg_left hzero (survival_factor_nonneg 0 T (by norm_num) hT1.le)
      simp only [sub_zero,div_one,mul_one] at hm hh
      exact hm.trans hh

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma conditional_survival {n : ℕ} (G : SimpleGraph (Fin n)) (E : EdgeSet n)
    (hE : ∀ e ∈ E, ¬e.IsDiag) (z w : Fin n) (hwz : w ≠ z)
    (hH : graphEdges G = E.filter (fun e => z ∉ e)) (hz : ∀ e ∈ G.edgeSet, z ∉ e)
    (h : History n) (hm : IsMatching h.accepted) (hsub : h.accepted ⊆ graphEdges G)
    (htime : ∀ e ∈ h.accepted, 0 < h.time e ∧ h.time e < 1) (hinj : Set.InjOn h.time h.accepted)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1)
    (hsupport : ∀ᵐ t ∂residualLaw G 1 h, history G 1 t = h)
    (T : ℝ) (hT : 0 < T) (hT1 : T < 1)
    (hw : w ∉ covered (h.accepted.filter (fun e => h.time e < T))) :
    1-T ≤ ∫ v, (if w ∉ covered (clockOpenState E v T) then (1:ℝ) else 0) ∂Measure.pi (liftedCoordinate G h) := by
  let μ := Measure.pi (liftedCoordinate G h)
  haveI (e : Edge n) := liftedCoordinate_probability G h hvalid e
  let closed : ℝ → ℝ := fun s => ∫ v, (if w ∉ covered (clockState E v s) then (1:ℝ) else 0) ∂μ
  let opened : ℝ → ℝ := fun t => ∫ v, (if w ∉ covered (clockOpenState E v t) then (1:ℝ) else 0) ∂μ
  let S := (h.accepted.filter (fun e => h.time e < T)).image h.time
  have hreg := lifted_injective G h hvalid hsub hinj
  have htimes := lifted_times G h hvalid hsub htime
  have hcoords := lifted_accepted_coordinates G h hvalid hsub
  have hcut := lifted_cutoffs G h hvalid hsub htime hinj hsupport
  have hzero : 1 ≤ closed 0 := by
    have heq : closed 0 = ∫ _ : Edge n → ℝ, (1:ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [htimes] with v hv
      have hp : clockPrefix E v 0 = [] := by
        unfold clockPrefix
        apply List.filter_eq_nil_iff.mpr
        intro e he
        simp only [decide_eq_true_eq]
        exact not_le_of_gt (hv e).1
      simp [clockState,hp,greedy,covered]
    rw [heq]
    simp [μ]
  apply finite_gap_survival S T hT hT1 ?_ closed opened hzero ?_ ?_
  · intro s hs
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hs
    have heh := Finset.mem_filter.mp he
    exact ⟨(htime e heh.1).1,heh.2⟩
  · intro s hs
    obtain ⟨f,hf,hfs⟩ := Finset.mem_image.mp hs
    have hfh := Finset.mem_filter.mp hf
    have hwf : w ∉ f := by
      intro hwf
      apply hw
      simp only [covered,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨f,Finset.mem_filter.mp hf,hwf⟩
    have heq : opened s = closed s := by
      apply integral_congr_ae
      filter_upwards [hreg,hcoords] with v hv hvc
      have hiff := clockOpen_closed_vertex E v s w (fun e he het => by
        have hef : e=f := hv (het.trans (hfs.symm.trans (hvc f hfh.1).symm))
        rw [hef]
        exact hwf)
      simp only [hiff]
    exact heq.le
  · intro a b ha hab hb hnone
    have hgap : historyClosed h a = h.accepted.filter (fun e => h.time e < b) := by
      ext e
      simp only [historyClosed,Finset.mem_filter]
      constructor
      · rintro ⟨he,hea⟩
        exact ⟨he,hea.trans_lt hab⟩
      · rintro ⟨he,heb⟩
        refine ⟨he,?_⟩
        by_contra hna
        have has : h.time e ∈ S := Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,heb.trans_le hb⟩,rfl⟩
        exact hnone _ has ⟨lt_of_not_ge hna,heb⟩
    have hwD : w ∉ covered (historyClosed h a) := by
      apply fun hc => hw (covered_mono (show historyClosed h a ⊆ h.accepted.filter (fun e => h.time e < T) from ?_) hc)
      intro e he
      have hh := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨hh.1,hh.2.trans_lt (hab.trans_le hb)⟩
    have hzD : z ∉ covered (historyClosed h a) := by
      intro hc
      obtain ⟨e,he,hze⟩ : ∃ e ∈ historyClosed h a, z ∈ e := by simpa [covered] using hc
      have heG : e ∈ G.edgeSet := by simpa [graphEdges] using hsub (Finset.mem_filter.mp he).1
      exact hz e heG hze
    have hleft : ∀ᵐ v ∂μ, clockState (E.filter (fun e => z ∉ e)) v a = historyClosed h a := by
      filter_upwards [hcut] with v hv
      rw [←hH]
      exact hv.1 a
    have hMgood : ∀ᵐ v ∂μ, IsMatching (clockOpenState E v b) ∧ clockState E v a ⊆ clockOpenState E v b ∧
        ∀ e ∈ clockOpenState E v b, e ∈ E ∧ v e ≤ b ∧ (z ∉ e → ¬free (historyClosed h a) e) := by
      filter_upwards [hreg,hcut] with v hv hc
      apply clockOpen_good E (historyClosed h a) hE v a b hab z hv.injOn
      rw [←hH,hc.2 b,←hgap]
    exact clock_survival_step E (historyClosed h a) hE z w hwz hwD hzD (liftedCoordinate G h) a b hab.le (hb.trans_lt hT1)
      (hreg.mono (fun v hv => hv.injOn)) hleft (fun v => clockOpenState E v b) (measurable_clockOpenState E b) hMgood
      (fun u hu _ => lifted_hole_coordinate G h hm a ha z w u hz hwD hu)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def fullClockCount {n : ℕ} (E : EdgeSet n) (y : Fin n) (v : Edge n → ℝ) : ℝ :=
  count {y} (greedy (orderFor E (fun e => v e.val)))

lemma measurable_fullClockCount {n : ℕ} (E : EdgeSet n) (y : Fin n) : Measurable (fullClockCount E y) := by
  exact (measurable_orderFor_score E (fun l => count {y} (greedy l))).comp
    (measurable_pi_iff.mpr (fun e => measurable_pi_apply e.val))

lemma integrable_fullClockCount {n : ℕ} (E : EdgeSet n) (y : Fin n)
    (μ : Measure (Edge n → ℝ)) [IsFiniteMeasure μ] : Integrable (fullClockCount E y) μ := by
  apply Integrable.of_bound (measurable_fullClockCount E y).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun v => by unfold fullClockCount; rw [count_singleton]; split_ifs <;> norm_num)

lemma conditional_vertex_bound {n : ℕ} (G : SimpleGraph (Fin n)) (E : EdgeSet n)
    (hE : ∀ e ∈ E, ¬e.IsDiag) (z y : Fin n)
    (hH : graphEdges G = E.filter (fun e => z ∉ e)) (hz : ∀ e ∈ G.edgeSet, z ∉ e)
    (h : History n) (hm : IsMatching h.accepted) (hsub : h.accepted ⊆ graphEdges G)
    (htime : ∀ e ∈ h.accepted, 0 < h.time e ∧ h.time e < 1) (hinj : Set.InjOn h.time h.accepted)
    (hvalid : ∀ e : G.edgeSet, e.val ∉ h.accepted → lowerTime 1 h e.val < 1)
    (hsupport : ∀ᵐ t ∂residualLaw G 1 h, history G 1 t = h) :
    1-matchTime 1 h y ≤ ∫ v, fullClockCount E y v ∂Measure.pi (liftedCoordinate G h) := by
  haveI (e : Edge n) := liftedCoordinate_probability G h hvalid e
  by_cases hy : y ∈ covered h.accepted
  · obtain ⟨f,hf,hyf⟩ : ∃ f ∈ h.accepted, y ∈ f := by simpa [covered] using hy
    obtain ⟨w,hfw⟩ := Sym2.mem_iff_exists.mp hyf
    subst f
    have hfG : s(y,w) ∈ G.edgeSet := by simpa [graphEdges] using hsub hf
    have hwz : w ≠ z := by intro heq; exact hz _ hfG (by simp [heq])
    have hw : w ∉ covered (h.accepted.filter (fun e => h.time e < h.time s(y,w))) := by
      intro hc
      obtain ⟨e,he,hwe⟩ : ∃ e ∈ h.accepted.filter (fun e => h.time e < h.time s(y,w)), w ∈ e := by simpa [covered] using hc
      have heh := Finset.mem_filter.mp he
      have heq : e=s(y,w) := by
        by_contra hne
        exact hm.2 e heh.1 s(y,w) hf hne w hwe (by simp)
      rw [heq] at heh
      exact (lt_irrefl _ heh.2)
    have hsurv := conditional_survival G E hE z w hwz hH hz h hm hsub htime hinj hvalid hsupport
      (h.time s(y,w)) (htime _ hf).1 (htime _ hf).2 hw
    have hcmp : (∫ v, (if w ∉ covered (clockOpenState E v (h.time s(y,w))) then (1:ℝ) else 0) ∂Measure.pi (liftedCoordinate G h)) ≤
        ∫ v, fullClockCount E y v ∂Measure.pi (liftedCoordinate G h) := by
      apply integral_mono_ae
        (integrable_finite_comp _ _ (measurable_clockOpenState E _) (fun M => if w ∉ covered M then (1:ℝ) else 0))
        (integrable_fullClockCount E y _)
      filter_upwards [lifted_injective G h hvalid hsub hinj,lifted_accepted_coordinates G h hvalid hsub] with v hv hc
      unfold fullClockCount
      rw [count_singleton]
      by_cases hw : w ∉ covered (clockOpenState E v (h.time s(y,w)))
      · have hve := hc s(y,w) hf
        have heE : s(y,w) ∈ E := by
          have hh := hsub hf
          rw [hH] at hh
          exact (Finset.mem_filter.mp hh).1
        have hmat := clock_partner_matched E hE v hv.injOn y w heE (by rwa [hve])
        simp [hw,hmat]
      · simp only [if_neg hw]
        split_ifs <;> norm_num
    rw [matchTime_accepted_vertex 1 h hm s(y,w) hf (htime _ hf).2.le y (by simp)]
    exact hsurv.trans hcmp
  · rw [matchTime_free_vertex 1 h y hy,sub_self]
    exact integral_nonneg (fun v => by unfold fullClockCount; rw [count_singleton]; split_ifs <;> norm_num)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma fullClockCount_bound {n : ℕ} (E : EdgeSet n) (y : Fin n) (v : Edge n → ℝ) :
    ‖fullClockCount E y v‖ ≤ 1 := by
  unfold fullClockCount
  rw [count_singleton]
  split_ifs <;> norm_num

lemma deletion_history_bound {n : ℕ} (G : SimpleGraph (Fin n)) (E : EdgeSet n)
    (hE : ∀ e ∈ E, ¬e.IsDiag) (z y : Fin n)
    (hH : graphEdges G = E.filter (fun e => z ∉ e)) (hz : ∀ e ∈ G.edgeSet, z ∉ e) :
    (∫ h, (1-matchTime 1 h y) ∂historyLaw G 1) ≤
      ∫ v, fullClockCount E y v ∂Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1)) := by
  rw [lifted_integral G (fullClockCount E y) (measurable_fullClockCount E y) 1 (fullClockCount_bound E y)]
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun h => sub_nonneg.mpr ((le_matchTime_iff (matchTime 1 h y) 1 h y).mp le_rfl).1))
    (lifted_mean_integrable G (fullClockCount E y) (measurable_fullClockCount E y) 1 (fullClockCount_bound E y))
  filter_upwards [full_history_regular G,full_history_valid G,full_residual_support G] with h hr hv hs
  exact conditional_vertex_bound G E hE z y hH hz h hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 hv hs

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma deleted_reference_expected {n : ℕ} (E F : EdgeSet n) (x y z : Fin n) (hxy : x ≠ y)
    (hE : ∀ e ∈ E, ¬e.IsDiag) (hFloop : ∀ e ∈ F, ¬e.IsDiag) (hF : ∀ e ∈ F, x ∈ e)
    (href : s(x,y) ∉ E.filter (fun e => z ∉ e) ∪ F)
    (q : ℝ) (hq : (3/5:ℝ) ≤ q) (hq1 : q ≤ 1) :
    3-(∫ v, fullClockCount E y v ∂Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))) ≤
      ∫ v, referenceScore x y q (clockGreedy (insert s(x,y) (E.filter (fun e => z ∉ e) ∪ F)) v)
        (clockGreedy (E.filter (fun e => z ∉ e) ∪ F) v)
        ∂Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1)) := by
  let H := E.filter (fun e => z ∉ e)
  let G := graphOfEdges H
  have hH : ∀ e ∈ H, ¬e.IsDiag := fun e he => hE e (Finset.mem_filter.mp he).1
  have hGE : graphEdges G = H := graphEdges_graphOfEdges H hH
  have hz : ∀ e ∈ G.edgeSet, z ∉ e := by
    intro e he
    have heH := (mem_graphOfEdges H hH e).mp he
    exact (Finset.mem_filter.mp heH).2
  have hdel := deletion_history_bound G E hE z y hGE hz
  have href' := reference_expected H F x y hxy (fun e he => by
    rcases Finset.mem_union.mp he with he | he
    · exact hH e he
    · exact hFloop e he) hF href q hq hq1
  haveI := arrival_probability G
  haveI : IsProbabilityMeasure (historyLaw G 1) := by
    unfold historyLaw
    exact Measure.isProbabilityMeasure_map (measurable_history G 1).aemeasurable
  rw [integral_sub (integrable_const 1) (history_matchTime_integrable G y)] at hdel
  have hc : (∫ _ : History n, (1:ℝ) ∂historyLaw G 1) = 1 := by simp
  rw [hc] at hdel
  change 2+(∫ h, matchTime 1 h y ∂historyLaw G 1) ≤ _ at href'
  linarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma integral_projected_order {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] (A : Finset ι) (b : ℝ) (hb : b < 1)
    (C : ENNReal)
    (hmap : (Measure.pi μ).map (fun t : ι → ℝ => fun i : A => t i.val) =
      C • Measure.pi (fun _ : A => tailLaw b)) (f : List ι → ℝ) :
    (∫ t : ι → ℝ, f (orderFor A (fun i => t i.val)) ∂Measure.pi μ) = C.toReal*orderMean A f := by
  haveI := tailLaw_probability b hb
  haveI := tailLaw_atomless b
  have hproj : Measurable (fun t : ι → ℝ => fun i : A => t i.val) := measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)
  have hpi := integral_map hproj.aemeasurable
    ((measurable_orderFor_score A f).aestronglyMeasurable (μ:=(Measure.pi μ).map (fun t : ι → ℝ => fun i : A => t i.val)))
  rw [hmap,integral_smul_measure] at hpi
  rw [←hpi,iid_orderFor A (tailLaw b) f]
  rfl

lemma integral_active_tail_order {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (A : Finset ι) (b : ℝ) (hb : b < 1)
    (hactive : ∀ i : A, μ i.val = (μ i.val Set.univ) • tailLaw b) (f : List ι → ℝ) :
    (∫ t : ι → ℝ, f (orderFor A (fun i => t i.val)) ∂Measure.pi μ) =
      (Measure.pi μ).real Set.univ*orderMean A f := by
  haveI := tailLaw_probability b hb
  haveI (i : A) : SigmaFinite ((μ i.val Set.univ) • tailLaw b) := by
    rw [←hactive i]
    infer_instance
  have hp := finite_pi_projection μ A
  have hsel : Measure.pi (fun i : A => μ i.val) =
      (∏ i : A, μ i.val Set.univ) • Measure.pi (fun _ : A => tailLaw b) := by
    have hfun : (fun i : A => μ i.val) = (fun i : A => (μ i.val Set.univ) • tailLaw b) := funext hactive
    rw [hfun]
    exact finite_pi_scalars (fun _ : A => tailLaw b) _
  rw [hsel,smul_smul] at hp
  have hprod : (∏ i : {i : ι // i ∉ A}, μ i.val Set.univ)*(∏ i : A, μ i.val Set.univ) =
      (Measure.pi μ) Set.univ := by
    rw [Measure.pi_univ,mul_comm]
    convert! Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ A) (fun i => μ i Set.univ) using 1
    congr 2
    ext i
    simp
  have hp' : (Measure.pi μ).map (fun t : ι → ℝ => fun i : A => t i.val) =
      ((Measure.pi μ) Set.univ) • Measure.pi (fun _ : A => tailLaw b) := by
    convert! hp using 1
    congr 1
    convert! hprod.symm using 1
    congr 2
    ext i
    simp
  clear hp
  exact integral_projected_order μ A b hb _ hp' f

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma global_orderMean {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Finset ι) (f : List ι → ℝ) :
    (∫ v, f (orderFor E (fun e => v e.val)) ∂Measure.pi (fun _ : ι => volume.restrict (Set.Icc (0:ℝ) 1))) = orderMean E f := by
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by simp⟩
  have hh := integral_active_tail_order (fun _ : ι => volume.restrict (Set.Icc (0:ℝ) 1)) E 0 (by norm_num)
    (fun i => by simp only [measure_univ,one_smul]; exact uniform_eq_tail_zero) f
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,one_mul] using hh

lemma global_coupled_orderMean {n : ℕ} (E A B : EdgeSet n) (hAE : A ⊆ E) (hBE : B ⊆ E)
    (f : EdgeSet n → EdgeSet n → ℝ) :
    (∫ v, f (clockGreedy A v) (clockGreedy B v)
      ∂Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))) =
      orderMean E (fun σ => f (greedy (σ.filter (fun e => e ∈ A))) (greedy (σ.filter (fun e => e ∈ B)))) := by
  rw [←global_orderMean]
  apply integral_congr_ae
  filter_upwards [uniform_clock_injective (ι:=Edge n)] with v hv
  unfold clockGreedy
  rw [orderFor_subset E A hAE v hv.injOn,orderFor_subset E B hBE v hv.injOn]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma local_order_loopless {n : ℕ} (d : Local n) (hd : d.Valid) (σ : List (Edge n))
    (hσ : σ.Perm (d.base ∪ d.potential).toList) : ∀ e ∈ σ, ¬ e.IsDiag := by
  intro e he
  have hm := Finset.mem_toList.mp (hσ.mem_iff.mp he)
  exact local_edges_loopless d hd d.potential (Finset.Subset.refl _) e (Finset.mem_union.mp hm)

lemma oneRun_filtered {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n) :
    oneRun d σ r = greedy ((σ.filter (fun e => d.x2 ∉ e)).filter
      (fun e => e ∈ d.base ∨ e ∈ r.filter (fun e => d.x2 ∉ e))) := by
  unfold oneRun
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  by_cases hx : d.x2 ∈ e <;> by_cases hb : e ∈ d.base <;> by_cases hr : e ∈ r <;> simp [hx,hb,hr]

lemma baseRun_filtered {n : ℕ} (d : Local n) (hd : d.Valid) (σ : List (Edge n)) :
    baseRun d σ = greedy ((σ.filter (fun e => d.x2 ∉ e)).filter (fun e => e ∈ d.base)) := by
  unfold baseRun
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  by_cases hb : e ∈ d.base
  · have hx := (hd.2.1 e hb).2.2
    simp [hb,hx]
  · simp [hb]

lemma single_reference_full_coin_bound {n : ℕ} (d : Local n) (hd : d.Valid)
    (σ : List (Edge n)) (hσ : σ.Perm (d.base ∪ d.potential).toList)
    (y : Fin n) (hy : y ∈ d.Y) (href : s(d.x1,y) ∈ d.potential)
    (r : EdgeSet n) (hr : r ⊆ d.potential) (hnot : s(d.x1,y) ∉ r)
    (q : ℝ) (hq : 5/8 ≤ q) (hq1 : q ≤ 1) :
    q*(3*N d σ (insert s(d.x1,y) r)+2*count {y} (localRun d σ (insert s(d.x1,y) r)))+
    (1-q)*(3*N d σ r+2*count {y} (localRun d σ r))+count {y} (baseRun d σ) ≥ 3 := by
  let σ' := σ.filter (fun e => d.x2 ∉ e)
  let F := r.filter (fun e => d.x2 ∉ e)
  have hxy : d.x1 ≠ y := fun hh => hd.2.2.1 (hh ▸ hy)
  have hx2y : d.x2 ≠ y := fun hh => hd.2.2.2.1 (hh ▸ hy)
  have hx2ref : d.x2 ∉ s(d.x1,y) := by
    simp only [Sym2.mem_iff,not_or]
    exact ⟨hd.1.symm,hx2y⟩
  have hrefσ : s(d.x1,y) ∈ σ' := by
    apply List.mem_filter.mpr
    refine ⟨hσ.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_union_right _ href)),?_⟩
    simpa only [decide_eq_true_eq] using hx2ref
  have hB : ∀ e ∈ d.base, d.x1 ∉ e := fun e he => (hd.2.1 e he).2.1
  have hF : ∀ e ∈ F, d.x1 ∈ e := by
    intro e he
    obtain ⟨her,heNot⟩ := Finset.mem_filter.mp he
    obtain ⟨x,hx,z,hz,rfl⟩ := hd.2.2.2.2.2.2 e (hr her)
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp
    · have hx' : x = d.x2 := Finset.mem_singleton.mp hx
      exact (heNot (by simp [hx'])).elim
  have hFnot : s(d.x1,y) ∉ F := fun hh => hnot (Finset.mem_filter.mp hh).1
  have hloop : ∀ e ∈ σ', ¬ e.IsDiag := fun e he => local_order_loopless d hd σ hσ e (List.mem_of_mem_filter he)
  have hcore := one_reference_coin_bound d.x1 y hxy σ' hloop hrefσ d.base F hB hF hFnot q (by linarith) hq1
  have hplus : (insert s(d.x1,y) r).filter (fun e => d.x2 ∉ e) = insert s(d.x1,y) F := by
    simp only [Finset.filter_insert,hx2ref,not_false_eq_true,↓reduceIte,F]
  have heq0 : greedy (σ'.filter (fun e => e ∈ d.base ∨ e ∈ F)) = oneRun d σ r :=
    (oneRun_filtered d σ r).symm
  have heqplus : greedy (σ'.filter (fun e => e ∈ d.base ∨ e ∈ insert s(d.x1,y) F)) = oneRun d σ (insert s(d.x1,y) r) := by
    rw [←hplus]
    exact (oneRun_filtered d σ _).symm
  have heqB : greedy (σ'.filter (fun e => e ∈ d.base)) = baseRun d σ := (baseRun_filtered d hd σ).symm
  rw [heq0,heqplus,heqB] at hcore
  let d' : Local n := {d with marked := {y}}
  have hd' : d'.Valid := by
    refine ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,?_,?_,hd.2.2.2.2.2.2⟩
    · intro v hv; exact Finset.mem_singleton.mp hv ▸ hy
    · simp [d']
  have hrplus : insert s(d.x1,y) r ⊆ d.potential := Finset.insert_subset_iff.mpr ⟨href,hr⟩
  have hcmp := local_comparison d' hd' σ r hr
  have hcmpplus := local_comparison d' hd' σ (insert s(d.x1,y) r) hrplus
  change 3*N d σ r+2*count {y} (localRun d σ r) ≥
    3*count {d.x1} (oneRun d σ r)+2*count {y} (oneRun d σ r) at hcmp
  change 3*N d σ (insert s(d.x1,y) r)+2*count {y} (localRun d σ (insert s(d.x1,y) r)) ≥
    3*count {d.x1} (oneRun d σ (insert s(d.x1,y) r))+2*count {y} (oneRun d σ (insert s(d.x1,y) r)) at hcmpplus
  have hp := mul_le_mul_of_nonneg_left hcmpplus (show 0 ≤ q by linarith)
  have hm := mul_le_mul_of_nonneg_left hcmp (show 0 ≤ 1-q by linarith)
  linarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def swapLocal {n : ℕ} (d : Local n) : Local n := {d with x1 := d.x2,x2 := d.x1}

lemma swapLocal_valid {n : ℕ} (d : Local n) (hd : d.Valid) : (swapLocal d).Valid := by
  refine ⟨hd.1.symm,?_,hd.2.2.2.1,hd.2.2.1,hd.2.2.2.2.1,hd.2.2.2.2.2.1,?_⟩
  · intro e he
    have hh := hd.2.1 e he
    exact ⟨hh.1,hh.2.2,hh.2.1⟩
  · intro e he
    obtain ⟨x,hx,y,hy,hxy⟩ := hd.2.2.2.2.2.2 e he
    refine ⟨x,?_,y,hy,hxy⟩
    simpa only [swapLocal,Finset.pair_comm] using hx

lemma N_swapLocal {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n) :
    N (swapLocal d) σ r = N d σ r := by
  change count {d.x2,d.x1} (localRun d σ r) = count {d.x1,d.x2} (localRun d σ r)
  exact congrArg (fun A => count A (localRun d σ r)) (Finset.pair_comm _ _)

lemma single_reference_any_coin_bound {n : ℕ} (d : Local n) (hd : d.Valid)
    (σ : List (Edge n)) (hσ : σ.Perm (d.base ∪ d.potential).toList)
    (x y : Fin n) (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n))) (hy : y ∈ d.Y) (href : s(x,y) ∈ d.potential)
    (r : EdgeSet n) (hr : r ⊆ d.potential) (hnot : s(x,y) ∉ r)
    (q : ℝ) (hq : 5/8 ≤ q) (hq1 : q ≤ 1) :
    q*(3*N d σ (insert s(x,y) r)+2*count {y} (localRun d σ (insert s(x,y) r)))+
    (1-q)*(3*N d σ r+2*count {y} (localRun d σ r))+count {y} (baseRun d σ) ≥ 3 := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact single_reference_full_coin_bound d hd σ hσ y hy href r hr hnot q hq hq1
  · have hx' : x = d.x2 := Finset.mem_singleton.mp hx
    subst x
    have hh := single_reference_full_coin_bound (swapLocal d) (swapLocal_valid d hd) σ hσ y hy href r hr hnot q hq hq1
    rw [N_swapLocal,N_swapLocal] at hh
    convert! hh using 1

end
end FengLiYangMatching.General
open Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

def bernWeight {α : Type*} [DecidableEq α] (E : Finset α) (q : ℝ) (r : Finset α) : ℝ :=
  ∏ e ∈ E, if e ∈ r then q else 1-q

lemma bernWeight_nonneg {α : Type*} [DecidableEq α] (E : Finset α) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (r : Finset α) : 0 ≤ bernWeight E q r := by
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> linarith

lemma bernWeight_insert_selected {α : Type*} [DecidableEq α] (E : Finset α) (e : α) (he : e ∉ E)
    (q : ℝ) (r : Finset α) : bernWeight (insert e E) q (insert e r) = q*bernWeight E q r := by
  unfold bernWeight
  rw [Finset.prod_insert he]
  simp only [Finset.mem_insert_self,↓reduceIte]
  congr 1
  apply Finset.prod_congr rfl
  intro f hf
  have hfe : f ≠ e := fun h => he (h ▸ hf)
  simp only [Finset.mem_insert,hfe,false_or]

lemma bernWeight_insert_unselected {α : Type*} [DecidableEq α] (E : Finset α) (e : α) (he : e ∉ E)
    (q : ℝ) (r : Finset α) (hr : r ⊆ E) : bernWeight (insert e E) q r = (1-q)*bernWeight E q r := by
  unfold bernWeight
  rw [Finset.prod_insert he,if_neg (fun h => he (hr h))]

lemma bernoulli_sum_insert {α : Type*} [DecidableEq α] (E : Finset α) (e : α) (he : e ∉ E)
    (q : ℝ) (f : Finset α → ℝ) :
    (∑ r ∈ (insert e E).powerset, bernWeight (insert e E) q r*f r) =
      ∑ r ∈ E.powerset, bernWeight E q r*(q*f (insert e r)+(1-q)*f r) := by
  have hdis : Disjoint E.powerset (E.powerset.image (insert e)) := by
    rw [Finset.disjoint_left]
    intro r hr hi
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hi
    exact he ((Finset.mem_powerset.mp hr) (Finset.mem_insert_self _ _))
  have hinj : Set.InjOn (fun r : Finset α => insert e r) (↑E.powerset : Set (Finset α)) := by
    intro r hr s hs h
    have h' := congrArg (fun r : Finset α => r.erase e) h
    have her : e ∉ r := fun hh => he (Finset.mem_powerset.mp hr hh)
    have hes : e ∉ s := fun hh => he (Finset.mem_powerset.mp hs hh)
    simpa only [Finset.erase_insert her,Finset.erase_insert hes] using h'
  rw [Finset.powerset_insert,Finset.sum_union hdis,Finset.sum_image hinj]
  have hfalse : (∑ r ∈ E.powerset, bernWeight (insert e E) q r*f r) =
      ∑ r ∈ E.powerset, (1-q)*bernWeight E q r*f r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [bernWeight_insert_unselected E e he q r (Finset.mem_powerset.mp hr)]
  have htrue : (∑ r ∈ E.powerset, bernWeight (insert e E) q (insert e r)*f (insert e r)) =
      ∑ r ∈ E.powerset, q*bernWeight E q r*f (insert e r) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [bernWeight_insert_selected E e he]
  rw [hfalse,htrue,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma bernoulli_weights_sum {α : Type*} [DecidableEq α] (E : Finset α) (q : ℝ) :
    (∑ r ∈ E.powerset, bernWeight E q r) = 1 := by
  induction E using Finset.induction_on with
  | empty => simp [bernWeight]
  | @insert e E he ih =>
    have hh := bernoulli_sum_insert E e he q (fun _ => 1)
    simpa only [mul_one,sub_add_cancel,one_mul] using hh.trans (by simpa only [add_sub_cancel, mul_one] using ih)

lemma bernoulli_single_coin_bound {α : Type*} [DecidableEq α] (E : Finset α) (e : α) (he : e ∈ E)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : Finset α → ℝ) (K : ℝ)
    (hbound : ∀ r ⊆ E.erase e, q*f (insert e r)+(1-q)*f r ≥ K) :
    (∑ r ∈ E.powerset, bernWeight E q r*f r) ≥ K := by
  have hh := bernoulli_sum_insert (E.erase e) e (Finset.notMem_erase e E) q f
  rw [Finset.insert_erase he] at hh
  rw [hh]
  calc
    K = ∑ r ∈ (E.erase e).powerset, bernWeight (E.erase e) q r*K := by rw [←Finset.sum_mul,bernoulli_weights_sum,one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
      (hbound r (Finset.mem_powerset.mp hr)) (bernWeight_nonneg _ q hq0 hq1 r))

lemma bernoulli_const_bound {α : Type*} [DecidableEq α] (E : Finset α)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : Finset α → ℝ) (K : ℝ)
    (hbound : ∀ r ⊆ E, K ≤ f r) : K ≤ ∑ r ∈ E.powerset, bernWeight E q r*f r := by
  calc
    K = ∑ r ∈ E.powerset, bernWeight E q r*K := by rw [←Finset.sum_mul,bernoulli_weights_sum,one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
      (hbound r (Finset.mem_powerset.mp hr)) (bernWeight_nonneg E q hq0 hq1 r))

lemma bernoulli_add_const {α : Type*} [DecidableEq α] (E : Finset α)
    (q : ℝ) (f : Finset α → ℝ) (K : ℝ) :
    (∑ r ∈ E.powerset, bernWeight E q r*(f r+K)) = (∑ r ∈ E.powerset, bernWeight E q r*f r)+K := by
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,bernoulli_weights_sum,one_mul]

lemma bernoulli_nonempty_bound {α : Type*} [DecidableEq α] (E : Finset α)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : Finset α → ℝ) (K : ℝ)
    (hf0 : f ∅ = 0) (hbound : ∀ r ⊆ E, r ≠ ∅ → K ≤ f r) :
    K*(1-(1-q)^E.card) ≤ ∑ r ∈ E.powerset, bernWeight E q r*f r := by
  have hempty : (∅ : Finset α) ∈ E.powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
  have hw := Finset.sum_erase_add (f:=fun r => bernWeight E q r) E.powerset hempty
  rw [bernoulli_weights_sum] at hw
  have hf := Finset.sum_erase_add (f:=fun r => bernWeight E q r*f r) E.powerset hempty
  rw [hf0,mul_zero,add_zero] at hf
  have hsum := Finset.sum_le_sum (s:=E.powerset.erase ∅) (fun r hr =>
    mul_le_mul_of_nonneg_left
      (hbound r (Finset.mem_powerset.mp (Finset.mem_erase.mp hr).2) (Finset.mem_erase.mp hr).1)
      (bernWeight_nonneg E q hq0 hq1 r))
  rw [←Finset.sum_mul,hf] at hsum
  have hweight : bernWeight E q ∅ = (1-q)^E.card := by simp [bernWeight]
  rw [hweight] at hw
  have hmass : (∑ x ∈ E.powerset.erase ∅, bernWeight E q x) = 1-(1-q)^E.card := eq_sub_of_add_eq hw
  rw [hmass] at hsum
  simpa only [mul_comm] using hsum

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma orders_nonempty {n : ℕ} (d : Local n) : (orders d).Nonempty := by
  refine ⟨(d.base ∪ d.potential).toList,?_⟩
  simpa only [orders,List.mem_toFinset,List.mem_permutations] using (List.Perm.refl (d.base ∪ d.potential).toList)

lemma order_mem_perm {n : ℕ} (d : Local n) (σ : List (Edge n)) (hσ : σ ∈ orders d) :
    σ.Perm (d.base ∪ d.potential).toList := by simpa only [orders,List.mem_toFinset,List.mem_permutations] using hσ

lemma markedMean_add {n : ℕ} (d : Local n) (q : ℝ) (fixed : EdgeSet n)
    (f g : List (Edge n) → EdgeSet n → ℝ) :
    markedMean d q fixed (fun σ r => f σ r+g σ r) = markedMean d q fixed f+markedMean d q fixed g := by
  unfold markedMean
  simp only [mul_add,Finset.sum_add_distrib,add_div]

lemma markedMean_mono {n : ℕ} (d : Local n) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (fixed : EdgeSet n)
    (f g : List (Edge n) → EdgeSet n → ℝ) (hfg : ∀ σ r, f σ r ≤ g σ r) :
    markedMean d q fixed f ≤ markedMean d q fixed g := by
  unfold markedMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro σ hσ
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left (hfg σ (fixed ∪ r)) (bernWeight_nonneg (markedPotential d) q hq0 hq1 r)

lemma markedMean_baseline {n : ℕ} (d : Local n) (q : ℝ) (fixed : EdgeSet n) (y : Fin n) :
    markedMean d q fixed (fun σ r => count {y} (baseRun d σ)) = mu d y := by
  unfold markedMean mu
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  change (∑ r ∈ (markedPotential d).powerset, bernWeight (markedPotential d) q r * count {y} (baseRun d σ)) = _
  rw [←Finset.sum_mul,bernoulli_weights_sum,one_mul]

lemma markedMean_one_reference {n : ℕ} (d : Local n) (hd : d.Valid) (fixed : EdgeSet n)
    (hfixed : fixed ⊆ d.potential) (hmarked : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : 5/8 ≤ q) (hq1 : q ≤ 1) (x y : Fin n)
    (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n))) (hy : y ∈ d.marked) (href : s(x,y) ∈ d.potential) :
    markedMean d q fixed (fun σ r => 3*N d σ r+2*count {y} (localRun d σ r)+count {y} (baseRun d σ)) ≥ 3 := by
  let E := markedPotential d
  have hrefE : s(x,y) ∈ E := Finset.mem_filter.mpr ⟨href,y,hy,by simp⟩
  have hY : y ∈ d.Y := hd.2.2.2.2.1 hy
  have hinner (σ : List (Edge n)) (hσ : σ ∈ orders d) :
      (∑ r ∈ E.powerset, bernWeight E q r*(3*N d σ (fixed ∪ r)+
        2*count {y} (localRun d σ (fixed ∪ r))+count {y} (baseRun d σ))) ≥ 3 := by
    apply bernoulli_single_coin_bound E s(x,y) hrefE q (by linarith) hq1
    intro r hr
    have hrE : r ⊆ E := hr.trans (Finset.erase_subset _ _)
    have hF : fixed ∪ r ⊆ d.potential := Finset.union_subset hfixed (hrE.trans (Finset.filter_subset _ _))
    have hnotF : s(x,y) ∉ fixed ∪ r := by
      intro hh
      rcases Finset.mem_union.mp hh with hh | hh
      · exact Finset.disjoint_left.mp hmarked hh hrefE
      · exact (Finset.mem_erase.mp (hr hh)).1 rfl
    have hh := single_reference_any_coin_bound d hd σ (order_mem_perm d σ hσ) x y hx hY href
      (fixed ∪ r) hF hnotF q hq hq1
    simp only [Finset.union_insert] at *
    nlinarith
  have hsum := Finset.sum_le_sum (s:=orders d) (fun σ hσ => hinner σ hσ)
  have hpos : (0:ℝ) < (orders d).card := by exact_mod_cast Finset.card_pos.mpr (orders_nonempty d)
  change (∑ σ ∈ orders d, ∑ r ∈ E.powerset, bernWeight E q r*(3*N d σ (fixed ∪ r)+
      2*count {y} (localRun d σ (fixed ∪ r))+count {y} (baseRun d σ))) / (orders d).card ≥ 3
  apply (le_div_iff₀ hpos).mpr
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hsum

lemma count_union {n : ℕ} (A B : Finset (Fin n)) (hd : Disjoint A B) (F : EdgeSet n) :
    count (A ∪ B) F = count A F+count B F := by
  unfold count
  rw [Finset.union_inter_distrib_right,Finset.card_union_of_disjoint]
  · simp only [Nat.cast_add]
  · rw [Finset.disjoint_left]
    intro v hv hv'
    exact Finset.disjoint_left.mp hd (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv').1

lemma two_reference_weak_bound {n : ℕ} (d : Local n) (hd : d.Valid) (fixed : EdgeSet n)
    (hfixed : fixed ⊆ d.potential) (hmarked : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : 5/8 ≤ q) (hq1 : q ≤ 1) (yi yj : Fin n) (hne : yi ≠ yj)
    (hmarks : d.marked = {yi,yj}) (hedge : ∃ x ∈ ({d.x1,d.x2} : Finset (Fin n)), s(x,yi) ∈ d.potential) :
    markedMean d q fixed (fun σ r => 3*N d σ r+2*R d σ r+K d σ) ≥ 3+mu d yj := by
  obtain ⟨x,hx,href⟩ := hedge
  have hyi : yi ∈ d.marked := by rw [hmarks]; simp
  have hlow := markedMean_one_reference d hd fixed hfixed hmarked q hq hq1 x yi hx hyi href
  let f : List (Edge n) → EdgeSet n → ℝ := fun σ r => 3*N d σ r+2*count {yi} (localRun d σ r)+count {yi} (baseRun d σ)
  let g : List (Edge n) → EdgeSet n → ℝ := fun σ r => count {yj} (baseRun d σ)
  have hpair (F : EdgeSet n) : count d.marked F = count {yi} F+count {yj} F := by
    rw [hmarks]
    simpa only [Finset.singleton_union] using count_union {yi} {yj} (by simp [hne]) F
  have hm := markedMean_mono d q (by linarith) hq1 fixed (fun σ r => f σ r+g σ r)
    (fun σ r => 3*N d σ r+2*R d σ r+K d σ) (fun σ r => by
      dsimp only [f,g,R,K]
      rw [hpair,hpair]
      linarith [count_nonneg {yj} (localRun d σ r)])
  rw [markedMean_add,markedMean_baseline] at hm
  linarith

end
end FengLiYangMatching.General
open Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma bernoulli_sum_linear {α : Type*} [DecidableEq α] (E : Finset α) (q s t : ℝ)
    (f g : Finset α → ℝ) :
    (∑ r ∈ E.powerset, bernWeight E q r*(s*f r+t*g r)) =
      s*(∑ r ∈ E.powerset, bernWeight E q r*f r)+t*(∑ r ∈ E.powerset, bernWeight E q r*g r) := by
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro r hr <;> ring

lemma bernoulli_union_sum {α : Type*} [DecidableEq α] (A B : Finset α) (hd : Disjoint A B)
    (q : ℝ) (f : Finset α → ℝ) :
    (∑ r ∈ (A ∪ B).powerset, bernWeight (A ∪ B) q r*f r) =
      ∑ s ∈ A.powerset, bernWeight A q s*(∑ t ∈ B.powerset, bernWeight B q t*f (s ∪ t)) := by
  induction A using Finset.induction_on generalizing f with
  | empty => simp [bernWeight]
  | @insert e A he ih =>
    have heB : e ∉ B := fun hh => Finset.disjoint_left.mp hd (Finset.mem_insert_self _ _) hh
    have heAB : e ∉ A ∪ B := by simp [he,heB]
    have hdAB : Disjoint A B := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hd
    rw [Finset.insert_union,bernoulli_sum_insert (A ∪ B) e heAB,
      bernoulli_sum_linear,ih hdAB (fun r => f (insert e r)),ih hdAB f,
      bernoulli_sum_insert A e he]
    simp only [Finset.insert_union,bernoulli_sum_linear]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma localMean_marked_partition {n : ℕ} (d : Local n) (q : ℝ)
    (f : List (Edge n) → EdgeSet n → ℝ) :
    localMean d q f = ∑ fixed ∈ (d.potential \ markedPotential d).powerset,
      bernWeight (d.potential \ markedPotential d) q fixed * markedMean d q fixed f := by
  let A := d.potential \ markedPotential d
  let B := markedPotential d
  have hB : B ⊆ d.potential := Finset.filter_subset _ _
  have hU : A ∪ B = d.potential := Finset.sdiff_union_of_subset hB
  have hd : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 hf
  have hinner (σ : List (Edge n)) : (∑ r ∈ d.potential.powerset, bernWeight d.potential q r*f σ r) =
      ∑ s ∈ A.powerset, bernWeight A q s*(∑ t ∈ B.powerset, bernWeight B q t*f σ (s ∪ t)) := by
    have hh := bernoulli_union_sum A B hd q (f σ)
    rw [hU] at hh
    exact hh
  change (∑ σ ∈ orders d, ∑ r ∈ d.potential.powerset, bernWeight d.potential q r*f σ r)/(orders d).card = _
  simp_rw [hinner]
  rw [Finset.sum_comm]
  simp only [Finset.sum_div,Finset.mul_sum,mul_div_assoc]
  simp only [markedMean,A,B,bernWeight,Finset.mul_sum,Finset.sum_div,mul_div_assoc]

lemma localMean_from_marked_bound {n : ℕ} (d : Local n) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (f : List (Edge n) → EdgeSet n → ℝ) (C : ℝ)
    (hbound : ∀ fixed ⊆ d.potential \ markedPotential d, C ≤ markedMean d q fixed f) :
    C ≤ localMean d q f := by
  rw [localMean_marked_partition]
  exact bernoulli_const_bound (d.potential \ markedPotential d) q hq0 hq1 (fun fixed => markedMean d q fixed f) C hbound

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma markedMean_orderMean {n : ℕ} (d : Local n) (q : ℝ) (fixed : EdgeSet n)
    (f : List (Edge n) → EdgeSet n → ℝ) :
    markedMean d q fixed f = ∑ r ∈ (markedPotential d).powerset,
      bernWeight (markedPotential d) q r*orderMean (d.base ∪ d.potential) (fun σ => f σ (fixed ∪ r)) := by
  unfold markedMean orderMean
  change (∑ σ ∈ permLists (d.base ∪ d.potential), ∑ r ∈ (markedPotential d).powerset,
    bernWeight (markedPotential d) q r*f σ (fixed ∪ r))/(permLists (d.base ∪ d.potential)).card = _
  rw [Finset.sum_comm]
  simp only [Finset.sum_div,Finset.mul_sum,mul_div_assoc]

lemma coupled_orderMean_restrict {n : ℕ} (E U A B : EdgeSet n) (hUE : U ⊆ E)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (f : EdgeSet n → EdgeSet n → ℝ) :
    orderMean E (fun σ => f (greedy (σ.filter (fun e => e ∈ A))) (greedy (σ.filter (fun e => e ∈ B)))) =
      orderMean U (fun σ => f (greedy (σ.filter (fun e => e ∈ A))) (greedy (σ.filter (fun e => e ∈ B)))) := by
  have hh := orderMean_restrict E U hUE
    (fun σ => f (greedy (σ.filter (fun e => e ∈ A))) (greedy (σ.filter (fun e => e ∈ B))))
  simpa only [filter_filter_subset U A hAU,filter_filter_subset U B hBU] using hh

lemma markedPotential_active {n : ℕ} (d : Local n) (fixed : EdgeSet n)
    (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d)) :
    markedPotential {d with potential := fixed ∪ markedPotential d} = markedPotential d := by
  ext e
  change (e ∈ (fixed ∪ markedPotential d).filter (fun e => ∃ y ∈ d.marked, y ∈ e)) ↔ _
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨he | he,hP⟩
    · exact Finset.mem_filter.mpr ⟨hfixed he,hP⟩
    · exact he
  · intro he
    exact ⟨Or.inr he,(Finset.mem_filter.mp he).2⟩

lemma local_score_filter {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n) :
    3*N d σ r+2*R d σ r+K d σ =
      (fun A B => 3*count {d.x1,d.x2} A+2*count d.marked A+count d.marked B)
        (greedy (σ.filter (fun e => e ∈ d.base ∪ r)))
        (greedy (σ.filter (fun e => e ∈ d.base))) := by
  unfold N R K localRun baseRun
  congr 3 <;> congr 1 <;> apply congrArg greedy <;> apply List.filter_congr <;> intro e he <;> simp only [Finset.mem_union]

lemma markedMean_active {n : ℕ} (d : Local n) (fixed : EdgeSet n)
    (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d)) (q : ℝ) :
    markedMean d q fixed (fun σ r => 3*N d σ r+2*R d σ r+K d σ) =
      markedMean {d with potential := fixed ∪ markedPotential d} q fixed
        (fun σ r => 3*N {d with potential := fixed ∪ markedPotential d} σ r+
          2*R {d with potential := fixed ∪ markedPotential d} σ r+
          K {d with potential := fixed ∪ markedPotential d} σ) := by
  rw [markedMean_orderMean,markedMean_orderMean,markedPotential_active d fixed hfixed hdis]
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun x => bernWeight (markedPotential d) q r*x)
  have hrsub : r ⊆ markedPotential d := Finset.mem_powerset.mp hr
  have hU : d.base ∪ (fixed ∪ markedPotential d) ⊆ d.base ∪ d.potential :=
    Finset.union_subset (Finset.subset_union_left) (Finset.subset_union_right.trans' (Finset.union_subset hfixed (Finset.filter_subset _ _)))
  have hA : d.base ∪ (fixed ∪ r) ⊆ d.base ∪ (fixed ∪ markedPotential d) := by
    exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union (Finset.Subset.refl _) hrsub)
  have hB : d.base ⊆ d.base ∪ (fixed ∪ markedPotential d) := Finset.subset_union_left
  have hh := coupled_orderMean_restrict (d.base ∪ d.potential) (d.base ∪ (fixed ∪ markedPotential d))
    (d.base ∪ (fixed ∪ r)) d.base hU hA hB
    (fun A B => 3*count {d.x1,d.x2} A+2*count d.marked A+count d.marked B)
  simp_rw [local_score_filter]
  exact hh

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma singleMean_orderMean {n : ℕ} (d : Local n) (q : ℝ) (ref : Edge n) (fixed : EdgeSet n)
    (f : List (Edge n) → EdgeSet n → ℝ) :
    singleMean d q ref fixed f = orderMean (d.base ∪ d.potential)
      (fun σ => q*f σ (insert ref fixed)+(1-q)*f σ fixed) := rfl

lemma mu_orderMean {n : ℕ} (d : Local n) (y : Fin n) :
    mu d y = orderMean (d.base ∪ d.potential) (fun σ => count {y} (baseRun d σ)) := rfl

lemma lemma_4_3_proof {n : ℕ} (d : Local n) (hd : d.Valid) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3)
    (q : ℝ) (hq : 5/8 ≤ q) (hq1 : q ≤ 1)
    (x y z : Fin n) (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n)))
    (hy : y ∈ d.marked) (hz1 : z ≠ d.x1) (hz2 : z ≠ d.x2) (hzy : z ≠ y)
    (hedge : s(x,y) ∈ d.potential) (fixed : EdgeSet n)
    (hfixed : fixed ⊆ d.potential) (href : s(x,y) ∉ fixed) :
    singleMean d q s(x,y) fixed (fun σ r =>
      3 * count {x} (deletedRun d x z σ r) + 2 * count {y} (deletedRun d x z σ r))
      ≥ 3 - mu d y := by
  let H := d.base.filter (fun e => z ∉ e)
  let F := fixed.filter (fun e => z ∉ e ∧ x ∈ e)
  let A := insert s(x,y) (H ∪ F)
  let B := H ∪ F
  let U := d.base ∪ d.potential
  have hxY : x ∉ d.Y := by
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hd.2.2.1
    · rw [Finset.mem_singleton.mp h]; exact hd.2.2.2.1
  have hyY := hd.2.2.2.2.1 hy
  have hxy : x ≠ y := fun h => hxY (h.symm ▸ hyY)
  have hxz : x ≠ z := by
    rcases Finset.mem_insert.mp hx with h | h
    · exact h ▸ hz1.symm
    · exact (Finset.mem_singleton.mp h) ▸ hz2.symm
  have hzr : z ∉ s(x,y) := by simp [Sym2.mem_iff,hxz.symm,hzy]
  have hbasex : ∀ e ∈ d.base, x ∉ e := by
    intro e he
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact (hd.2.1 e he).2.1
    · rw [Finset.mem_singleton.mp h]; exact (hd.2.1 e he).2.2
  have hnotbase : s(x,y) ∉ d.base := fun he => hbasex _ he (by simp)
  have hnot : s(x,y) ∉ H ∪ F := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact hnotbase (Finset.mem_filter.mp he).1
    · exact href (Finset.mem_filter.mp he).1
  have hAU : A ⊆ U := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_union_right _ hedge
    · rcases Finset.mem_union.mp he with he | he
      · exact Finset.mem_union_left _ (Finset.mem_filter.mp he).1
      · exact Finset.mem_union_right _ (hfixed (Finset.mem_filter.mp he).1)
  have hBU : B ⊆ U := (Finset.subset_insert s(x,y) B).trans hAU
  have hbig := deleted_reference_expected d.base F x y z hxy
    (fun e he => (hd.2.1 e he).1)
    (fun e he => local_edges_loopless d hd fixed hfixed e (Or.inr (Finset.mem_filter.mp he).1))
    (fun e he => (Finset.mem_filter.mp he).2.2) hnot q (by linarith) hq1
  have hmu : (∫ v, fullClockCount d.base y v ∂Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1))) = mu d y := by
    have hh := global_coupled_orderMean U d.base d.base Finset.subset_union_left Finset.subset_union_left
      (fun M _ => count {y} M)
    exact hh
  have hmean := global_coupled_orderMean U A B hAU hBU (referenceScore x y q)
  have hr0 (σ : List (Edge n)) : deletedRun d x z σ fixed = greedy (σ.filter (fun e => e ∈ B)) := by
    unfold deletedRun
    congr 1
    apply List.filter_congr
    intro e he
    apply Bool.decide_congr
    simp only [B,H,F,Finset.mem_union,Finset.mem_filter]
    tauto
  have hr1 (σ : List (Edge n)) : deletedRun d x z σ (insert s(x,y) fixed) = greedy (σ.filter (fun e => e ∈ A)) := by
    unfold deletedRun
    congr 1
    apply List.filter_congr
    intro e he
    apply Bool.decide_congr
    simp only [A,H,F,Finset.mem_insert,Finset.mem_union,Finset.mem_filter]
    by_cases her : e=s(x,y)
    · subst e
      simp [hzr]
    · simp [her]
      tauto
  have hscore : singleMean d q s(x,y) fixed (fun σ r =>
      3*count {x} (deletedRun d x z σ r)+2*count {y} (deletedRun d x z σ r)) =
      orderMean U (fun σ => referenceScore x y q (greedy (σ.filter (fun e => e ∈ A))) (greedy (σ.filter (fun e => e ∈ B)))) := by
    rw [singleMean_orderMean]
    apply orderMean_congr
    intro σ hσ
    rw [hr0,hr1]
    rfl
  rw [hscore]
  rw [hmu] at hbig
  change 3-mu d y ≤ ∫ v, referenceScore x y q (clockGreedy A v) (clockGreedy B v)
    ∂Measure.pi (fun _ : Edge n => volume.restrict (Set.Icc (0:ℝ) 1)) at hbig
  rwa [hmean] at hbig

end
end FengLiYangMatching.General
open MeasureTheory Finset
open FengLiYangMatching.General
theorem solution {n : ℕ} (d : Local n) (hd : d.Valid) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3)
    (q : ℝ) (hq : 5/8 ≤ q) (hq1 : q ≤ 1)
    (x y z : Fin n) (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n)))
    (hy : y ∈ d.marked) (hz1 : z ≠ d.x1) (hz2 : z ≠ d.x2) (hzy : z ≠ y)
    (hedge : s(x,y) ∈ d.potential) (fixed : EdgeSet n)
    (hfixed : fixed ⊆ d.potential) (href : s(x,y) ∉ fixed) :
    singleMean d q s(x,y) fixed (fun σ r =>
      3 * count {x} (deletedRun d x z σ r) + 2 * count {y} (deletedRun d x z σ r))
      ≥ 3 - mu d y := by
  exact FengLiYangMatching.General.lemma_4_3_proof d hd a b p ha hab hb hp0 hp2 q hq hq1 x y z hx hy hz1 hz2 hzy hedge fixed hfixed href
