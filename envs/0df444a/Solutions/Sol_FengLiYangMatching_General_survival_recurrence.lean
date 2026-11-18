-- Prove2me | solution 1 for FengLiYangMatching.General.survival_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:44:38.694324+00:00
-- url     : https://prove2.me/submissions/6021f3aa-e444-49eb-8e72-93cde0cd85b5

import Definitions.Def_FengLiYangMatching_General_Local
import Definitions.Def_FengLiYangMatching_General_Process
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

set_option maxHeartbeats 1400000 in
lemma survival_recurrence_proof {n : ℕ} (J : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) :
    survival J A u = survival J A 1 +
      ∑ e ∈ (graphEdges J).filter (fun e => ∃ v ∈ A, v ∈ e),
        ∫ s in u..(1:ℝ), survival (J.deleteEdges {e}) (A ∪ covered {e}) s := by
  let score : J.edgeSet → Times J → ℝ := fun e t =>
    if u ≤ t e ∧ (∃ v ∈ A, v ∈ e.val) ∧
      vacant (A ∪ covered {e.val}) (shadowAt (J.deleteEdges {e.val}) (restrictTimes J e t) (t e)) then 1 else 0
  have hscore (e : J.edgeSet) : Integrable (score e) (arrivalLaw J) := by
    by_cases he : ∃ v ∈ A, v ∈ e.val
    · simpa only [score,he,true_and] using integrable_edge_vacancy J e A u
    · simp only [score,he,false_and,and_false,↓reduceIte]
      exact integrable_zero _ _ _
  have hpoint : ∀ᵐ t ∂arrivalLaw J,
      (if vacant A (shadowAt J t u) then (1:ℝ) else 0) =
        (if vacant A (shadowAt J t 1) then (1:ℝ) else 0) + ∑ e : J.edgeSet, score e t := by
    filter_upwards [arrival_injective J,arrival_lt_one J] with t hinj hlt
    let T : Edge n → ℝ := fun e => if h : e ∈ J.edgeSet then t ⟨e,h⟩ else 0
    have hcoords (e : J.edgeSet) : T e.val = t e := by simp [T,e.property]
    have hTG : (fun e : J.edgeSet => T e.val) = t := funext hcoords
    have hT : Set.InjOn T J.edgeSet := by
      intro e he f hf heq
      have ht : t ⟨e,he⟩ = t ⟨f,hf⟩ := by simpa only [T,dif_pos he,dif_pos hf] using heq
      exact congrArg Subtype.val (hinj ht)
    have h1 : ∀ e ∈ J.edgeSet, T e < 1 := by
      intro e he
      simpa only [T,dif_pos he] using hlt ⟨e,he⟩
    have hRest (e : J.edgeSet) : (fun f : (J.deleteEdges {e.val}).edgeSet => T f.val) = restrictTimes J e t := by
      rw [←restrictTimes_from_global J e T,hTG]
    have hh := first_hit_graph J T hT h1 A u hu.2
    simpa only [hTG,hRest,hcoords,score] using hh
  have hh := integral_congr_ae hpoint
  rw [integral_add (integrable_vacancy J A 1) (integrable_finsetSum univ (fun e he => hscore e)),
    integral_finsetSum univ (fun e he => hscore e),vacancy_integral,vacancy_integral] at hh
  rw [hh]
  congr 1
  calc
    (∑ e : J.edgeSet, ∫ t, score e t ∂arrivalLaw J) =
      ∑ e : J.edgeSet, if (∃ v ∈ A, v ∈ e.val) then
        (∫ s in u..(1:ℝ), survival (J.deleteEdges {e.val}) (A ∪ covered {e.val}) s) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hinc : ∃ v ∈ A, v ∈ e.val
      · simp only [score,hinc,true_and,↓reduceIte]
        exact edge_vacancy_integral J e A u hu.1 hu.2
      · simp [score,hinc]
    _ = ∑ e ∈ graphEdges J, if (∃ v ∈ A, v ∈ e) then
        (∫ s in u..(1:ℝ), survival (J.deleteEdges {e}) (A ∪ covered {e}) s) else 0 := by
      symm
      apply Finset.sum_subtype (graphEdges J) (fun e => by simp [graphEdges])
    _ = _ := by rw [Finset.sum_filter]

end
end FengLiYangMatching.General
open FengLiYangMatching.General
theorem solution {n : ℕ} (J : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    survival J A t = survival J A 1 +
      ∑ e ∈ (graphEdges J).filter (fun e => ∃ v ∈ A, v ∈ e),
        ∫ s in t..(1:ℝ), survival (J.deleteEdges {e}) (A ∪ covered {e}) s := by
  exact survival_recurrence_proof J A t ht
