-- Prove2me | solution 1 for FengLiYangMatching.General.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T19:23:57.67284+00:00
-- url     : https://prove2.me/submissions/63e9bc1b-0c41-4d01-94ee-d76b89fec74b

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

lemma history_resampling_law {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) :
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
  have hT := refreshList_preserving G b hb hb1 Finset.univ.toList
  have hgood := refreshAll_coordinates G b hb hb1
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

lemma history_disintegration {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1)
    (S : Set (History n)) (hS : MeasurableSet S) (A : Set (Times G)) (hA : MeasurableSet A) :
    arrivalLaw G (A ∩ (history G b) ⁻¹' S) =
      ∫⁻ h in S, residualLaw G b h A ∂historyLaw G b := by
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
  have heq := congrArg (fun m : Measure (History n × Times G) => m (S ×ˢ A)) (history_resampling_law G b hb hb1)
  rw [Measure.map_apply hq (hS.prod hA),
    Measure.map_apply hg (hS.prod hA)] at heq
  have hleft : (fun t : Times G => (history G b t,t)) ⁻¹' (S ×ˢ A) = A ∩ (history G b) ⁻¹' S := by
    ext t
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_inter_iff]
    tauto
  rw [hleft] at heq
  have hinter (t : Times G) :
      arrivalLaw G ((fun u : Times G => q (t,u)) ⁻¹' (S ×ˢ A)) =
        S.indicator (fun h => residualLaw G b h A) (history G b t) := by
    have huf : Measurable (fun u : Times G => (history G b t,u)) := measurable_const.prodMk measurable_id
    have hu0 := (measurable_residualSample G b).comp huf
    have hu : Measurable (residualSample G b (history G b t)) := by
      convert! hu0 using 1
    have hr : residualLaw G b (history G b t) A =
        arrivalLaw G ((residualSample G b (history G b t)) ⁻¹' A) := by
      rw [←residual_sample_map G b hb1 _,Measure.map_apply hu hA]
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
      ∫⁻ t, S.indicator (fun h => residualLaw G b h A) (history G b t) ∂arrivalLaw G := by
    rw [Measure.prod_apply (hq (hS.prod hA))]
    apply lintegral_congr
    exact hinter
  have hm : Measurable (S.indicator (fun h => residualLaw G b h A)) :=
    (measurable_residualLaw G b hb1 A hA).indicator hS
  have hmap := lintegral_map' (μ:=arrivalLaw G) hm.aemeasurable (measurable_history G b).aemeasurable
  rw [←lintegral_indicator hS,historyLaw,hmap]
  exact heq.symm.trans hp

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma conditional_arrival_law {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Measurable (history G b) ∧
    (∀ A : Set (Times G), MeasurableSet A →
      Measurable (fun h : History n => residualLaw G b h A)) ∧
    (∀ᵐ h ∂historyLaw G b, IsProbabilityMeasure (residualLaw G b h)) ∧
    (∀ S : Set (History n), MeasurableSet S → ∀ A : Set (Times G), MeasurableSet A →
      arrivalLaw G (A ∩ (history G b) ⁻¹' S) =
        ∫⁻ h in S, residualLaw G b h A ∂historyLaw G b) := by
  exact ⟨measurable_history G b,measurable_residualLaw G b hb1,
    Filter.Eventually.of_forall (residual_probability G b hb1),history_disintegration G b hb0 hb1⟩

end
end FengLiYangMatching.General

open FengLiYangMatching.General
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3) :
    Measurable (history G b) ∧
    (∀ A : Set (Times G), MeasurableSet A →
      Measurable (fun h : History n => residualLaw G b h A)) ∧
    (∀ᵐ h ∂historyLaw G b, IsProbabilityMeasure (residualLaw G b h)) ∧
    (∀ S : Set (History n), MeasurableSet S → ∀ A : Set (Times G), MeasurableSet A →
      arrivalLaw G (A ∩ (history G b) ⁻¹' S) =
        ∫⁻ h in S, residualLaw G b h A ∂historyLaw G b) := by
  exact conditional_arrival_law G b (ha.trans (le_of_lt hab)) (hb.trans_lt (by norm_num))

