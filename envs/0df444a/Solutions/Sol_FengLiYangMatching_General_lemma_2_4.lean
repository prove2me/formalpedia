-- Prove2me | solution 1 for FengLiYangMatching.General.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:14:37.024276+00:00
-- url     : https://prove2.me/submissions/7fae59ee-ae53-419c-932c-8ce929a8fc6c

import Definitions.Def_FengLiYangMatching_General_Process
import Definitions.Def_FengLiYangMatching_General_Local
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

open FengLiYangMatching.General


theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3)
    (t : Times G) :
    ((M1Y M a (history G b t)).card : ℝ) + (MYY M (history G b t)).card ≥
      2 * (OPT G : ℝ) - 2 * (shadowAt G t b).card - U G M t a + (M2 G M a b t).card := by
  exact vertex_accounting G M hM hmax a b (le_of_lt hab) t


