-- Prove2me | solution 1 for FengLiYangMatching.General.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:54:54.048716+00:00
-- url     : https://prove2.me/submissions/4e389bf9-1b92-4f50-a114-50d1431dc30b

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

open FengLiYangMatching.General
theorem solution {n : ℕ} (d : Local n) (hd : d.Valid) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3)
    (σ : List (Edge n)) (hσ : σ.Perm (d.base ∪ d.potential).toList)
    (r : EdgeSet n) (hr : r ⊆ d.potential) :
    3 * N d σ r + 2 * R d σ r ≥ 3 * N1 d σ r + 2 * R1 d σ r := by
  exact local_comparison d hd σ r hr

