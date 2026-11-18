-- Prove2me | solution 1 for FengLiYangMatching.General.local_recovery_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T22:53:16.241074+00:00
-- url     : https://prove2.me/submissions/fa229ffe-ade1-4f68-b126-7530d9466ae5

import Mathlib
import Definitions.Def_FengLiYangMatching_General_Process
import Definitions.Def_FengLiYangMatching_General_Local
import Theorems.Thm_FengLiYangMatching_General_lemma_4_3
import Theorems.Thm_FengLiYangMatching_General_lemma_4_4
import Theorems.Thm_FengLiYangMatching_General_lemma_4_5
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
open Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma orderMean_mono {α : Type*} [DecidableEq α] (E : Finset α) (f g : List α → ℝ)
    (h : ∀ σ ∈ permLists E, f σ ≤ g σ) : orderMean E f ≤ orderMean E g := by
  unfold orderMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

lemma orderMean_linear {α : Type*} [DecidableEq α] (E : Finset α) (s t : ℝ) (f g : List α → ℝ) :
    orderMean E (fun σ => s*f σ+t*g σ) = s*orderMean E f+t*orderMean E g := by
  unfold orderMean
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,add_div,mul_div_assoc]

def orderCoinMean {α : Type*} [DecidableEq α] (E P : Finset α) (q : ℝ)
    (f : List α → Finset α → ℝ) : ℝ :=
  ∑ r ∈ P.powerset, bernWeight P q r*orderMean E (fun σ => f σ r)

lemma orderCoinMean_congr {α : Type*} [DecidableEq α] (E P : Finset α) (q : ℝ)
    (f g : List α → Finset α → ℝ) (h : ∀ r ⊆ P, ∀ σ ∈ permLists E, f σ r = g σ r) :
    orderCoinMean E P q f = orderCoinMean E P q g := by
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun x => bernWeight P q r*x)
  exact orderMean_congr E _ _ (h r (Finset.mem_powerset.mp hr))

lemma orderCoinMean_mono {α : Type*} [DecidableEq α] (E P : Finset α) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (f g : List α → Finset α → ℝ) (h : ∀ r ⊆ P, ∀ σ ∈ permLists E, f σ r ≤ g σ r) :
    orderCoinMean E P q f ≤ orderCoinMean E P q g := by
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left (orderMean_mono E _ _ (h r (Finset.mem_powerset.mp hr))) (bernWeight_nonneg P q hq hq1 r)

lemma orderCoinMean_const {α : Type*} [DecidableEq α] (E P : Finset α) (q C : ℝ) :
    orderCoinMean E P q (fun _ _ => C) = C := by
  unfold orderCoinMean
  simp_rw [orderMean_const]
  rw [←Finset.sum_mul,bernoulli_weights_sum,one_mul]

lemma orderCoinMean_first {α : Type*} [DecidableEq α] (E P : Finset α) (hE : E.Nonempty) (q : ℝ)
    (f : List α → Finset α → ℝ) :
    orderCoinMean E P q f = (∑ e ∈ E, orderCoinMean (E.erase e) P q (fun σ r => f (e::σ) r))/E.card := by
  unfold orderCoinMean
  simp_rw [orderMean_first E hE]
  simp only [Finset.mul_sum,Finset.sum_div,mul_div_assoc]
  rw [Finset.sum_comm]

lemma orderCoinMean_split_coin {α : Type*} [DecidableEq α] (E P : Finset α) (e : α) (he : e ∈ P)
    (q : ℝ) (f : List α → Finset α → ℝ) :
    orderCoinMean E P q f = q*orderCoinMean E (P.erase e) q (fun σ r => f σ (insert e r))+
      (1-q)*orderCoinMean E (P.erase e) q f := by
  unfold orderCoinMean
  have hP : insert e (P.erase e) = P := Finset.insert_erase he
  rw [←hP,bernoulli_sum_insert (P.erase e) e (Finset.notMem_erase e P)]
  simp only [orderMean_linear,bernoulli_sum_linear]
  rw [hP]

lemma markedMean_orderCoinMean {n : ℕ} (d : Local n) (fixed : EdgeSet n) (q : ℝ)
    (f : List (Edge n) → EdgeSet n → ℝ) :
    markedMean d q fixed f = orderCoinMean (d.base ∪ d.potential) (markedPotential d) q (fun σ r => f σ (fixed ∪ r)) :=
  markedMean_orderMean d q fixed f

end
end FengLiYangMatching.General
open Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma bernoulli_projection {α : Type*} [DecidableEq α] (P Q : Finset α) (hQP : Q ⊆ P) (q : ℝ)
    (f : Finset α → ℝ) :
    (∑ r ∈ P.powerset, bernWeight P q r*f (r ∩ Q)) = ∑ s ∈ Q.powerset, bernWeight Q q s*f s := by
  have hd : Disjoint Q (P \ Q) := by
    rw [Finset.disjoint_left]
    intro e he ht
    exact (Finset.mem_sdiff.mp ht).2 he
  have hu : Q ∪ (P \ Q) = P := Finset.union_sdiff_of_subset hQP
  have hh := bernoulli_union_sum Q (P \ Q) hd q (fun r => f (r ∩ Q))
  rw [hu] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro s hs
  apply congrArg (fun z => bernWeight Q q s*z)
  have hsQ := Finset.mem_powerset.mp hs
  have hm : (∑ t ∈ (P \ Q).powerset, bernWeight (P \ Q) q t*f ((s ∪ t) ∩ Q)) =
      ∑ t ∈ (P \ Q).powerset, bernWeight (P \ Q) q t*f s := by
    apply Finset.sum_congr rfl
    intro t ht
    have htP := Finset.mem_powerset.mp ht
    have heq : (s ∪ t) ∩ Q = s := by
      ext e
      simp only [Finset.mem_inter,Finset.mem_union]
      constructor
      · rintro ⟨he | he,hQ⟩
        · exact he
        · exact ((Finset.mem_sdiff.mp (htP he)).2 hQ).elim
      · intro he
        exact ⟨Or.inl he,hsQ he⟩
    rw [heq]
  rw [hm,←Finset.sum_mul,bernoulli_weights_sum,one_mul]

lemma orderCoinMean_project_coins {α : Type*} [DecidableEq α] (E P Q : Finset α) (hQP : Q ⊆ P) (q : ℝ)
    (f : List α → Finset α → ℝ) :
    orderCoinMean E P q (fun σ r => f σ (r ∩ Q)) = orderCoinMean E Q q f :=
  bernoulli_projection P Q hQP q (fun r => orderMean E (fun σ => f σ r))

lemma orderCoinMean_restrict_orders {α : Type*} [DecidableEq α] (E F P : Finset α) (hFE : F ⊆ E) (q : ℝ)
    (f : List α → Finset α → ℝ) :
    orderCoinMean E P q (fun σ r => f (σ.filter (fun e => e ∈ F)) r) = orderCoinMean F P q f := by
  unfold orderCoinMean
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun z => bernWeight P q r*z)
  exact orderMean_restrict E F hFE (fun σ => f σ r)

lemma orderCoinMean_project {α : Type*} [DecidableEq α] (E F P Q : Finset α) (hFE : F ⊆ E) (hQP : Q ⊆ P)
    (q : ℝ) (f : List α → Finset α → ℝ) :
    orderCoinMean E P q (fun σ r => f (σ.filter (fun e => e ∈ F)) (r ∩ Q)) = orderCoinMean F Q q f := by
  rw [orderCoinMean_project_coins E P Q hQP,orderCoinMean_restrict_orders E F Q hFE]

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

lemma edge_avoid_symm {n : ℕ} (e f : Edge n) :
    (∀ v, v ∈ e → v ∉ f) ↔ (∀ v, v ∈ f → v ∉ e) := by
  constructor <;> intro h v hv hw <;> exact h v hw hv

lemma greedy_fold_insert_edge {n : ℕ} (e : Edge n) (l : List (Edge n)) (D : EdgeSet n) :
    l.foldl (fun D f => if free D f then insert f D else D) (insert e D) =
      insert e ((l.filter (fun f => ∀ v, v ∈ e → v ∉ f)).foldl
        (fun D f => if free D f then insert f D else D) D) := by
  induction l generalizing D with
  | nil => rfl
  | cons f l ih =>
    simp only [List.foldl_cons,free_insert_iff,List.filter_cons,decide_eq_true_eq]
    by_cases hav : ∀ v, v ∈ e → v ∉ f
    · have hav' := (edge_avoid_symm e f).mp hav
      rw [if_pos hav,List.foldl_cons]
      by_cases hf : free D f
      · rw [if_pos ⟨hf,hav'⟩,if_pos hf,Finset.insert_comm]
        exact ih _
      · rw [if_neg (fun hh => hf hh.1),if_neg hf]
        exact ih _
    · have hav' : ¬∀ v, v ∈ f → v ∉ e := mt (edge_avoid_symm e f).mpr hav
      rw [if_neg hav,if_neg (fun hh => hav' hh.2)]
      exact ih D

lemma greedy_first_edge {n : ℕ} (e : Edge n) (l : List (Edge n)) :
    greedy (e::l) = insert e (greedy (l.filter (fun f => ∀ v, v ∈ e → v ∉ f))) := by
  change l.foldl (fun D f => if free D f then insert f D else D)
    (if free ∅ e then insert e ∅ else ∅) = _
  have hf : free ∅ e := by simp [free,covered]
  rw [if_pos hf]
  exact greedy_fold_insert_edge e l ∅

lemma greedy_avoids_edge {n : ℕ} (e : Edge n) (l : List (Edge n)) :
    free (greedy (l.filter (fun f => ∀ v, v ∈ e → v ∉ f))) e := by
  intro v hv hcov
  obtain ⟨f,hf,hvf⟩ := (show ∃ f ∈ greedy (l.filter (fun f => ∀ v, v ∈ e → v ∉ f)), v ∈ f from by
    simpa [covered] using hcov)
  have hseen := List.mem_toFinset.mp (greedy_seen _ hf)
  exact (of_decide_eq_true (List.mem_filter.mp hseen).2) v hv hvf

lemma count_insert_free {n : ℕ} (A : Finset (Fin n)) (F : EdgeSet n) (e : Edge n) (hf : free F e) :
    count A (insert e F) = count A {e}+count A F := by
  unfold count
  have hcov : covered (insert e F) = covered {e} ∪ covered F := by
    rw [covered_insert,covered_singleton,Finset.union_comm]
  rw [hcov,Finset.inter_union_distrib_left,Finset.card_union_of_disjoint]
  · simp only [Nat.cast_add]
  · rw [Finset.disjoint_left]
    intro v hv hw
    have hve : v ∈ e := by simpa only [covered_singleton,Sym2.mem_toFinset] using (Finset.mem_inter.mp hv).2
    exact hf v hve (Finset.mem_inter.mp hw).2

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def trimBy {n : ℕ} (W : Finset (Fin n)) (E : EdgeSet n) : EdgeSet n := E.filter (fun e => ∀ v ∈ W, v ∉ e)

def trimLocal {n : ℕ} (d : Local n) (W : Finset (Fin n)) : Local n :=
  {d with base := trimBy W d.base, potential := trimBy W d.potential, Y := d.Y \ W, marked := d.marked \ W}

lemma trimBy_subset {n : ℕ} (W : Finset (Fin n)) (E : EdgeSet n) : trimBy W E ⊆ E := Finset.filter_subset _ _

lemma trimBy_union {n : ℕ} (W : Finset (Fin n)) (E F : EdgeSet n) : trimBy W (E ∪ F) = trimBy W E ∪ trimBy W F := by
  ext e
  simp only [trimBy,Finset.mem_filter,Finset.mem_union]
  tauto

lemma trimLocal_valid {n : ℕ} (d : Local n) (hd : d.Valid) (W : Finset (Fin n))
    (hx1 : d.x1 ∉ W) (hx2 : d.x2 ∉ W) : (trimLocal d W).Valid := by
  rcases hd with ⟨h12,hbase,h1Y,h2Y,hmark,hcard,hpot⟩
  refine ⟨h12,?_,?_,?_,?_,?_,?_⟩
  · intro e he
    exact hbase e (Finset.mem_filter.mp he).1
  · exact fun h => h1Y (Finset.mem_sdiff.mp h).1
  · exact fun h => h2Y (Finset.mem_sdiff.mp h).1
  · intro y hy
    have hy' := Finset.mem_sdiff.mp hy
    exact Finset.mem_sdiff.mpr ⟨hmark hy'.1,hy'.2⟩
  · exact (Finset.card_le_card Finset.sdiff_subset).trans hcard
  · intro e he
    have he' := Finset.mem_filter.mp he
    obtain ⟨x,hx,y,hy,heq⟩ := hpot e he'.1
    refine ⟨x,hx,y,Finset.mem_sdiff.mpr ⟨hy,?_⟩,heq⟩
    intro hyW
    exact he'.2 y hyW (by rw [heq]; simp)

lemma trimLocal_partners {n : ℕ} (d : Local n) (hpartners : d.Partners) (W : Finset (Fin n))
    (hx1 : d.x1 ∉ W) (hx2 : d.x2 ∉ W) : (trimLocal d W).Partners := by
  obtain ⟨f,hfi,hf⟩ := hpartners
  let g : (trimLocal d W).marked → Fin n := fun y => f ⟨y.val,(Finset.mem_sdiff.mp y.property).1⟩
  refine ⟨g,?_,?_⟩
  · intro y z hyz
    have hyz' := hfi hyz
    have hval : y.val = z.val := congrArg (fun a : d.marked => a.val) hyz'
    exact Subtype.ext hval
  · intro y
    have hy' := Finset.mem_sdiff.mp y.property
    have hh := hf (⟨y.val,hy'.1⟩ : d.marked)
    refine ⟨hh.1,Finset.mem_filter.mpr ⟨hh.2,?_⟩⟩
    intro v hvW hve
    rcases Sym2.mem_iff.mp hve with hvg | hvy
    · have hgW : g y ∉ W := by
        rcases Finset.mem_insert.mp hh.1 with hx | hx
        · change f ⟨y.val,hy'.1⟩ ∉ W
          rw [hx]
          exact hx1
        · change f ⟨y.val,hy'.1⟩ ∉ W
          rw [Finset.mem_singleton.mp hx]
          exact hx2
      exact hgW (hvg ▸ hvW)
    · exact hy'.2 (hvy ▸ hvW)

lemma trim_markedPotential {n : ℕ} (d : Local n) (W : Finset (Fin n)) :
    markedPotential (trimLocal d W) = trimBy W (markedPotential d) := by
  ext e
  simp only [markedPotential,trimLocal,trimBy,Finset.mem_filter,Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨he,hW⟩,y,⟨hy,hyW⟩,hye⟩
    exact ⟨⟨he,y,hy,hye⟩,hW⟩
  · rintro ⟨⟨he,y,hy,hye⟩,hW⟩
    refine ⟨⟨he,hW⟩,y,⟨hy,?_⟩,hye⟩
    exact fun hyW => hW y hyW hye

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma greedy_trim_avoids {n : ℕ} (W : Finset (Fin n)) (σ : List (Edge n)) (E : EdgeSet n)
    (v : Fin n) (hv : v ∈ W) : v ∉ covered (greedy (σ.filter (fun e => e ∈ trimBy W E))) := by
  intro hcov
  obtain ⟨e,he,hve⟩ : ∃ e ∈ greedy (σ.filter (fun e => e ∈ trimBy W E)), v ∈ e := by simpa [covered] using hcov
  have hseen := List.mem_toFinset.mp (greedy_seen _ he)
  have heT := of_decide_eq_true (List.mem_filter.mp hseen).2
  exact (Finset.mem_filter.mp heT).2 v hv hve

lemma count_sdiff_of_avoids {n : ℕ} (A W : Finset (Fin n)) (M : EdgeSet n)
    (hW : ∀ v ∈ W, v ∉ covered M) : count (A \ W) M = count A M := by
  unfold count
  congr 1
  have heq : (A \ W) ∩ covered M = A ∩ covered M := by
    ext v
    simp only [Finset.mem_inter,Finset.mem_sdiff]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · rintro ⟨hA,hM⟩
      exact ⟨⟨hA,fun hv => hW v hv hM⟩,hM⟩
  rw [heq]

lemma localRun_base_first {n : ℕ} (d : Local n) (f : Edge n) (hf : f ∈ d.base)
    (σ : List (Edge n)) (r : EdgeSet n) :
    localRun d (f::σ) r = insert f (localRun (trimLocal d f.toFinset) σ (trimBy f.toFinset r)) := by
  unfold localRun
  simp only [List.filter_cons,decide_eq_true_eq,hf,true_or,↓reduceIte,greedy_first_edge]
  congr 1
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  simp only [trimLocal,trimBy,Finset.mem_filter,Sym2.mem_toFinset]
  tauto

lemma baseRun_first {n : ℕ} (d : Local n) (f : Edge n) (hf : f ∈ d.base)
    (σ : List (Edge n)) :
    baseRun d (f::σ) = insert f (baseRun (trimLocal d f.toFinset) σ) := by
  have hh := localRun_base_first d f hf σ ∅
  have he (d' : Local n) (l : List (Edge n)) : localRun d' l ∅ = baseRun d' l := by
    unfold localRun baseRun
    simp
  simp only [trimBy,Finset.filter_empty] at hh
  rw [he,he] at hh
  exact hh

lemma localRun_trim_avoids {n : ℕ} (d : Local n) (W : Finset (Fin n)) (σ : List (Edge n)) (r : EdgeSet n)
    (v : Fin n) (hv : v ∈ W) : v ∉ covered (localRun (trimLocal d W) σ (trimBy W r)) := by
  have heq : localRun (trimLocal d W) σ (trimBy W r) = greedy (σ.filter (fun e => e ∈ trimBy W (d.base ∪ r))) := by
    unfold localRun
    congr 1
    apply List.filter_congr
    intro e he
    simp only [trimLocal,trimBy,Finset.mem_filter,Finset.mem_union]
    apply Bool.decide_congr
    tauto
  rw [heq]
  exact greedy_trim_avoids W σ (d.base ∪ r) v hv

lemma baseRun_trim_avoids {n : ℕ} (d : Local n) (W : Finset (Fin n)) (σ : List (Edge n))
    (v : Fin n) (hv : v ∈ W) : v ∉ covered (baseRun (trimLocal d W) σ) :=
  greedy_trim_avoids W σ d.base v hv

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def localScore {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n) : ℝ := 3*N d σ r+2*R d σ r+K d σ

lemma count_single_edge {n : ℕ} (A : Finset (Fin n)) (f : Edge n) :
    count A {f} = ((A ∩ f.toFinset).card : ℝ) := by rw [count,covered_singleton]

lemma trim_marked_card {n : ℕ} (d : Local n) (f : Edge n) :
    count d.marked {f}+((trimLocal d f.toFinset).marked.card : ℝ) = (d.marked.card : ℝ) := by
  rw [count_single_edge]
  change ((d.marked ∩ f.toFinset).card : ℝ)+((d.marked \ f.toFinset).card : ℝ) = _
  exact_mod_cast (by have hh := Finset.card_sdiff_add_card_inter d.marked f.toFinset; omega : (d.marked ∩ f.toFinset).card+(d.marked \ f.toFinset).card = d.marked.card)

lemma localScore_base_first {n : ℕ} (d : Local n) (hd : d.Valid) (f : Edge n) (hf : f ∈ d.base)
    (σ : List (Edge n)) (r : EdgeSet n) :
    localScore d (f::σ) r = 3*count d.marked {f}+localScore (trimLocal d f.toFinset) σ (trimBy f.toFinset r) := by
  let d' := trimLocal d f.toFinset
  let r' := trimBy f.toFinset r
  have hlocal : free (localRun d' σ r') f := fun v hv => localRun_trim_avoids d f.toFinset σ r v (by simpa using hv)
  have hbase : free (baseRun d' σ) f := fun v hv => baseRun_trim_avoids d f.toFinset σ v (by simpa using hv)
  have hmarks (M : EdgeSet n) (hM : ∀ v ∈ f.toFinset, v ∉ covered M) : count d.marked M = count d'.marked M :=
    (count_sdiff_of_avoids d.marked f.toFinset M hM).symm
  have hnone : count {d.x1,d.x2} {f} = 0 := by
    unfold count
    have heq : ({d.x1,d.x2} : Finset (Fin n)) ∩ covered {f} = ∅ := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,covered_singleton,Sym2.mem_toFinset,Finset.notMem_empty,iff_false,not_and]
      intro hv
      rcases hv with rfl | rfl
      · exact (hd.2.1 f hf).2.1
      · exact (hd.2.1 f hf).2.2
    rw [heq]
    simp
  unfold localScore N R K
  rw [localRun_base_first d f hf σ r,baseRun_first d f hf σ]
  rw [count_insert_free {d.x1,d.x2} _ f hlocal,count_insert_free d.marked _ f hlocal,count_insert_free d.marked _ f hbase,hnone]
  rw [hmarks _ (fun v hv => localRun_trim_avoids d f.toFinset σ r v hv),hmarks _ (fun v hv => baseRun_trim_avoids d f.toFinset σ v hv)]
  dsimp only [d',r',trimLocal]
  ring

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma endpoint_not_Y {n : ℕ} (d : Local n) (hd : d.Valid) (x : Fin n)
    (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n))) : x ∉ d.Y := by
  rcases Finset.mem_insert.mp hx with hx | hx
  · rw [hx]; exact hd.2.2.1
  · rw [Finset.mem_singleton.mp hx]; exact hd.2.2.2.1

lemma base_avoids_endpoint {n : ℕ} (d : Local n) (hd : d.Valid) (x : Fin n)
    (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n))) (e : Edge n) (he : e ∈ d.base) : x ∉ e := by
  rcases Finset.mem_insert.mp hx with hx | hx
  · rw [hx]; exact (hd.2.1 e he).2.1
  · rw [Finset.mem_singleton.mp hx]; exact (hd.2.1 e he).2.2

lemma potential_other_endpoint {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (e : Edge n) (he : e ∈ d.potential) : xi ∉ e ↔ xj ∈ e := by
  have hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hxj : xj ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hxiY := endpoint_not_Y d hd xi hxi
  have hxjY := endpoint_not_Y d hd xj hxj
  obtain ⟨x,hx,y,hy,rfl⟩ := hd.2.2.2.2.2.2 e he
  rw [hpair] at hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    have hjy : xj ≠ y := fun h => hxjY (h.symm ▸ hy)
    simp [Sym2.mem_iff,hij.symm,hjy]
  · have hx : x=xj := Finset.mem_singleton.mp hx
    subst x
    have hiy : xi ≠ y := fun h => hxiY (h.symm ▸ hy)
    simp [Sym2.mem_iff,hij,hiy]

lemma potential_head_run {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj z : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (σ : List (Edge n)) (r : EdgeSet n) (hr : r ⊆ d.potential) (hf : s(xi,z) ∈ r) :
    localRun d (s(xi,z)::σ) r = insert s(xi,z) (deletedRun d xj z σ r) := by
  have hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  unfold localRun
  simp only [List.filter_cons,decide_eq_true_eq,hf,or_true,↓reduceIte,greedy_first_edge]
  congr 1
  unfold deletedRun
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  have hav : (∀ v, v ∈ s(xi,z) → v ∉ e) ↔ xi ∉ e ∧ z ∉ e := by
    simp only [Sym2.mem_iff]
    aesop
  rw [hav]
  by_cases heB : e ∈ d.base
  · have hxiE := base_avoids_endpoint d hd xi hxi e heB
    simp [heB,hxiE]
  · by_cases heR : e ∈ r
    · have hiff := potential_other_endpoint d hd xi xj hpair hij e (hr heR)
      simp only [heB,heR,false_or,true_and]
      tauto
    · simp [heB,heR]

lemma potential_head_baseRun {n : ℕ} (d : Local n) (hd : d.Valid) (x z : Fin n)
    (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n))) (σ : List (Edge n)) :
    baseRun d (s(x,z)::σ) = baseRun d σ := by
  have hn : s(x,z) ∉ d.base := fun h => base_avoids_endpoint d hd x hx _ h (by simp)
  unfold baseRun
  simp [hn]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def erasePotential {n : ℕ} (d : Local n) (e : Edge n) : Local n := {d with potential := d.potential.erase e}

lemma erasePotential_valid {n : ℕ} (d : Local n) (hd : d.Valid) (f : Edge n) : (erasePotential d f).Valid := by
  rcases hd with ⟨h12,hbase,h1Y,h2Y,hmark,hcard,hpot⟩
  exact ⟨h12,hbase,h1Y,h2Y,hmark,hcard,fun e he => hpot e (Finset.mem_erase.mp he).2⟩

lemma erase_markedPotential {n : ℕ} (d : Local n) (e : Edge n) : markedPotential (erasePotential d e) = (markedPotential d).erase e := by
  exact Finset.filter_erase (p:=fun f => ∃ y ∈ d.marked, y ∈ f) e d.potential

lemma erasePotential_union {n : ℕ} (d : Local n) (f : Edge n) (hf : f ∉ d.base) :
    (erasePotential d f).base ∪ (erasePotential d f).potential = (d.base ∪ d.potential).erase f := by
  ext e
  simp only [erasePotential,Finset.mem_union,Finset.mem_erase]
  constructor
  · rintro (he | ⟨hne,he⟩)
    · exact ⟨fun h => hf (h ▸ he),Or.inl he⟩
    · exact ⟨hne,Or.inr he⟩
  · rintro ⟨hne,he | he⟩
    · exact Or.inl he
    · exact Or.inr ⟨hne,he⟩

lemma erasePotential_score {n : ℕ} (d : Local n) (f : Edge n) (σ : List (Edge n)) (r : EdgeSet n) :
    localScore (erasePotential d f) σ r = localScore d σ r := rfl

lemma localScore_skip_head {n : ℕ} (d : Local n) (f : Edge n) (hfb : f ∉ d.base)
    (σ : List (Edge n)) (r : EdgeSet n) (hfr : f ∉ r) : localScore d (f::σ) r = localScore d σ r := by
  unfold localScore N R K localRun baseRun
  simp [hfb,hfr]

lemma unretained_head_mean {n : ℕ} (d : Local n) (fixed : EdgeSet n) (f : Edge n)
    (hfb : f ∉ d.base) (hff : f ∉ fixed) (q : ℝ) :
    orderCoinMean ((d.base ∪ d.potential).erase f) ((markedPotential d).erase f) q
      (fun σ r => localScore d (f::σ) (fixed ∪ r)) = markedMean (erasePotential d f) q fixed (localScore (erasePotential d f)) := by
  rw [markedMean_orderCoinMean,erasePotential_union d f hfb,erase_markedPotential]
  apply orderCoinMean_congr
  intro r hr σ hσ
  have hfr : f ∉ fixed ∪ r := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact hff he
    · exact (Finset.mem_erase.mp (hr he)).1 rfl
  rw [localScore_skip_head d f hfb σ (fixed ∪ r) hfr]
  rfl

lemma erasePotential_fixed_subset {n : ℕ} (d : Local n) (fixed : EdgeSet n) (f : Edge n)
    (hfixed : fixed ⊆ d.potential) (hff : f ∉ fixed) : fixed ⊆ (erasePotential d f).potential := by
  intro e he
  exact Finset.mem_erase.mpr ⟨fun hef => hff (hef ▸ he),hfixed he⟩

lemma erasePotential_fixed_disjoint {n : ℕ} (d : Local n) (fixed : EdgeSet n) (f : Edge n)
    (hdis : Disjoint fixed (markedPotential d)) : Disjoint fixed (markedPotential (erasePotential d f)) := by
  rw [erase_markedPotential]
  exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hdis

end
end FengLiYangMatching.General
open Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma orderMean_add_const {α : Type*} [DecidableEq α] (E : Finset α) (C : ℝ) (f : List α → ℝ) :
    orderMean E (fun σ => C+f σ) = C+orderMean E f := by
  have hh := orderMean_linear E 1 1 (fun _ => C) f
  simpa only [one_mul,orderMean_const] using hh

lemma orderCoinMean_add_const {α : Type*} [DecidableEq α] (E P : Finset α) (q C : ℝ)
    (f : List α → Finset α → ℝ) :
    orderCoinMean E P q (fun σ r => C+f σ r) = C+orderCoinMean E P q f := by
  unfold orderCoinMean
  simp_rw [orderMean_add_const]
  simp only [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,bernoulli_weights_sum,one_mul]

end
end FengLiYangMatching.General
open Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma orderCoinMean_linear {α : Type*} [DecidableEq α] (E P : Finset α) (q s t : ℝ)
    (f g : List α → Finset α → ℝ) :
    orderCoinMean E P q (fun σ r => s*f σ r+t*g σ r) = s*orderCoinMean E P q f+t*orderCoinMean E P q g := by
  unfold orderCoinMean
  simp_rw [orderMean_linear]
  exact bernoulli_sum_linear P q s t _ _

lemma orderCoinMean_add {α : Type*} [DecidableEq α] (E P : Finset α) (q : ℝ)
    (f g : List α → Finset α → ℝ) :
    orderCoinMean E P q (fun σ r => f σ r+g σ r) = orderCoinMean E P q f+orderCoinMean E P q g := by
  simpa only [one_mul] using orderCoinMean_linear E P q 1 1 f g

lemma orderCoinMean_no_coin {α : Type*} [DecidableEq α] (E P : Finset α) (q : ℝ) (f : List α → ℝ) :
    orderCoinMean E P q (fun σ _ => f σ) = orderMean E f := by
  unfold orderCoinMean
  rw [←Finset.sum_mul,bernoulli_weights_sum,one_mul]

lemma orderMean_ignore_edge {α : Type*} [DecidableEq α] (E : Finset α) (e : α) (f : List α → ℝ)
    (hignore : ∀ σ, f (σ.filter (fun a => a ≠ e)) = f σ) :
    orderMean E f = orderMean (E.erase e) f := by
  have hh := orderMean_restrict E (E.erase e) (Finset.erase_subset _ _) f
  rw [←hh]
  apply orderMean_congr
  intro σ hσ
  have hm := (mem_permLists E _).mp hσ
  have heq : σ.filter (fun a => a ∈ E.erase e) = σ.filter (fun a => a ≠ e) := by
    apply List.filter_congr
    intro a ha
    have haE : a ∈ E := by rw [←hm.2]; exact List.mem_toFinset.mpr ha
    simp [haE]
  rw [heq,hignore]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma localRun_union_unselected {n : ℕ} (d : Local n) (σ : List (Edge n)) (F r : EdgeSet n)
    (hrB : Disjoint r d.base) (hrF : Disjoint r F)
    (hnot : ∀ e ∈ r, e ∉ localRun d σ (F ∪ r)) : localRun d σ (F ∪ r) = localRun d σ F := by
  let l := σ.filter (fun e => e ∈ d.base ∨ e ∈ F ∪ r)
  have hh := greedy_skip_unselected l (fun e => e ∈ r) (fun e he her => hnot e her)
  change greedy l = localRun d σ F
  rw [hh]
  unfold localRun
  dsimp only [l]
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  by_cases her : e ∈ r
  · have heb : e ∉ d.base := fun h => Finset.disjoint_left.mp hrB her h
    have hef : e ∉ F := fun h => Finset.disjoint_left.mp hrF her h
    simp [her,heb,hef]
  · simp [her]

lemma count_ge_one {n : ℕ} (A : Finset (Fin n)) (F : EdgeSet n) (v : Fin n)
    (hvA : v ∈ A) (hvF : v ∈ covered F) : (1:ℝ) ≤ count A F := by
  unfold count
  exact_mod_cast (Finset.card_pos.mpr ⟨v,Finset.mem_inter.mpr ⟨hvA,hvF⟩⟩ : 0 < (A ∩ covered F).card)

lemma N_pair {n : ℕ} (d : Local n) (hd : d.Valid) (σ : List (Edge n)) (r : EdgeSet n) :
    N d σ r = count {d.x1} (localRun d σ r)+count {d.x2} (localRun d σ r) := by
  simpa only [N,Finset.singleton_union] using count_union {d.x1} {d.x2} (by simp [hd.1]) (localRun d σ r)

lemma selected_reference_score {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n)
    (x y : Fin n) (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n))) (he : s(x,y) ∈ localRun d σ r) :
    (5:ℝ) ≤ 3*N d σ r+2*count {y} (localRun d σ r) := by
  have hxCov : x ∈ covered (localRun d σ r) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,s(x,y),he,by simp⟩
  have hyCov : y ∈ covered (localRun d σ r) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,s(x,y),he,by simp⟩
  have hN := count_ge_one {d.x1,d.x2} (localRun d σ r) x hx hxCov
  rw [count_singleton,if_pos hyCov]
  change 1 ≤ N d σ r at hN
  linarith

lemma retained_reference_blocks {n : ℕ} (d : Local n) (σ : List (Edge n)) (F r : EdgeSet n)
    (x y : Fin n) (hrefσ : s(x,y) ∈ σ) (href : s(x,y) ∈ r)
    (hx : x ∉ covered (localRun d σ F)) (hy : y ∉ covered (localRun d σ F)) :
    localRun d σ (F ∪ r) ≠ localRun d σ F := by
  intro hh
  have hseen : s(x,y) ∈ σ.filter (fun e => e ∈ d.base ∨ e ∈ F ∪ r) :=
    List.mem_filter.mpr ⟨hrefσ,by simp [href]⟩
  have hb := greedy_blocks_seen _ _ hseen
  apply hb
  change free (localRun d σ (F ∪ r)) s(x,y)
  rw [hh]
  intro v hv
  rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma count_mono_first {n : ℕ} (A B : Finset (Fin n)) (M : EdgeSet n) (hAB : A ⊆ B) : count A M ≤ count B M := by
  unfold count
  exact_mod_cast (Finset.card_le_card (show A ∩ covered M ⊆ B ∩ covered M from fun v hv =>
    Finset.mem_inter.mpr ⟨hAB (Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2⟩))

lemma deletedRun_free_head {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj z : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (σ : List (Edge n)) (r : EdgeSet n) (hr : r ⊆ d.potential) : free (deletedRun d xj z σ r) s(xi,z) := by
  have hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  intro v hv hc
  obtain ⟨e,he,hve⟩ : ∃ e ∈ deletedRun d xj z σ r, v ∈ e := by simpa [covered] using hc
  have hs := List.mem_toFinset.mp (greedy_seen _ he)
  have hmem := of_decide_eq_true (List.mem_filter.mp hs).2
  change z ∉ e ∧ (e ∈ d.base ∨ (e ∈ r ∧ xj ∈ e)) at hmem
  rcases Sym2.mem_iff.mp hv with hv | hv
  · have hxiE : xi ∉ e := by
      rcases hmem.2 with heB | ⟨heR,hxj⟩
      · exact base_avoids_endpoint d hd xi hxi e heB
      · exact (potential_other_endpoint d hd xi xj hpair hij e (hr heR)).mpr hxj
    exact hxiE (hv ▸ hve)
  · exact hmem.1 (hv ▸ hve)

lemma count_head_marked {n : ℕ} (A : Finset (Fin n)) (x z : Fin n) (hx : x ∉ A) :
    count A {s(x,z)} = if z ∈ A then 1 else 0 := by
  unfold count
  rw [covered_singleton,Sym2.toFinset_mk_eq,Finset.inter_comm,Finset.insert_inter_of_notMem hx]
  by_cases hz : z ∈ A <;> simp [hz,Finset.singleton_inter]

lemma potential_head_score {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj z yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hz : z ∈ d.Y) (hyj : yj ∈ d.marked)
    (σ : List (Edge n)) (r : EdgeSet n) (hr : r ⊆ d.potential) (hf : s(xi,z) ∈ r) :
    3+2*(if z ∈ d.marked then 1 else 0)+
      (3*count {xj} (deletedRun d xj z σ r)+2*count {yj} (deletedRun d xj z σ r))+K d σ ≤
      localScore d (s(xi,z)::σ) r := by
  let D := deletedRun d xj z σ r
  have hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hxj : xj ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hfree := deletedRun_free_head d hd xi xj z hpair hij σ r hr
  have hxiM : xi ∉ covered D := hfree xi (by simp)
  have hxiMark : xi ∉ d.marked := fun hx => endpoint_not_Y d hd xi hxi (hd.2.2.2.2.1 hx)
  have hxjz : xj ≠ z := fun h => endpoint_not_Y d hd xj hxj (h.symm ▸ hz)
  have hNhead : count {d.x1,d.x2} {s(xi,z)} = 1 := by
    rw [hpair]
    have hp := count_union {xi} {xj} (by simp [hij]) {s(xi,z)}
    simp only [Finset.singleton_union,count_singleton,covered_singleton,Sym2.mem_toFinset,Sym2.mem_iff] at hp
    simpa [hij.symm,hxjz] using hp
  have hNtail : count {d.x1,d.x2} D = count {xj} D := by
    rw [hpair]
    have hp := count_union {xi} {xj} (by simp [hij]) D
    simpa only [Finset.singleton_union,count_singleton,hxiM,↓reduceIte,zero_add] using hp
  have hRhead := count_head_marked d.marked xi z hxiMark
  have hRtail : count {yj} D ≤ count d.marked D := count_mono_first {yj} d.marked D (by simpa using hyj)
  have hK : K d (s(xi,z)::σ) = K d σ := by unfold K; rw [potential_head_baseRun d hd xi z hxi σ]
  unfold localScore N R
  rw [potential_head_run d hd xi xj z hpair hij σ r hr hf,hK]
  rw [count_insert_free {d.x1,d.x2} _ s(xi,z) hfree,count_insert_free d.marked _ s(xi,z) hfree,hNhead,hRhead]
  change _ ≤ 3*(1+count {d.x1,d.x2} D)+2*((if z ∈ d.marked then 1 else 0)+count d.marked D)+K d σ
  rw [hNtail]
  linarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

def deletedScore {n : ℕ} (d : Local n) (x z y : Fin n) (σ : List (Edge n)) (r : EdgeSet n) : ℝ :=
  3*count {x} (deletedRun d x z σ r)+2*count {y} (deletedRun d x z σ r)

lemma deletedRun_ignore_edge {n : ℕ} (d : Local n) (x z : Fin n) (f : Edge n) (hzf : z ∈ f)
    (σ : List (Edge n)) (r : EdgeSet n) :
    deletedRun d x z (σ.filter (fun e => e ≠ f)) r = deletedRun d x z σ r := by
  unfold deletedRun
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  have himp : z ∉ e → e ≠ f := by intro hz heq; subst e; exact hz hzf
  tauto

lemma baseRun_ignore_edge {n : ℕ} (d : Local n) (f : Edge n) (hfb : f ∉ d.base) (σ : List (Edge n)) :
    baseRun d (σ.filter (fun e => e ≠ f)) = baseRun d σ := by
  unfold baseRun
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  have himp : e ∈ d.base → e ≠ f := fun he hef => hfb (hef ▸ he)
  tauto

lemma orderMean_deleted_head {n : ℕ} (d : Local n) (x z y : Fin n) (f : Edge n) (hzf : z ∈ f)
    (r : EdgeSet n) :
    orderMean (d.base ∪ d.potential) (fun σ => deletedScore d x z y σ r) =
      orderMean ((d.base ∪ d.potential).erase f) (fun σ => deletedScore d x z y σ r) := by
  apply orderMean_ignore_edge
  intro σ
  unfold deletedScore
  rw [deletedRun_ignore_edge d x z f hzf σ r]

lemma singleMean_eq_orderMean {n : ℕ} (d : Local n) (q : ℝ) (ref : Edge n) (fixed : EdgeSet n)
    (f : List (Edge n) → EdgeSet n → ℝ) :
    singleMean d q ref fixed f = orderMean (d.base ∪ d.potential)
      (fun σ => q*f σ (insert ref fixed)+(1-q)*f σ fixed) := rfl

lemma deleted_coin_mean {n : ℕ} (d : Local n) (hd : d.Valid) (x y z : Fin n)
    (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n))) (hy : y ∈ d.marked)
    (hz1 : z ≠ d.x1) (hz2 : z ≠ d.x2) (hzy : z ≠ y) (href : s(x,y) ∈ d.potential)
    (head : Edge n) (hzh : z ∈ head) (fixed Q : EdgeSet n)
    (hfixed : fixed ⊆ d.potential) (hQ : Q ⊆ d.potential) (hrefQ : s(x,y) ∈ Q)
    (hnot : s(x,y) ∉ fixed) (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    3-mu d y ≤ orderCoinMean ((d.base ∪ d.potential).erase head) Q q
      (fun σ r => deletedScore d x z y σ (fixed ∪ r)) := by
  unfold orderCoinMean
  apply bernoulli_single_coin_bound Q s(x,y) hrefQ q (by linarith) hq1
  intro r hr
  have hrQ : r ⊆ Q := hr.trans (Finset.erase_subset _ _)
  have hfr : fixed ∪ r ⊆ d.potential := Finset.union_subset hfixed (hrQ.trans hQ)
  have hn : s(x,y) ∉ fixed ∪ r := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact hnot he
    · exact (Finset.mem_erase.mp (hr he)).1 rfl
  have hh := lemma_4_3 d hd 0 (1/4) 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) q hq hq1 x y z hx hy hz1 hz2 hzy href (fixed ∪ r) hfr hn
  rw [singleMean_eq_orderMean] at hh
  change orderMean (d.base ∪ d.potential) (fun σ => q*deletedScore d x z y σ (insert s(x,y) (fixed ∪ r))+
    (1-q)*deletedScore d x z y σ (fixed ∪ r)) ≥ _ at hh
  rw [orderMean_linear] at hh
  rw [orderMean_deleted_head d x z y head hzh,orderMean_deleted_head d x z y head hzh] at hh
  have hu : fixed ∪ insert s(x,y) r = insert s(x,y) (fixed ∪ r) := Finset.union_insert s(x,y) fixed r
  simpa only [hu] using hh

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma potential_not_base {n : ℕ} (d : Local n) (hd : d.Valid) (e : Edge n) (he : e ∈ d.potential) : e ∉ d.base := by
  obtain ⟨x,hx,y,hy,rfl⟩ := hd.2.2.2.2.2.2 e he
  exact fun heB => base_avoids_endpoint d hd x hx _ heB (by simp)

lemma mu_erasePotential {n : ℕ} (d : Local n) (e : Edge n) (he : e ∉ d.base) (y : Fin n) :
    mu (erasePotential d e) y = mu d y := by
  change orderMean ((erasePotential d e).base ∪ (erasePotential d e).potential) (fun σ => count {y} (baseRun (erasePotential d e) σ)) = _
  rw [erasePotential_union d e he]
  symm
  apply orderMean_ignore_edge
  intro σ
  rw [baseRun_ignore_edge d e he]

lemma partners_pair {n : ℕ} (d : Local n) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hyij : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential) : d.Partners := by
  let f : d.marked → Fin n := fun y => if y.val=yi then xi else xj
  have hmem (y : d.marked) : y.val=yi ∨ y.val=yj := by simpa only [hmarks,Finset.mem_insert,Finset.mem_singleton] using y.property
  refine ⟨f,?_,?_⟩
  · intro a b hab
    change (if a.val=yi then xi else xj) = (if b.val=yi then xi else xj) at hab
    by_cases ha : a.val=yi <;> by_cases hb : b.val=yi
    · exact Subtype.ext (ha.trans hb.symm)
    · simp [ha,hb,hij] at hab
    · simp [ha,hb,hij.symm] at hab
    · exact Subtype.ext (((hmem a).resolve_left ha).trans ((hmem b).resolve_left hb).symm)
  · intro a
    change (if a.val=yi then xi else xj) ∈ ({d.x1,d.x2} : Finset (Fin n)) ∧
      s((if a.val=yi then xi else xj),a.val) ∈ d.potential
    by_cases ha : a.val=yi
    · simp [ha,hpair,hri]
    · have hb := (hmem a).resolve_left ha
      simp [ha,hb,hyij.symm,hpair,hrj]

lemma partners_labelling {n : ℕ} (d : Local n) (hd : d.Valid) (hp : d.Partners) (hc : d.marked.card=2) :
    ∃ xi xj yi yj : Fin n, ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj} ∧ xi ≠ xj ∧
      d.marked = {yi,yj} ∧ yi ≠ yj ∧ s(xi,yi) ∈ d.potential ∧ s(xj,yj) ∈ d.potential := by
  obtain ⟨yi,yj,hyij,hmarks⟩ := Finset.card_eq_two.mp hc
  obtain ⟨f,hfi,hf⟩ := hp
  have hyi : yi ∈ d.marked := by rw [hmarks]; simp
  have hyj : yj ∈ d.marked := by rw [hmarks]; simp
  let xi := f ⟨yi,hyi⟩
  let xj := f ⟨yj,hyj⟩
  have hi := hf (⟨yi,hyi⟩ : d.marked)
  have hj := hf (⟨yj,hyj⟩ : d.marked)
  have hij : xi ≠ xj := by
    intro heq
    have hh := hfi heq
    exact hyij (congrArg (fun y : d.marked => y.val) hh)
  have hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hi.1
      · exact Finset.mem_singleton.mp hx ▸ hj.1
    · simp [hd.1,hij]
  exact ⟨xi,xj,yi,yj,hpair,hij,hmarks,hyij,hi.2,hj.2⟩

lemma markedPotential_repr {n : ℕ} (d : Local n) (hd : d.Valid) (e : Edge n) (he : e ∈ markedPotential d) :
    ∃ x ∈ ({d.x1,d.x2} : Finset (Fin n)), ∃ y ∈ d.marked, e=s(x,y) := by
  have heP := Finset.mem_filter.mp he
  obtain ⟨x,hx,y,hy,heq⟩ := hd.2.2.2.2.2.2 e heP.1
  obtain ⟨m,hm,hme⟩ := heP.2
  have hmY := hd.2.2.2.2.1 hm
  have hmxy : m=x ∨ m=y := by rw [heq] at hme; exact Sym2.mem_iff.mp hme
  have hmy : m=y := hmxy.resolve_left (fun h => endpoint_not_Y d hd x hx (h ▸ hmY))
  exact ⟨x,hx,y,hmy ▸ hm,heq⟩

lemma markedPotential_four {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hmarks : d.marked = {yi,yj})
    (e : Edge n) (he : e ∈ markedPotential d) :
    e=s(xi,yi) ∨ e=s(xj,yj) ∨ e=s(xi,yj) ∨ e=s(xj,yi) := by
  obtain ⟨x,hx,y,hy,rfl⟩ := markedPotential_repr d hd e he
  rw [hpair] at hx
  rw [hmarks] at hy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> tauto

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma orderMean_K_pair {n : ℕ} (d : Local n) (yi yj : Fin n) (hij : yi ≠ yj)
    (hmarks : d.marked = {yi,yj}) :
    orderMean (d.base ∪ d.potential) (K d) = mu d yi+mu d yj := by
  have heq : K d = (fun σ => count {yi} (baseRun d σ)+count {yj} (baseRun d σ)) := by
    funext σ
    unfold K
    rw [hmarks]
    simpa only [Finset.singleton_union] using count_union {yi} {yj} (by simp [hij]) (baseRun d σ)
  rw [heq]
  have hh := orderMean_linear (d.base ∪ d.potential) 1 1 (fun σ => count {yi} (baseRun d σ)) (fun σ => count {yj} (baseRun d σ))
  simpa only [one_mul,mu,orderMean,orders,permLists] using hh

lemma orderCoinMean_K_head {n : ℕ} (d : Local n) (Q : EdgeSet n) (q : ℝ) (head : Edge n) (hnot : head ∉ d.base) :
    orderCoinMean ((d.base ∪ d.potential).erase head) Q q (fun σ _ => K d σ) = orderMean (d.base ∪ d.potential) (K d) := by
  rw [orderCoinMean_no_coin]
  symm
  apply orderMean_ignore_edge
  intro σ
  unfold K
  rw [baseRun_ignore_edge d head hnot]

lemma potential_head_mean_lower {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj z yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hz : z ∈ d.Y) (hym : yi ≠ yj) (hmarks : d.marked = {yi,yj}) (hzyj : z ≠ yj)
    (fixed Q : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hQ : Q ⊆ d.potential)
    (hhead : s(xi,z) ∈ fixed) (hrefQ : s(xj,yj) ∈ Q) (hnot : s(xj,yj) ∉ fixed)
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    6+2*(if z ∈ d.marked then 1 else 0)+mu d yi ≤
      orderCoinMean ((d.base ∪ d.potential).erase s(xi,z)) Q q (fun σ r => localScore d (s(xi,z)::σ) (fixed ∪ r)) := by
  have hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hxj : xj ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hyj : yj ∈ d.marked := by rw [hmarks]; simp
  have hheadB : s(xi,z) ∉ d.base := fun he => base_avoids_endpoint d hd xi hxi _ he (by simp)
  have hz1 : z ≠ d.x1 := fun he => hd.2.2.1 (he ▸ hz)
  have hz2 : z ≠ d.x2 := fun he => hd.2.2.2.1 (he ▸ hz)
  have hdel := deleted_coin_mean d hd xj yj z hxj hyj hz1 hz2 hzyj (hQ hrefQ) s(xi,z) (by simp)
    fixed Q hfixed hQ hrefQ hnot q hq hq1
  have hmono := orderCoinMean_mono ((d.base ∪ d.potential).erase s(xi,z)) Q q (by linarith) hq1
    (fun σ r => (3+2*(if z ∈ d.marked then 1 else 0))+(deletedScore d xj z yj σ (fixed ∪ r)+K d σ))
    (fun σ r => localScore d (s(xi,z)::σ) (fixed ∪ r)) (by
      intro r hr σ hσ
      have hret : fixed ∪ r ⊆ d.potential := Finset.union_subset hfixed (hr.trans hQ)
      have hhead' : s(xi,z) ∈ fixed ∪ r := Finset.mem_union_left _ hhead
      have hh := potential_head_score d hd xi xj z yj hpair hij hz hyj σ (fixed ∪ r) hret hhead'
      unfold deletedScore
      linarith)
  rw [orderCoinMean_add_const,orderCoinMean_add,orderCoinMean_K_head d Q q s(xi,z) hheadB,
    orderMean_K_pair d yi yj hym hmarks] at hmono
  linarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

def headValue {n : ℕ} (d : Local n) (fixed : EdgeSet n) (q : ℝ) (e : Edge n) : ℝ :=
  orderCoinMean ((d.base ∪ d.potential).erase e) (markedPotential d) q (fun σ r => localScore d (e::σ) (fixed ∪ r))

lemma markedMean_first {n : ℕ} (d : Local n) (fixed : EdgeSet n) (q : ℝ)
    (hE : (d.base ∪ d.potential).Nonempty) :
    markedMean d q fixed (localScore d) = (∑ e ∈ d.base ∪ d.potential, headValue d fixed q e)/(d.base ∪ d.potential).card := by
  rw [markedMean_orderCoinMean,orderCoinMean_first _ _ hE]
  rfl

lemma headValue_coin_lower {n : ℕ} (d : Local n) (fixed : EdgeSet n) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (e : Edge n) (he : e ∈ markedPotential d) (A B : ℝ)
    (hA : A ≤ orderCoinMean ((d.base ∪ d.potential).erase e) ((markedPotential d).erase e) q
      (fun σ r => localScore d (e::σ) (fixed ∪ insert e r)))
    (hB : B ≤ orderCoinMean ((d.base ∪ d.potential).erase e) ((markedPotential d).erase e) q
      (fun σ r => localScore d (e::σ) (fixed ∪ r))) : q*A+(1-q)*B ≤ headValue d fixed q e := by
  unfold headValue
  rw [orderCoinMean_split_coin _ _ e he]
  exact add_le_add (mul_le_mul_of_nonneg_left hA hq) (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hq1))

lemma mu_nonneg {n : ℕ} (d : Local n) (y : Fin n) : 0 ≤ mu d y := by
  unfold mu
  apply div_nonneg
  · exact Finset.sum_nonneg (fun σ hσ => count_nonneg {y} (baseRun d σ))
  · exact Nat.cast_nonneg _

lemma markedMean_of_heads {n : ℕ} (d : Local n) (fixed : EdgeSet n) (q C : ℝ)
    (hE : (d.base ∪ d.potential).Nonempty)
    (hhead : ∀ e ∈ d.base ∪ d.potential, C ≤ headValue d fixed q e) :
    C ≤ markedMean d q fixed (localScore d) := by
  rw [markedMean_first d fixed q hE]
  apply (le_div_iff₀ (show (0:ℝ) < (d.base ∪ d.potential).card by exact_mod_cast Finset.card_pos.mpr hE)).mpr
  have hh := Finset.sum_le_sum hhead
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh

lemma markedMean_of_grouped_heads {n : ℕ} (d : Local n) (fixed : EdgeSet n) (q C : ℝ)
    (hE : (d.base ∪ d.potential).Nonempty) (S : EdgeSet n) (hS : S ⊆ d.base ∪ d.potential)
    (hgroup : C*(S.card : ℝ) ≤ ∑ e ∈ S, headValue d fixed q e)
    (hother : ∀ e ∈ (d.base ∪ d.potential) \ S, C ≤ headValue d fixed q e) :
    C ≤ markedMean d q fixed (localScore d) := by
  rw [markedMean_first d fixed q hE]
  apply (le_div_iff₀ (show (0:ℝ) < (d.base ∪ d.potential).card by exact_mod_cast Finset.card_pos.mpr hE)).mpr
  have hrest := Finset.sum_le_sum hother
  simp only [Finset.sum_const,nsmul_eq_mul] at hrest
  have hsum := Finset.sum_sdiff hS (f:=fun e => headValue d fixed q e)
  have hcard := Finset.card_sdiff_add_card_eq_card hS
  have hcardR : (((d.base ∪ d.potential) \ S).card : ℝ)+(S.card : ℝ)=(d.base ∪ d.potential).card := by exact_mod_cast hcard
  have hm := congrArg (fun x : ℝ => C*x) hcardR
  rw [mul_add] at hm
  nlinarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section
set_option maxHeartbeats 1000000

lemma marked_edge_mem {n : ℕ} (d : Local n) (x y : Fin n) (hy : y ∈ d.marked)
    (he : s(x,y) ∈ d.potential) : s(x,y) ∈ markedPotential d := Finset.mem_filter.mpr ⟨he,y,hy,by simp⟩

lemma endpoint_edge_eq_iff {n : ℕ} (d : Local n) (hd : d.Valid) (x x' y y' : Fin n)
    (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n))) (hx' : x' ∈ ({d.x1,d.x2} : Finset (Fin n)))
    (hy : y ∈ d.Y) (hy' : y' ∈ d.Y) : s(x,y)=s(x',y') ↔ x=x' ∧ y=y' := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact (endpoint_not_Y d hd x hx (h.1.symm ▸ hy')).elim
  · exact Or.inl

lemma reference_retained_lower {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    8+mu d yi ≤ orderCoinMean ((d.base ∪ d.potential).erase s(xi,yi)) ((markedPotential d).erase s(xi,yi)) q
      (fun σ r => localScore d (s(xi,yi)::σ) (fixed ∪ insert s(xi,yi) r)) := by
  have hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hxj : xj ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hyi : yi ∈ d.marked := by rw [hmarks]; simp
  have hyj : yj ∈ d.marked := by rw [hmarks]; simp
  have hyiY := hd.2.2.2.2.1 hyi
  have hyjY := hd.2.2.2.2.1 hyj
  have hrjP := marked_edge_mem d xj yj hyj hrj
  have hne : s(xj,yj) ≠ s(xi,yi) := fun h => hij ((endpoint_edge_eq_iff d hd xj xi yj yi hxj hxi hyjY hyiY).mp h).1.symm
  have hret := potential_head_mean_lower d hd xi xj yi yi yj hpair hij hyiY hym hmarks hym
    (insert s(xi,yi) fixed) ((markedPotential d).erase s(xi,yi))
    (Finset.insert_subset hri hfixed) ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _)) (Finset.mem_insert_self _ _)
    (Finset.mem_erase.mpr ⟨hne,hrjP⟩) (by
      intro he
      rcases Finset.mem_insert.mp he with he | he
      · exact hne he
      · exact Finset.disjoint_left.mp hdis he hrjP) q hq hq1
  have hfun : (fun σ r => localScore d (s(xi,yi)::σ) (insert s(xi,yi) fixed ∪ r)) =
      (fun σ r => localScore d (s(xi,yi)::σ) (fixed ∪ insert s(xi,yi) r)) := by
    funext σ r
    congr 1
    simp only [Finset.union_insert,Finset.insert_union]
  rw [hfun] at hret
  simpa only [hyi,↓reduceIte,mul_one,show (6:ℝ)+2=8 by norm_num] using hret

lemma reference_unretained_weak {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    3+mu d yi ≤ orderCoinMean ((d.base ∪ d.potential).erase s(xi,yi)) ((markedPotential d).erase s(xi,yi)) q
      (fun σ r => localScore d (s(xi,yi)::σ) (fixed ∪ r)) := by
  have hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hxj : xj ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hyi : yi ∈ d.marked := by rw [hmarks]; simp
  have hyj : yj ∈ d.marked := by rw [hmarks]; simp
  have hrjP := marked_edge_mem d xj yj hyj hrj
  have hriP := marked_edge_mem d xi yi hyi hri
  have hne : s(xj,yj) ≠ s(xi,yi) := by
    intro h
    exact hij ((endpoint_edge_eq_iff d hd xj xi yj yi hxj hxi (hd.2.2.2.2.1 hyj) (hd.2.2.2.2.1 hyi)).mp h).1.symm
  have hnotB := potential_not_base d hd s(xi,yi) hri
  have hnotF : s(xi,yi) ∉ fixed := fun h => Finset.disjoint_left.mp hdis h hriP
  rw [unretained_head_mean d fixed s(xi,yi) hnotB hnotF q]
  have hh := lemma_4_4 (erasePotential d s(xi,yi)) (erasePotential_valid d hd _) 0 (1/4) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    fixed (erasePotential_fixed_subset d fixed _ hfixed hnotF) (erasePotential_fixed_disjoint d fixed _ hdis)
    q hq hq1 yj yi hym.symm (by simpa only [erasePotential,Finset.pair_comm] using hmarks)
    ⟨xj,hxj,Finset.mem_erase.mpr ⟨hne,hrj⟩⟩
  rw [mu_erasePotential d s(xi,yi) hnotB yi] at hh
  exact hh

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma reference_unretained_strong {n : ℕ} (d : Local n) (hd : d.Valid) (xi yi yj : Fin n)
    (hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n))) (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential)
    (honly : ∀ x ∈ ({d.x1,d.x2} : Finset (Fin n)), ∀ y ∈ ({yi,yj} : Finset (Fin n)),
      s(x,y) ∈ (erasePotential d s(xi,yi)).potential ↔ y=yj)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    4+mu d yi-mu d yj ≤ orderCoinMean ((d.base ∪ d.potential).erase s(xi,yi)) ((markedPotential d).erase s(xi,yi)) q
      (fun σ r => localScore d (s(xi,yi)::σ) (fixed ∪ r)) := by
  have hyi : yi ∈ d.marked := by rw [hmarks]; simp
  have hriP := marked_edge_mem d xi yi hyi hri
  have hnotB := potential_not_base d hd s(xi,yi) hri
  have hnotF : s(xi,yi) ∉ fixed := fun h => Finset.disjoint_left.mp hdis h hriP
  rw [unretained_head_mean d fixed s(xi,yi) hnotB hnotF q]
  have hh := lemma_4_5 (erasePotential d s(xi,yi)) (erasePotential_valid d hd _) 0 (1/4) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    fixed (erasePotential_fixed_subset d fixed _ hfixed hnotF) (erasePotential_fixed_disjoint d fixed _ hdis)
    q hq hq1 yi yj hym hmarks honly
  rw [mu_erasePotential d s(xi,yi) hnotB yi,mu_erasePotential d s(xi,yi) hnotB yj] at hh
  exact hh

lemma reference_head_weak_lower {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) : 3+5*q+mu d yi ≤ headValue d fixed q s(xi,yi) := by
  have hyi : yi ∈ d.marked := by rw [hmarks]; simp
  have hh := headValue_coin_lower d fixed q (by linarith) hq1 s(xi,yi) (marked_edge_mem d xi yi hyi hri)
    (8+mu d yi) (3+mu d yi)
    (reference_retained_lower d hd xi xj yi yj hpair hij hmarks hym hri hrj fixed hfixed hdis q hq hq1)
    (reference_unretained_weak d hd xi xj yi yj hpair hij hmarks hym hri hrj fixed hfixed hdis q hq hq1)
  nlinarith

lemma reference_head_strong_lower {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (honly : ∀ x ∈ ({d.x1,d.x2} : Finset (Fin n)), ∀ y ∈ ({yi,yj} : Finset (Fin n)),
      s(x,y) ∈ (erasePotential d s(xi,yi)).potential ↔ y=yj)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    4+4*q+mu d yi-(1-q)*mu d yj ≤ headValue d fixed q s(xi,yi) := by
  have hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hyi : yi ∈ d.marked := by rw [hmarks]; simp
  have hh := headValue_coin_lower d fixed q (by linarith) hq1 s(xi,yi) (marked_edge_mem d xi yi hyi hri)
    (8+mu d yi) (4+mu d yi-mu d yj)
    (reference_retained_lower d hd xi xj yi yj hpair hij hmarks hym hri hrj fixed hfixed hdis q hq hq1)
    (reference_unretained_strong d hd xi yi yj hxi hmarks hym hri honly fixed hfixed hdis q hq hq1)
  nlinarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma erasePotential_card_lt {n : ℕ} (d : Local n) (hd : d.Valid) (e : Edge n) (he : e ∈ d.potential) :
    ((erasePotential d e).base ∪ (erasePotential d e).potential).card < (d.base ∪ d.potential).card := by
  rw [erasePotential_union d e (potential_not_base d hd e he)]
  exact Finset.card_erase_lt_of_mem (Finset.mem_union_right _ he)

lemma erasePotential_partners_unmarked {n : ℕ} (d : Local n) (hp : d.Partners) (e : Edge n)
    (he : e ∉ markedPotential d) : (erasePotential d e).Partners := by
  obtain ⟨f,hfi,hf⟩ := hp
  refine ⟨f,hfi,?_⟩
  intro y
  have hh := hf y
  refine ⟨hh.1,Finset.mem_erase.mpr ⟨?_,hh.2⟩⟩
  intro heq
  apply he
  rw [←heq]
  exact Finset.mem_filter.mpr ⟨hh.2,y.val,y.property,by simp⟩

lemma unused_head_mean {n : ℕ} (d : Local n) (fixed : EdgeSet n) (e : Edge n)
    (heB : e ∉ d.base) (heF : e ∉ fixed) (heP : e ∉ markedPotential d) (q : ℝ) :
    headValue d fixed q e = markedMean (erasePotential d e) q fixed (localScore (erasePotential d e)) := by
  unfold headValue
  have hh := unretained_head_mean d fixed e heB heF q
  simpa only [Finset.erase_eq_of_notMem heP] using hh

lemma unretained_head_bound {n : ℕ} (d : Local n) (hd : d.Valid) (fixed : EdgeSet n) (hdis : Disjoint fixed (markedPotential d))
    (e : Edge n) (he : e ∈ markedPotential d) (q : ℝ) (C : ℝ)
    (hb : C ≤ markedMean (erasePotential d e) q fixed (localScore (erasePotential d e))) :
    C ≤ orderCoinMean ((d.base ∪ d.potential).erase e) ((markedPotential d).erase e) q
      (fun σ r => localScore d (e::σ) (fixed ∪ r)) := by
  rw [unretained_head_mean d fixed e (potential_not_base d hd e (Finset.mem_filter.mp he).1)
    (fun hf => Finset.disjoint_left.mp hdis hf he) q]
  exact hb

lemma head_coin_six {n : ℕ} (d : Local n) (fixed : EdgeSet n) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (e : Edge n) (he : e ∈ markedPotential d)
    (hret : 8 ≤ orderCoinMean ((d.base ∪ d.potential).erase e) ((markedPotential d).erase e) q
      (fun σ r => localScore d (e::σ) (fixed ∪ insert e r)))
    (hun : 6 ≤ orderCoinMean ((d.base ∪ d.potential).erase e) ((markedPotential d).erase e) q
      (fun σ r => localScore d (e::σ) (fixed ∪ r))) : 6 ≤ headValue d fixed q e := by
  have hh := headValue_coin_lower d fixed q hq hq1 e he 8 6 hret hun
  nlinarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma reference_head_of_unretained {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1)
    (hun : 6 ≤ orderCoinMean ((d.base ∪ d.potential).erase s(xi,yi)) ((markedPotential d).erase s(xi,yi)) q
      (fun σ r => localScore d (s(xi,yi)::σ) (fixed ∪ r))) : 6 ≤ headValue d fixed q s(xi,yi) := by
  have hyi : yi ∈ d.marked := by rw [hmarks]; simp
  apply head_coin_six d fixed q (by linarith) hq1 s(xi,yi) (marked_edge_mem d xi yi hyi hri) ?_ hun
  have hh := reference_retained_lower d hd xi xj yi yj hpair hij hmarks hym hri hrj fixed hfixed hdis q hq hq1
  exact (by linarith [mu_nonneg d yi] : 8 ≤ 8+mu d yi).trans hh

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma pair_edges_distinct {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj) :
    s(xi,yi) ≠ s(xj,yj) ∧ s(xi,yi) ≠ s(xi,yj) ∧ s(xi,yi) ≠ s(xj,yi) ∧
    s(xj,yj) ≠ s(xi,yj) ∧ s(xj,yj) ≠ s(xj,yi) ∧ s(xi,yj) ≠ s(xj,yi) := by
  have hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hxj : xj ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hyi : yi ∈ d.Y := hd.2.2.2.2.1 (by rw [hmarks]; simp)
  have hyj : yj ∈ d.Y := hd.2.2.2.2.1 (by rw [hmarks]; simp)
  exact ⟨fun h => hij ((endpoint_edge_eq_iff d hd xi xj yi yj hxi hxj hyi hyj).mp h).1,
    fun h => hym ((endpoint_edge_eq_iff d hd xi xi yi yj hxi hxi hyi hyj).mp h).2,
    fun h => hij ((endpoint_edge_eq_iff d hd xi xj yi yi hxi hxj hyi hyi).mp h).1,
    fun h => hij.symm ((endpoint_edge_eq_iff d hd xj xi yj yj hxj hxi hyj hyj).mp h).1,
    fun h => hym.symm ((endpoint_edge_eq_iff d hd xj xj yj yi hxj hxj hyj hyi).mp h).2,
    fun h => hij ((endpoint_edge_eq_iff d hd xi xj yj yi hxi hxj hyj hyi).mp h).1⟩

lemma one_cross_only {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hrj : s(xj,yj) ∈ d.potential) (hc1 : s(xi,yj) ∈ d.potential) (hc2 : s(xj,yi) ∉ d.potential) :
    ∀ x ∈ ({d.x1,d.x2} : Finset (Fin n)), ∀ y ∈ ({yi,yj} : Finset (Fin n)),
      s(x,y) ∈ (erasePotential d s(xi,yi)).potential ↔ y=yj := by
  have hn := pair_edges_distinct d hd xi xj yi yj hpair hij hmarks hym
  intro x hx y hy
  rw [hpair] at hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      simp [erasePotential,hym]
    · have hy' : y=yj := Finset.mem_singleton.mp hy
      subst y
      simp [erasePotential,hc1,hn.2.1.symm]
  · have hx' : x=xj := Finset.mem_singleton.mp hx
    subst x
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      simp [erasePotential,hc2,hym]
    · have hy' : y=yj := Finset.mem_singleton.mp hy
      subst y
      simp [erasePotential,hrj,hn.1.symm]

lemma one_cross_marked_edges {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hmarks : d.marked = {yi,yj})
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (hc1 : s(xi,yj) ∈ d.potential) (hc2 : s(xj,yi) ∉ d.potential) :
    markedPotential d = {s(xi,yi),s(xj,yj),s(xi,yj)} := by
  have hyi : yi ∈ d.marked := by rw [hmarks]; simp
  have hyj : yj ∈ d.marked := by rw [hmarks]; simp
  ext e
  constructor
  · intro he
    rcases markedPotential_four d hd xi xj yi yj hpair hmarks e he with heq | heq | heq | heq
    · simp [heq]
    · simp [heq]
    · simp [heq]
    · exact (hc2 (heq ▸ (Finset.mem_filter.mp he).1)).elim
  · intro he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact marked_edge_mem d xi yi hyi hri
    · exact marked_edge_mem d xj yj hyj hrj
    · exact marked_edge_mem d xi yj hyj hc1

lemma erase_pair_partners {n : ℕ} (d : Local n) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (e : Edge n) (hnei : s(xi,yi) ≠ e) (hnej : s(xj,yj) ≠ e) : (erasePotential d e).Partners := by
  exact partners_pair (erasePotential d e) xi xj yi yj hpair hij hmarks hym
    (Finset.mem_erase.mpr ⟨hnei,hri⟩) (Finset.mem_erase.mpr ⟨hnej,hrj⟩)

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma no_cross_case {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (hc1 : s(xi,yj) ∉ d.potential) (hc2 : s(xj,yi) ∉ d.potential)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1)
    (hout : ∀ e ∈ d.base ∪ d.potential, e ∉ markedPotential d → 6 ≤ headValue d fixed q e) :
    6 ≤ markedMean d q fixed (localScore d) := by
  apply markedMean_of_heads d fixed q 6 ⟨s(xi,yi),Finset.mem_union_right _ hri⟩
  intro e he
  by_cases heP : e ∈ markedPotential d
  · rcases markedPotential_four d hd xi xj yi yj hpair hmarks e heP with h | h | h | h
    · subst e
      have hh := reference_head_weak_lower d hd xi xj yi yj hpair hij hmarks hym hri hrj fixed hfixed hdis q hq hq1
      linarith [mu_nonneg d yi]
    · subst e
      have hh := reference_head_weak_lower d hd xj xi yj yi (by rw [hpair,Finset.pair_comm]) hij.symm
        (by rw [hmarks,Finset.pair_comm]) hym.symm hrj hri fixed hfixed hdis q hq hq1
      linarith [mu_nonneg d yj]
    · exact (hc1 (h ▸ (Finset.mem_filter.mp heP).1)).elim
    · exact (hc2 (h ▸ (Finset.mem_filter.mp heP).1)).elim
  · exact hout e he heP

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma potential_head_simple_lower {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj z yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hz : z ∈ d.Y) (hym : yi ≠ yj) (hmarks : d.marked = {yi,yj}) (hzm : z ∈ d.marked)
    (fixed Q : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hQ : Q ⊆ d.potential)
    (hhead : s(xi,z) ∈ fixed) (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    5+mu d yi+mu d yj ≤ orderCoinMean ((d.base ∪ d.potential).erase s(xi,z)) Q q
      (fun σ r => localScore d (s(xi,z)::σ) (fixed ∪ r)) := by
  have hxi : xi ∈ ({d.x1,d.x2} : Finset (Fin n)) := by rw [hpair]; simp
  have hyj : yj ∈ d.marked := by rw [hmarks]; simp
  have hheadB : s(xi,z) ∉ d.base := fun he => base_avoids_endpoint d hd xi hxi _ he (by simp)
  have hmono := orderCoinMean_mono ((d.base ∪ d.potential).erase s(xi,z)) Q q (by linarith) hq1
    (fun σ _ => 5+K d σ) (fun σ r => localScore d (s(xi,z)::σ) (fixed ∪ r)) (by
      intro r hr σ hσ
      have hret : fixed ∪ r ⊆ d.potential := Finset.union_subset hfixed (hr.trans hQ)
      have hhead' : s(xi,z) ∈ fixed ∪ r := Finset.mem_union_left _ hhead
      have hh := potential_head_score d hd xi xj z yj hpair hij hz hyj σ (fixed ∪ r) hret hhead'
      simp only [hzm,↓reduceIte] at hh
      linarith [count_nonneg {xj} (deletedRun d xj z σ (fixed ∪ r)),count_nonneg {yj} (deletedRun d xj z σ (fixed ∪ r))])
  rw [orderCoinMean_add_const,orderCoinMean_K_head d Q q s(xi,z) hheadB,orderMean_K_pair d yi yj hym hmarks] at hmono
  linarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma fixed_head_lower_left {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj z yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj) (hz : z ∈ d.Y)
    (hrj : s(xj,yj) ∈ d.potential) (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential)
    (hdis : Disjoint fixed (markedPotential d)) (hhead : s(xi,z) ∈ fixed)
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) : 6 ≤ headValue d fixed q s(xi,z) := by
  have hyj : yj ∈ d.marked := by rw [hmarks]; simp
  have hnotZ : z ∉ d.marked := by
    intro hzm
    exact Finset.disjoint_left.mp hdis hhead (marked_edge_mem d xi z hzm (hfixed hhead))
  have hzyj : z ≠ yj := fun h => hnotZ (h.symm ▸ hyj)
  have hrjP := marked_edge_mem d xj yj hyj hrj
  have hn : s(xj,yj) ∉ fixed := fun he => Finset.disjoint_left.mp hdis he hrjP
  have hh := potential_head_mean_lower d hd xi xj z yi yj hpair hij hz hym hmarks hzyj
    fixed (markedPotential d) hfixed (Finset.filter_subset _ _) hhead hrjP hn q hq hq1
  simp only [hnotZ,↓reduceIte,mul_zero,add_zero] at hh
  exact (by linarith [mu_nonneg d yi] : 6 ≤ 6+mu d yi).trans hh

lemma fixed_head_lower {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (e : Edge n) (he : e ∈ fixed) (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    6 ≤ headValue d fixed q e := by
  obtain ⟨x,hx,z,hz,rfl⟩ := hd.2.2.2.2.2.2 e (hfixed he)
  rw [hpair] at hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    exact fixed_head_lower_left d hd xi xj z yi yj hpair hij hmarks hym hz hrj fixed hfixed hdis he q hq hq1
  · have hx' : x=xj := Finset.mem_singleton.mp hx
    subst x
    exact fixed_head_lower_left d hd xj xi z yj yi (by rw [hpair,Finset.pair_comm]) hij.symm
      (by rw [hmarks,Finset.pair_comm]) hym.symm hz hri fixed hfixed hdis he q hq hq1

lemma retained_simple_lower {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj z yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj) (hzm : z ∈ d.marked)
    (hhead : s(xi,z) ∈ d.potential) (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential)
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    5+mu d yi+mu d yj ≤ orderCoinMean ((d.base ∪ d.potential).erase s(xi,z)) ((markedPotential d).erase s(xi,z)) q
      (fun σ r => localScore d (s(xi,z)::σ) (fixed ∪ insert s(xi,z) r)) := by
  have hh := potential_head_simple_lower d hd xi xj z yi yj hpair hij (hd.2.2.2.2.1 hzm) hym hmarks hzm
    (insert s(xi,z) fixed) ((markedPotential d).erase s(xi,z)) (Finset.insert_subset hhead hfixed)
    ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _)) (Finset.mem_insert_self _ _) q hq hq1
  have hfun : (fun σ r => localScore d (s(xi,z)::σ) (insert s(xi,z) fixed ∪ r)) =
      (fun σ r => localScore d (s(xi,z)::σ) (fixed ∪ insert s(xi,z) r)) := by
    funext σ r
    congr 1
    simp only [Finset.union_insert,Finset.insert_union]
  rw [hfun] at hh
  exact hh

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma cross_head_lower {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj) (hcross : s(xi,yj) ∈ d.potential)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential)
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1)
    (hun : 6 ≤ orderCoinMean ((d.base ∪ d.potential).erase s(xi,yj)) ((markedPotential d).erase s(xi,yj)) q
      (fun σ r => localScore d (s(xi,yj)::σ) (fixed ∪ r))) :
    6-q+q*(mu d yi+mu d yj) ≤ headValue d fixed q s(xi,yj) := by
  have hyj : yj ∈ d.marked := by rw [hmarks]; simp
  have hret := retained_simple_lower d hd xi xj yj yi yj hpair hij hmarks hym hyj hcross fixed hfixed q hq hq1
  have hh := headValue_coin_lower d fixed q (by linarith) hq1 s(xi,yj) (marked_edge_mem d xi yj hyj hcross)
    (5+mu d yi+mu d yj) 6 hret hun
  nlinarith

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma one_cross_case {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (hc1 : s(xi,yj) ∈ d.potential) (hc2 : s(xj,yi) ∉ d.potential)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1)
    (hout : ∀ e ∈ d.base ∪ d.potential, e ∉ markedPotential d → 6 ≤ headValue d fixed q e)
    (herase : ∀ e ∈ markedPotential d, (erasePotential d e).Partners →
      6 ≤ orderCoinMean ((d.base ∪ d.potential).erase e) ((markedPotential d).erase e) q
        (fun σ r => localScore d (e::σ) (fixed ∪ r))) :
    6 ≤ markedMean d q fixed (localScore d) := by
  have hn := pair_edges_distinct d hd xi xj yi yj hpair hij hmarks hym
  have hyj : yj ∈ d.marked := by rw [hmarks]; simp
  have hcrossP := marked_edge_mem d xi yj hyj hc1
  have hcrossPartners := erase_pair_partners d xi xj yi yj hpair hij hmarks hym hri hrj s(xi,yj) hn.2.1 hn.2.2.2.1
  have hun := herase s(xi,yj) hcrossP hcrossPartners
  have h1 := reference_head_strong_lower d hd xi xj yi yj hpair hij hmarks hym hri hrj
    (one_cross_only d hd xi xj yi yj hpair hij hmarks hym hrj hc1 hc2) fixed hfixed hdis q hq hq1
  have h2 := reference_head_weak_lower d hd xj xi yj yi (by rw [hpair,Finset.pair_comm]) hij.symm
    (by rw [hmarks,Finset.pair_comm]) hym.symm hrj hri fixed hfixed hdis q hq hq1
  have h3 := cross_head_lower d hd xi xj yi yj hpair hij hmarks hym hc1 fixed hfixed q hq hq1 hun
  apply markedMean_of_grouped_heads d fixed q 6 ⟨s(xi,yi),Finset.mem_union_right _ hri⟩ (markedPotential d)
    ((Finset.filter_subset _ _).trans Finset.subset_union_right) ?_ ?_
  · rw [one_cross_marked_edges d hd xi xj yi yj hpair hmarks hri hrj hc1 hc2]
    have hni : s(xi,yi) ∉ ({s(xj,yj),s(xi,yj)} : EdgeSet n) := by simp [hn.1,hn.2.1]
    have hnj : s(xj,yj) ∉ ({s(xi,yj)} : EdgeSet n) := by simp [hn.2.2.2.1]
    rw [Finset.card_insert_of_notMem hni,Finset.card_insert_of_notMem hnj,Finset.card_singleton,
      Finset.sum_insert hni,Finset.sum_insert hnj,Finset.sum_singleton]
    norm_num only [Nat.cast_add,Nat.cast_one]
    nlinarith [mu_nonneg d yi,mu_nonneg d yj,mul_nonneg (show (0:ℝ) ≤ q by linarith) (mu_nonneg d yi),
      mul_nonneg (show (0:ℝ) ≤ q by linarith) (mu_nonneg d yj)]
  · intro e he
    have hm := Finset.mem_sdiff.mp he
    exact hout e hm.1 hm.2

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma two_cross_case {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (hc1 : s(xi,yj) ∈ d.potential) (hc2 : s(xj,yi) ∈ d.potential)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1)
    (hout : ∀ e ∈ d.base ∪ d.potential, e ∉ markedPotential d → 6 ≤ headValue d fixed q e)
    (herase : ∀ e ∈ markedPotential d, (erasePotential d e).Partners →
      6 ≤ orderCoinMean ((d.base ∪ d.potential).erase e) ((markedPotential d).erase e) q
        (fun σ r => localScore d (e::σ) (fixed ∪ r))) :
    6 ≤ markedMean d q fixed (localScore d) := by
  have hn := pair_edges_distinct d hd xi xj yi yj hpair hij hmarks hym
  have hyi : yi ∈ d.marked := by rw [hmarks]; simp
  have hyj : yj ∈ d.marked := by rw [hmarks]; simp
  have hpair' : ({d.x1,d.x2} : Finset (Fin n)) = {xj,xi} := by rw [hpair,Finset.pair_comm]
  have hmarks' : d.marked = {yj,yi} := by rw [hmarks,Finset.pair_comm]
  apply markedMean_of_heads d fixed q 6 ⟨s(xi,yi),Finset.mem_union_right _ hri⟩
  intro e he
  by_cases heP : e ∈ markedPotential d
  · rcases markedPotential_four d hd xi xj yi yj hpair hmarks e heP with heq | heq | heq | heq
    · subst e
      have hp := erase_pair_partners d xi xj yj yi hpair hij hmarks' hym.symm hc1 hc2 s(xi,yi) hn.2.1.symm hn.2.2.1.symm
      exact reference_head_of_unretained d hd xi xj yi yj hpair hij hmarks hym hri hrj fixed hfixed hdis q hq hq1 (herase _ heP hp)
    · subst e
      have hp := erase_pair_partners d xi xj yj yi hpair hij hmarks' hym.symm hc1 hc2 s(xj,yj) hn.2.2.2.1.symm hn.2.2.2.2.1.symm
      exact reference_head_of_unretained d hd xj xi yj yi hpair' hij.symm hmarks' hym.symm hrj hri fixed hfixed hdis q hq hq1 (herase _ heP hp)
    · subst e
      have hp := erase_pair_partners d xi xj yi yj hpair hij hmarks hym hri hrj s(xi,yj) hn.2.1 hn.2.2.2.1
      exact reference_head_of_unretained d hd xi xj yj yi hpair hij hmarks' hym.symm hc1 hc2 fixed hfixed hdis q hq hq1 (herase _ heP hp)
    · subst e
      have hp := erase_pair_partners d xi xj yi yj hpair hij hmarks hym hri hrj s(xj,yi) hn.2.2.1 hn.2.2.2.2.1
      exact reference_head_of_unretained d hd xj xi yi yj hpair' hij.symm hmarks hym hc2 hc1 fixed hfixed hdis q hq hq1 (herase _ heP hp)
  · exact hout e he heP

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma two_reference_cases {n : ℕ} (d : Local n) (hd : d.Valid) (xi xj yi yj : Fin n)
    (hpair : ({d.x1,d.x2} : Finset (Fin n)) = {xi,xj}) (hij : xi ≠ xj)
    (hmarks : d.marked = {yi,yj}) (hym : yi ≠ yj)
    (hri : s(xi,yi) ∈ d.potential) (hrj : s(xj,yj) ∈ d.potential)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1)
    (hout : ∀ e ∈ d.base ∪ d.potential, e ∉ markedPotential d → 6 ≤ headValue d fixed q e)
    (herase : ∀ e ∈ markedPotential d, (erasePotential d e).Partners →
      6 ≤ orderCoinMean ((d.base ∪ d.potential).erase e) ((markedPotential d).erase e) q
        (fun σ r => localScore d (e::σ) (fixed ∪ r))) :
    6 ≤ markedMean d q fixed (localScore d) := by
  by_cases hc1 : s(xi,yj) ∈ d.potential
  · by_cases hc2 : s(xj,yi) ∈ d.potential
    · exact two_cross_case d hd xi xj yi yj hpair hij hmarks hym hri hrj hc1 hc2 fixed hfixed hdis q hq hq1 hout herase
    · exact one_cross_case d hd xi xj yi yj hpair hij hmarks hym hri hrj hc1 hc2 fixed hfixed hdis q hq hq1 hout herase
  · by_cases hc2 : s(xj,yi) ∈ d.potential
    · exact one_cross_case d hd xj xi yj yi (by rw [hpair,Finset.pair_comm]) hij.symm
        (by rw [hmarks,Finset.pair_comm]) hym.symm hrj hri hc2 hc1 fixed hfixed hdis q hq hq1 hout herase
    · exact no_cross_case d hd xi xj yi yj hpair hij hmarks hym hri hrj hc1 hc2 fixed hfixed hdis q hq hq1 hout

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma markedMean_const {n : ℕ} (d : Local n) (q : ℝ) (fixed : EdgeSet n) (C : ℝ) :
    markedMean d q fixed (fun _ _ => C) = C := by
  rw [markedMean_orderCoinMean,orderCoinMean_const]

lemma markedMean_small {n : ℕ} (d : Local n) (hd : d.Valid) (hp : d.Partners)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) (hc : d.marked.card ≤ 1) :
    3*(d.marked.card : ℝ) ≤ markedMean d q fixed (localScore d) := by
  by_cases he : d.marked = ∅
  · have hpoint : ∀ σ r, (0:ℝ) ≤ localScore d σ r := by
      intro σ r
      unfold localScore N R K
      linarith [count_nonneg {d.x1,d.x2} (localRun d σ r),count_nonneg d.marked (localRun d σ r),count_nonneg d.marked (baseRun d σ)]
    have hh := markedMean_mono d q (by linarith) hq1 fixed (fun _ _ => 0) (localScore d) hpoint
    rw [markedMean_const] at hh
    simpa only [he,Finset.card_empty,Nat.cast_zero,mul_zero] using hh
  · have hcard : d.marked.card=1 := by have hn := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he); omega
    obtain ⟨y,hmarks⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨f,hfi,hf⟩ := hp
    have hy : y ∈ d.marked := by rw [hmarks]; simp
    let x := f ⟨y,hy⟩
    have hx := hf (⟨y,hy⟩ : d.marked)
    have hh := markedMean_one_reference d hd fixed hfixed hdis q hq hq1 x y hx.1 hy hx.2
    have heq : localScore d = (fun σ r => 3*N d σ r+2*count {y} (localRun d σ r)+count {y} (baseRun d σ)) := by
      funext σ r
      simp only [localScore,R,K,hmarks]
    rw [heq]
    simpa only [hmarks,Finset.card_singleton,Nat.cast_one,mul_one] using hh

end
end FengLiYangMatching.General
open Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma trimBy_inter {n : ℕ} (W : Finset (Fin n)) (P r : EdgeSet n) (hr : r ⊆ P) :
    trimBy W r = r ∩ trimBy W P := by
  ext e
  simp only [trimBy,Finset.mem_filter,Finset.mem_inter]
  exact ⟨fun h => ⟨h.1,hr h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩

lemma localScore_filter_order {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n) (hr : r ⊆ d.potential) :
    localScore d (σ.filter (fun e => e ∈ d.base ∪ d.potential)) r = localScore d σ r := by
  unfold localScore
  rw [local_score_filter,local_score_filter]
  have hsub : d.base ∪ r ⊆ d.base ∪ d.potential := Finset.union_subset_union (Finset.Subset.refl _) hr
  rw [filter_filter_subset _ _ hsub,filter_filter_subset _ _ Finset.subset_union_left]

lemma trimBy_edge_not_self {n : ℕ} (f : Edge n) (E : EdgeSet n) : f ∉ trimBy f.toFinset E := by
  intro hf
  have hnone := (Finset.mem_filter.mp hf).2
  induction f using Sym2.inductionOn with
  | hf x y => exact hnone x (by simp) (by simp)

lemma trimBy_edge_subset_erase {n : ℕ} (f : Edge n) (E : EdgeSet n) : trimBy f.toFinset E ⊆ E.erase f := by
  intro e he
  exact Finset.mem_erase.mpr ⟨(fun hef => trimBy_edge_not_self f E (hef ▸ he)),(Finset.mem_filter.mp he).1⟩

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma base_head_mean {n : ℕ} (d : Local n) (hd : d.Valid) (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential)
    (f : Edge n) (hf : f ∈ d.base) (q : ℝ) :
    orderCoinMean ((d.base ∪ d.potential).erase f) (markedPotential d) q
      (fun σ r => localScore d (f::σ) (fixed ∪ r)) =
      3*count d.marked {f}+markedMean (trimLocal d f.toFinset) q (trimBy f.toFinset fixed)
        (localScore (trimLocal d f.toFinset)) := by
  let W := f.toFinset
  let d' := trimLocal d W
  let E := d.base ∪ d.potential
  let E' := d'.base ∪ d'.potential
  let P := markedPotential d
  let P' := markedPotential d'
  let F' := trimBy W fixed
  have hEp : E' = trimBy W E := (trimBy_union W d.base d.potential).symm
  have hPp : P' = trimBy W P := trim_markedPotential d W
  have hEE : E' ⊆ E.erase f := by rw [hEp]; exact trimBy_edge_subset_erase f E
  have hPP : P' ⊆ P := by rw [hPp]; exact trimBy_subset W P
  have hfun : orderCoinMean (E.erase f) P q (fun σ r => localScore d (f::σ) (fixed ∪ r)) =
      orderCoinMean (E.erase f) P q (fun σ r => 3*count d.marked {f}+
        localScore d' (σ.filter (fun e => e ∈ E')) (F' ∪ (r ∩ P'))) := by
    apply orderCoinMean_congr
    intro r hr σ hσ
    rw [localScore_base_first d hd f hf σ (fixed ∪ r)]
    have heq : trimBy W (fixed ∪ r) = F' ∪ (r ∩ P') := by
      rw [trimBy_union,trimBy_inter W P r hr,←hPp]
    change 3*count d.marked {f}+localScore d' σ (trimBy W (fixed ∪ r)) = _
    rw [heq]
    apply congrArg (fun z => 3*count d.marked {f}+z)
    have hret : F' ∪ (r ∩ P') ⊆ d'.potential := by
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · have hh := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨hfixed hh.1,hh.2⟩
      · exact (Finset.filter_subset _ _) (Finset.mem_inter.mp he).2
    exact (localScore_filter_order d' σ _ hret).symm
  rw [hfun,orderCoinMean_add_const]
  apply congrArg (fun z => 3*count d.marked {f}+z)
  rw [markedMean_orderCoinMean]
  exact orderCoinMean_project (E.erase f) E' P P' hEE hPP q (fun σ r => localScore d' σ (F' ∪ r))

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma trimBy_edge_card_lt {n : ℕ} (f : Edge n) (E : EdgeSet n) (hf : f ∈ E) :
    (trimBy f.toFinset E).card < E.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨trimBy_subset _ _,?_⟩
  intro heq
  exact trimBy_edge_not_self f E (heq.symm ▸ hf)

lemma trim_fixed_subset {n : ℕ} (d : Local n) (W : Finset (Fin n)) (fixed : EdgeSet n)
    (hf : fixed ⊆ d.potential) : trimBy W fixed ⊆ (trimLocal d W).potential := by
  intro e he
  have hh := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hf hh.1,hh.2⟩

lemma trim_fixed_disjoint {n : ℕ} (d : Local n) (W : Finset (Fin n)) (fixed : EdgeSet n)
    (hd : Disjoint fixed (markedPotential d)) : Disjoint (trimBy W fixed) (markedPotential (trimLocal d W)) := by
  rw [trim_markedPotential,Finset.disjoint_left]
  intro e he hf
  exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1

lemma base_head_lower {n : ℕ} (d : Local n) (hd : d.Valid) (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential)
    (f : Edge n) (hf : f ∈ d.base) (q : ℝ)
    (hsmall : 3*((trimLocal d f.toFinset).marked.card : ℝ) ≤
      markedMean (trimLocal d f.toFinset) q (trimBy f.toFinset fixed) (localScore (trimLocal d f.toFinset))) :
    3*(d.marked.card : ℝ) ≤ orderCoinMean ((d.base ∪ d.potential).erase f) (markedPotential d) q
      (fun σ r => localScore d (f::σ) (fixed ∪ r)) := by
  rw [base_head_mean d hd fixed hfixed f hf q]
  linarith [trim_marked_card d f]

end
end FengLiYangMatching.General
open MeasureTheory Finset Classical
namespace FengLiYangMatching.General
noncomputable section

lemma marked_recovery_bound {n : ℕ} (d : Local n) (hd : d.Valid) (hp : d.Partners)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential) (hdis : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    3*(d.marked.card : ℝ) ≤ markedMean d q fixed (localScore d) := by
  suffices hAll : ∀ m : ℕ, ∀ d : Local n, (d.base ∪ d.potential).card=m → d.Valid → d.Partners →
      ∀ fixed : EdgeSet n, fixed ⊆ d.potential → Disjoint fixed (markedPotential d) →
        3*(d.marked.card : ℝ) ≤ markedMean d q fixed (localScore d) from hAll _ d rfl hd hp fixed hfixed hdis
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro d hcard hd hp fixed hfixed hdis
    by_cases hc : d.marked.card ≤ 1
    · exact markedMean_small d hd hp fixed hfixed hdis q hq hq1 hc
    · have hc2 : d.marked.card=2 := by have hh := hd.2.2.2.2.2.1; omega
      have hcR : 3*(d.marked.card : ℝ)=6 := by rw [hc2]; norm_num
      obtain ⟨xi,xj,yi,yj,hpair,hij,hmarks,hym,hri,hrj⟩ := partners_labelling d hd hp hc2
      rw [hcR]
      apply two_reference_cases d hd xi xj yi yj hpair hij hmarks hym hri hrj fixed hfixed hdis q hq hq1
      · intro e he heP
        by_cases heB : e ∈ d.base
        · let d' := trimLocal d e.toFinset
          have hx1 : d.x1 ∉ e.toFinset := by simpa only [Sym2.mem_toFinset] using (hd.2.1 e heB).2.1
          have hx2 : d.x2 ∉ e.toFinset := by simpa only [Sym2.mem_toFinset] using (hd.2.1 e heB).2.2
          have hlt : (d'.base ∪ d'.potential).card < m := by
            rw [←hcard]
            change (trimBy e.toFinset d.base ∪ trimBy e.toFinset d.potential).card < _
            rw [←trimBy_union]
            exact trimBy_edge_card_lt e (d.base ∪ d.potential) he
          have hb := ih _ hlt d' rfl (trimLocal_valid d hd e.toFinset hx1 hx2)
            (trimLocal_partners d hp e.toFinset hx1 hx2) (trimBy e.toFinset fixed)
            (trim_fixed_subset d e.toFinset fixed hfixed) (trim_fixed_disjoint d e.toFinset fixed hdis)
          have hh := base_head_lower d hd fixed hfixed e heB q hb
          rw [hcR] at hh
          exact hh
        · have heD : e ∈ d.potential := (Finset.mem_union.mp he).resolve_left heB
          by_cases heF : e ∈ fixed
          · exact fixed_head_lower d hd xi xj yi yj hpair hij hmarks hym hri hrj fixed hfixed hdis e heF q hq hq1
          · let d' := erasePotential d e
            have hlt : (d'.base ∪ d'.potential).card < m := by rw [←hcard]; exact erasePotential_card_lt d hd e heD
            have hb := ih _ hlt d' rfl (erasePotential_valid d hd e) (erasePotential_partners_unmarked d hp e heP)
              fixed (erasePotential_fixed_subset d fixed e hfixed heF) (erasePotential_fixed_disjoint d fixed e hdis)
            change 3*(d.marked.card : ℝ) ≤ markedMean d' q fixed (localScore d') at hb
            rw [hcR] at hb
            rw [unused_head_mean d fixed e heB heF heP q]
            exact hb
      · intro e he hp'
        have heD : e ∈ d.potential := (Finset.mem_filter.mp he).1
        have heF : e ∉ fixed := fun h => Finset.disjoint_left.mp hdis h he
        let d' := erasePotential d e
        have hlt : (d'.base ∪ d'.potential).card < m := by rw [←hcard]; exact erasePotential_card_lt d hd e heD
        have hb := ih _ hlt d' rfl (erasePotential_valid d hd e) hp' fixed
          (erasePotential_fixed_subset d fixed e hfixed heF) (erasePotential_fixed_disjoint d fixed e hdis)
        change 3*(d.marked.card : ℝ) ≤ markedMean d' q fixed (localScore d') at hb
        rw [hcR] at hb
        exact unretained_head_bound d hd fixed hdis e he q 6 hb

lemma local_recovery_bound_proof {n : ℕ} (d : Local n) (hd : d.Valid) (hp : d.Partners)
    (q : ℝ) (hq : (5/8:ℝ) ≤ q) (hq1 : q ≤ 1) :
    localMean d q (fun σ r => 3*N d σ r+2*R d σ r+K d σ) ≥ 3*d.marked.card := by
  apply localMean_from_marked_bound d q (by linarith) hq1 (localScore d) (3*d.marked.card)
  intro fixed hf
  have hfixed : fixed ⊆ d.potential := hf.trans Finset.sdiff_subset
  have hdis : Disjoint fixed (markedPotential d) := by
    rw [Finset.disjoint_left]
    intro e he hp
    exact (Finset.mem_sdiff.mp (hf he)).2 hp
  exact marked_recovery_bound d hd hp fixed hfixed hdis q hq hq1

end
end FengLiYangMatching.General
open MeasureTheory Finset
open FengLiYangMatching.General
theorem solution {n : ℕ} (d : Local n) (hd : d.Valid) (hpartners : d.Partners)
    (q : ℝ) (hq : 5/8 ≤ q) (hq1 : q ≤ 1) :
    localMean d q (fun σ r => 3*N d σ r+2*R d σ r+K d σ) ≥ 3*d.marked.card := by
  exact FengLiYangMatching.General.local_recovery_bound_proof d hd hpartners q hq hq1
