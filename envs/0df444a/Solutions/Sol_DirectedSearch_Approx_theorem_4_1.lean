-- Prove2me | solution 1 for DirectedSearch.Approx.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:57:01.491991+00:00
-- url     : https://prove2.me/submissions/914d001d-5bb7-4eff-8963-b6964831e0f8

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting
import Definitions.Def_DirectedSearch_Approx_Graphs
import Theorems.Thm_DirectedSearch_Approx_proposition_4_4
import Theorems.Thm_DirectedSearch_Approx_lemma_4_6
import Theorems.Thm_DirectedSearch_Approx_lemma_4_7
import Theorems.Thm_DirectedSearch_Approx_proposition_4_8

set_option linter.unusedSectionVars false

namespace DSA41

open DirectedSearch.Approx

section glue

variable {M W ι : Type} [Fintype M] [Fintype W] [Fintype ι] [DecidableEq ι]
  (cM : M → ι) (cW : W → ι)

/-- The sub-market on the types of block `i`. -/
def subMarket (mk : Market M W) (i : ι) : Market {m // cM m = i} {w // cW w = i} :=
  ⟨mk.δ, fun m => mk.αM m.1, fun w => mk.αW w.1, fun m w => mk.F m.1 w.1⟩

/-- The empty-assortment profile. -/
noncomputable def trivProfile {M' W' : Type} (mk : Market M' W') : Profile M' W' :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun m => mk.αM m / mk.δ, fun w => mk.αW w / mk.δ⟩

lemma trivProfile_feasible {M' W' : Type} [Fintype M'] [Fintype W'] (mk : Market M' W')
    (hδ : 0 < mk.δ) : SecondBestFeasible mk (trivProfile mk) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp [trivProfile] <;> field_simp

lemma trivProfile_welfare {M' W' : Type} [Fintype M'] [Fintype W'] (mk : Market M' W') :
    sbWelfare mk (trivProfile mk) = 0 := by
  simp [sbWelfare, trivProfile]

variable {cM cW}

/-- Gluing block profiles into a global profile. -/
noncomputable def glue (P : ∀ i, Profile {m // cM m = i} {w // cW w = i}) : Profile M W where
  lamM m w := if h : cW w = cM m then (P (cM m)).lamM ⟨m, rfl⟩ ⟨w, h⟩ else 0
  lamW w m := if h : cM m = cW w then (P (cW w)).lamW ⟨w, rfl⟩ ⟨m, h⟩ else 0
  tauM m := (P (cM m)).tauM ⟨m, rfl⟩
  tauW w := (P (cW w)).tauW ⟨w, rfl⟩
  xiM m := (P (cM m)).xiM ⟨m, rfl⟩
  xiW w := (P (cW w)).xiW ⟨w, rfl⟩
  etaM m := (P (cM m)).etaM ⟨m, rfl⟩
  etaW w := (P (cW w)).etaW ⟨w, rfl⟩

variable (P : ∀ i, Profile {m // cM m = i} {w // cW w = i})

lemma glue_tauM (i : ι) (m : {m // cM m = i}) : (glue P).tauM m.1 = (P i).tauM m := by
  rcases m with ⟨m, rfl⟩; rfl
lemma glue_tauW (i : ι) (w : {w // cW w = i}) : (glue P).tauW w.1 = (P i).tauW w := by
  rcases w with ⟨w, rfl⟩; rfl
lemma glue_xiM (i : ι) (m : {m // cM m = i}) : (glue P).xiM m.1 = (P i).xiM m := by
  rcases m with ⟨m, rfl⟩; rfl
lemma glue_xiW (i : ι) (w : {w // cW w = i}) : (glue P).xiW w.1 = (P i).xiW w := by
  rcases w with ⟨w, rfl⟩; rfl
lemma glue_etaM (i : ι) (m : {m // cM m = i}) : (glue P).etaM m.1 = (P i).etaM m := by
  rcases m with ⟨m, rfl⟩; rfl
lemma glue_etaW (i : ι) (w : {w // cW w = i}) : (glue P).etaW w.1 = (P i).etaW w := by
  rcases w with ⟨w, rfl⟩; rfl
lemma glue_lamM (i : ι) (m : {m // cM m = i}) (w : {w // cW w = i}) :
    (glue P).lamM m.1 w.1 = (P i).lamM m w := by
  rcases m with ⟨m, rfl⟩; rcases w with ⟨w, hw⟩
  simp [glue, hw]
lemma glue_lamW (i : ι) (w : {w // cW w = i}) (m : {m // cM m = i}) :
    (glue P).lamW w.1 m.1 = (P i).lamW w m := by
  rcases w with ⟨w, rfl⟩; rcases m with ⟨m, hm⟩
  simp [glue, hm]
lemma glue_lamM_zero (m : M) (w : W) (h : cW w ≠ cM m) : (glue P).lamM m w = 0 := by
  simp [glue, h]
lemma glue_lamW_zero (w : W) (m : M) (h : cM m ≠ cW w) : (glue P).lamW w m = 0 := by
  simp [glue, h]
lemma glue_thr (i : ι) (m : {m // cM m = i}) (w : {w // cW w = i}) :
    thr (glue P) m.1 w.1 = thr (P i) m w := by
  simp only [thr, glue_tauM, glue_tauW]

omit [Fintype ι] in
lemma sum_block {α : Type} [Fintype α] (c : α → ι) (i : ι) (f : α → ℝ)
    (hf : ∀ a, c a ≠ i → f a = 0) : ∑ a, f a = ∑ a : {a // c a = i}, f a.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => c a = i) f]
  have : ∑ a : {a // ¬ c a = i}, f a.1 = 0 :=
    Finset.sum_eq_zero (fun a _ => hf a.1 a.2)
  rw [this, add_zero]

omit [Fintype ι] in
lemma sum_block_le {α : Type} [Fintype α] (c : α → ι) (i : ι) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) : ∑ a : {a // c a = i}, f a.1 ≤ ∑ a, f a := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => c a = i) f]
  have : 0 ≤ ∑ a : {a // ¬ c a = i}, f a.1 := Finset.sum_nonneg (fun a _ => hf a.1)
  linarith

theorem glue_feasible (mk : Market M W)
    (hP : ∀ i, SecondBestFeasible (subMarket cM cW mk i) (P i)) :
    SecondBestFeasible mk (glue P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m; exact (hP (cM m)).1 ⟨m, rfl⟩
  · intro w; exact (hP (cW w)).2.1 ⟨w, rfl⟩
  · intro m w
    by_cases h : cW w = cM m
    · have e1 : (glue P).etaM m = _ := glue_etaM P (cM m) ⟨m, rfl⟩
      have e2 : (glue P).etaW w = _ := glue_etaW P (cM m) ⟨w, h⟩
      have e3 : (glue P).lamM m w = _ := glue_lamM P (cM m) ⟨m, rfl⟩ ⟨w, h⟩
      have e4 : (glue P).lamW w m = _ := glue_lamW P (cM m) ⟨w, h⟩ ⟨m, rfl⟩
      rw [e1, e2, e3, e4]
      exact (hP (cM m)).2.2.1 ⟨m, rfl⟩ ⟨w, h⟩
    · rw [glue_lamM_zero P m w h, glue_lamW_zero P w m (Ne.symm h)]; simp
  · intro m
    rw [sum_block cW (cM m) _ (fun w hw => glue_lamM_zero P m w hw)]
    have := (hP (cM m)).2.2.2.1 ⟨m, rfl⟩
    refine le_trans (le_of_eq ?_) this
    exact Finset.sum_congr rfl (fun w _ => glue_lamM P (cM m) ⟨m, rfl⟩ w)
  · intro w
    rw [sum_block cM (cW w) _ (fun m hm => glue_lamW_zero P w m hm)]
    have := (hP (cW w)).2.2.2.2.1 ⟨w, rfl⟩
    refine le_trans (le_of_eq ?_) this
    exact Finset.sum_congr rfl (fun m _ => glue_lamW P (cW w) ⟨w, rfl⟩ m)
  · intro m
    rw [sum_block cW (cM m) _ (fun w hw => by rw [glue_lamM_zero P m w hw, zero_mul])]
    have e1 : (glue P).xiM m = _ := glue_xiM P (cM m) ⟨m, rfl⟩
    rw [e1, (hP (cM m)).2.2.2.2.2.1 ⟨m, rfl⟩]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have e3 : (glue P).lamM m w.1 = _ := glue_lamM P (cM m) ⟨m, rfl⟩ w
    have e4 : thr (glue P) m w.1 = _ := glue_thr P (cM m) ⟨m, rfl⟩ w
    rw [e3, e4]; rfl
  · intro w
    rw [sum_block cM (cW w) _ (fun m hm => by rw [glue_lamW_zero P w m hm, zero_mul])]
    have e1 : (glue P).xiW w = _ := glue_xiW P (cW w) ⟨w, rfl⟩
    rw [e1, (hP (cW w)).2.2.2.2.2.2.1 ⟨w, rfl⟩]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have e3 : (glue P).lamW w m.1 = _ := glue_lamW P (cW w) ⟨w, rfl⟩ m
    have e4 : thr (glue P) m.1 w = _ := glue_thr P (cW w) m ⟨w, rfl⟩
    rw [e3, e4]; rfl
  · intro m
    rw [sum_block cW (cM m) _ (fun w hw => by rw [glue_lamM_zero P m w hw, zero_mul])]
    have e1 : (glue P).xiM m = _ := glue_xiM P (cM m) ⟨m, rfl⟩
    have e0 : (glue P).tauM m = _ := glue_tauM P (cM m) ⟨m, rfl⟩
    rw [e1, e0, (hP (cM m)).2.2.2.2.2.2.2.1 ⟨m, rfl⟩]
    congr 1
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have e3 : (glue P).lamM m w.1 = _ := glue_lamM P (cM m) ⟨m, rfl⟩ w
    have e4 : thr (glue P) m w.1 = _ := glue_thr P (cM m) ⟨m, rfl⟩ w
    rw [e3, e4]; rfl
  · intro w
    rw [sum_block cM (cW w) _ (fun m hm => by rw [glue_lamW_zero P w m hm, zero_mul])]
    have e1 : (glue P).xiW w = _ := glue_xiW P (cW w) ⟨w, rfl⟩
    have e0 : (glue P).tauW w = _ := glue_tauW P (cW w) ⟨w, rfl⟩
    rw [e1, e0, (hP (cW w)).2.2.2.2.2.2.2.2.1 ⟨w, rfl⟩]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have e3 : (glue P).lamW w m.1 = _ := glue_lamW P (cW w) ⟨w, rfl⟩ m
    have e4 : thr (glue P) m.1 w = _ := glue_thr P (cW w) m ⟨w, rfl⟩
    rw [e3, e4]; rfl
  · intro m w
    by_cases h : cW w = cM m
    · have e3 : (glue P).lamM m w = _ := glue_lamM P (cM m) ⟨m, rfl⟩ ⟨w, h⟩
      rw [e3]; exact (hP (cM m)).2.2.2.2.2.2.2.2.2.1 _ _
    · rw [glue_lamM_zero P m w h]
  · intro w m
    by_cases h : cM m = cW w
    · have e3 : (glue P).lamW w m = _ := glue_lamW P (cW w) ⟨w, rfl⟩ ⟨m, h⟩
      rw [e3]; exact (hP (cW w)).2.2.2.2.2.2.2.2.2.2 _ _
    · rw [glue_lamW_zero P w m h]

theorem glue_welfare (mk : Market M W) :
    sbWelfare mk (glue P) = ∑ i, sbWelfare (subMarket cM cW mk i) (P i) := by
  unfold sbWelfare
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Fintype.sum_fiberwise cM]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [sum_block cW i _ (fun w hw => by
      rw [glue_lamM_zero P m.1 w (by rw [m.2]; exact hw), mul_zero, zero_mul])]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [glue_etaM P i m, glue_lamM P i m w, glue_thr P i m w]; rfl
  · rw [← Fintype.sum_fiberwise cW]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun w _ => ?_))
    rw [sum_block cM i _ (fun m hm => by
      rw [glue_lamW_zero P w.1 m (by rw [w.2]; exact hm), mul_zero, zero_mul])]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [glue_etaW P i w, glue_lamW P i w m, glue_thr P i m w]; rfl

end glue

section graph

variable {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

/-- Pair weights `ρ_mw β_mw` on cross pairs, `0` otherwise. -/
def pairWt (ρ β : M → W → ℝ) : M ⊕ W → M ⊕ W → ℝ
  | Sum.inl m, Sum.inr w => ρ m w * β m w
  | Sum.inr w, Sum.inl m => ρ m w * β m w
  | _, _ => 0

/-- Edge weights on `Sym2 (M ⊕ W)`. -/
def wtFun (ρ β : M → W → ℝ) : Sym2 (M ⊕ W) → ℝ :=
  Sym2.lift ⟨pairWt ρ β, by intro a b; cases a <;> cases b <;> rfl⟩

lemma supportGraph_adj (β : M → W → ℝ) (x y : M ⊕ W) :
    (supportGraph β).Adj x y ↔ x ≠ y ∧
      ((∃ m w, x = Sum.inl m ∧ y = Sum.inr w ∧ 0 < β m w) ∨
        (∃ m w, y = Sum.inl m ∧ x = Sum.inr w ∧ 0 < β m w)) := by
  unfold supportGraph; rw [SimpleGraph.fromRel_adj]

lemma supportGraph_adj_cross (β : M → W → ℝ) (m : M) (w : W) :
    (supportGraph β).Adj (Sum.inl m) (Sum.inr w) ↔ 0 < β m w := by
  rw [supportGraph_adj]; simp

lemma supportGraph_not_ll (β : M → W → ℝ) (m m' : M) :
    ¬ (supportGraph β).Adj (Sum.inl m) (Sum.inl m') := by
  rw [supportGraph_adj]; simp

lemma supportGraph_not_rr (β : M → W → ℝ) (w w' : W) :
    ¬ (supportGraph β).Adj (Sum.inr w) (Sum.inr w') := by
  rw [supportGraph_adj]; simp

open Classical in
lemma graphWeight_eq (ρ β : M → W → ℝ) (H : SimpleGraph (M ⊕ W)) (hH : H ≤ supportGraph β) :
    graphWeight H (wtFun ρ β) =
      ∑ m, ∑ w, if H.Adj (Sum.inl m) (Sum.inr w) then ρ m w * β m w else 0 := by
  unfold graphWeight
  have hE : H.edgeFinset =
      (Finset.univ.filter (fun p : M × W => H.Adj (Sum.inl p.1) (Sum.inr p.2))).image
        (fun p => s(Sum.inl p.1, Sum.inr p.2)) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
      constructor
      · intro hxy
        rcases x with m | w <;> rcases y with m' | w'
        · exact absurd (hH hxy) (supportGraph_not_ll β m m')
        · exact ⟨m, w', hxy, rfl⟩
        · exact ⟨m', w, hxy.symm, Sym2.eq_swap⟩
        · exact absurd (hH hxy) (supportGraph_not_rr β w w')
      · rintro ⟨m, w, h, he⟩
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h
        · exact h.symm
  rw [hE, Finset.sum_image]
  · rw [Finset.sum_filter, Fintype.sum_prod_type]
    rfl
  · intro p _ q _ hpq
    rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Prod.ext (Sum.inl_injective h1) (Sum.inr_injective h2)
    · exact absurd h1 Sum.inl_ne_inr

/-- Adjacency-uniqueness form of "degree one". -/
def Leaf (H : SimpleGraph (M ⊕ W)) (v : M ⊕ W) : Prop := ∃! u, H.Adj v u

open Classical in
/-- The block (star centre) of each vertex of a star forest. -/
noncomputable def center (H : SimpleGraph (M ⊕ W)) : M ⊕ W → M ⊕ W
  | Sum.inl m =>
    if h : ∃ w, H.Adj (Sum.inl m) (Sum.inr w) ∧ ¬ Leaf H (Sum.inr w) then Sum.inr h.choose
    else Sum.inl m
  | Sum.inr w =>
    if h : ∃ m, H.Adj (Sum.inl m) (Sum.inr w) ∧ Leaf H (Sum.inr w) then Sum.inl h.choose
    else Sum.inr w

lemma center_inl (H : SimpleGraph (M ⊕ W)) (m m' : M) (h : center H (Sum.inl m) = Sum.inl m') :
    m' = m := by
  simp only [center] at h
  split_ifs at h
  all_goals first | exact (Sum.inl_injective h).symm | simp at h

lemma center_inr (H : SimpleGraph (M ⊕ W)) (w w' : W) (h : center H (Sum.inr w) = Sum.inr w') :
    w' = w := by
  simp only [center] at h
  split_ifs at h
  all_goals first | exact (Sum.inr_injective h).symm | simp at h

lemma center_edge (H : SimpleGraph (M ⊕ W)) (hst : ∀ u v, H.Adj u v → Leaf H u ∨ Leaf H v)
    (m : M) (w : W) (hadj : H.Adj (Sum.inl m) (Sum.inr w)) :
    center H (Sum.inr w) = center H (Sum.inl m) := by
  by_cases hw : Leaf H (Sum.inr w)
  · have hex : ∃ m, H.Adj (Sum.inl m) (Sum.inr w) ∧ Leaf H (Sum.inr w) := ⟨m, hadj, hw⟩
    have hnex : ¬ ∃ w', H.Adj (Sum.inl m) (Sum.inr w') ∧ ¬ Leaf H (Sum.inr w') := by
      rintro ⟨w', hadj', hnl⟩
      rcases hst _ _ hadj' with hl | hl
      · obtain ⟨u, _, hu⟩ := hl
        have e1 := hu _ hadj
        have e2 := hu _ hadj'
        have : w = w' := Sum.inr_injective (e1.trans e2.symm)
        subst this; exact hnl hw
      · exact hnl hl
    have lhs : center H (Sum.inr w) = Sum.inl hex.choose := by
      simp only [center]; rw [dif_pos hex]
    have rhs : center H (Sum.inl m) = Sum.inl m := by
      simp only [center]; rw [dif_neg hnex]
    rw [lhs, rhs]
    congr 1
    obtain ⟨u, _, hu⟩ := hw
    have e1 := hu _ hadj.symm
    have e2 := hu _ hex.choose_spec.1.symm
    exact Sum.inl_injective (e2.trans e1.symm)
  · have hex : ∃ w', H.Adj (Sum.inl m) (Sum.inr w') ∧ ¬ Leaf H (Sum.inr w') := ⟨w, hadj, hw⟩
    have hnex : ¬ ∃ m', H.Adj (Sum.inl m') (Sum.inr w) ∧ Leaf H (Sum.inr w) :=
      fun ⟨_, _, h⟩ => hw h
    have lhs : center H (Sum.inr w) = Sum.inr w := by
      simp only [center]; rw [dif_neg hnex]
    have rhs : center H (Sum.inl m) = Sum.inr hex.choose := by
      simp only [center]; rw [dif_pos hex]
    rw [lhs, rhs]
    congr 1
    rcases hst _ _ hadj with hl | hl
    · obtain ⟨u, _, hu⟩ := hl
      have e1 := hu _ hadj
      have e2 := hu _ hex.choose_spec.1
      exact Sum.inr_injective (e1.trans e2.symm)
    · exact absurd hl hw

open Classical in
/-- `β` restricted to the edges of `H`. -/
noncomputable def restrictB (H : SimpleGraph (M ⊕ W)) (β : M → W → ℝ) (m : M) (w : W) : ℝ :=
  if H.Adj (Sum.inl m) (Sum.inr w) then β m w else 0

end graph

open Classical in
lemma isStarForest_leaf {V : Type} [Fintype V] (H : SimpleGraph V) (h : IsStarForest H) :
    ∀ u v, H.Adj u v → (∃! x, H.Adj u x) ∨ (∃! x, H.Adj v x) := by
  intro u v huv
  rcases h u v huv with h1 | h1
  · left; exact SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp h1
  · right; exact SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp h1

end DSA41

open DirectedSearch.Approx DSA41 in
theorem solution {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) :
    ∃ P : Profile M W, SecondBestFeasible mk P ∧
      ∀ Q : FBProfile M W, FirstBestFeasible mk Q → fbWelfare mk Q ≤ 4 * sbWelfare mk P := by
  obtain ⟨βs, hβsF, hβsOpt, hacyc⟩ := lemma_4_6 (rho mk) mk.αM mk.αW
    (fun m => (hmk.alphaM_pos m).le) (fun w => (hmk.alphaW_pos w).le)
  obtain ⟨H, hHG, hHstar, hwt⟩ := lemma_4_7 (supportGraph βs) hacyc (wtFun (rho mk) βs)
  have hst : ∀ u v, H.Adj u v → Leaf H u ∨ Leaf H v := isStarForest_leaf H hHstar
  set cM : M → M ⊕ W := fun m => center H (Sum.inl m) with hcM
  set cW : W → M ⊕ W := fun w => center H (Sum.inr w) with hcW
  set βH := restrictB H βs with hβH
  have hβs0 : ∀ m w, 0 ≤ βs m w := hβsF.1
  have hβH0 : ∀ m w, 0 ≤ βH m w := by
    intro m w; simp only [hβH, restrictB]; split_ifs
    · exact hβs0 m w
    · exact le_refl _
  have hβHle : ∀ m w, βH m w ≤ βs m w := by
    intro m w; simp only [hβH, restrictB]; split_ifs
    · exact le_refl _
    · exact hβs0 m w
  have hβHblock : ∀ m w, βH m w ≠ 0 → cW w = cM m := by
    intro m w h
    simp only [hβH, restrictB] at h
    split_ifs at h with hadj
    · exact center_edge H hst m w hadj
    · exact absurd rfl h
  have hβHadj : ∀ m w, βH m w ≠ 0 → H.Adj (Sum.inl m) (Sum.inr w) := by
    intro m w h
    simp only [hβH, restrictB] at h
    split_ifs at h with hadj
    · exact hadj
    · exact absurd rfl h
  -- per-block equilibria
  have hsub : ∀ i, (subMarket cM cW mk i).Standing := fun i =>
    ⟨hmk.delta_pos, fun m => hmk.alphaM_pos m.1, fun w => hmk.alphaW_pos w.1,
      fun m w => hmk.prob m.1 w.1, fun m w => hmk.noAtoms m.1 w.1,
      fun m w => hmk.integrable m.1 w.1⟩
  have hblock : ∀ i, ∃ Pi, SecondBestFeasible (subMarket cM cW mk i) Pi ∧
      lpObj (subMarket cM cW mk i) (fun m w => βH m.1 w.1) ≤
        2 * sbWelfare (subMarket cM cW mk i) Pi := by
    intro i
    by_cases hcard : Fintype.card {m // cM m = i} = 1 ∨ Fintype.card {w // cW w = i} = 1
    · obtain ⟨Pi, hPi, hPiw⟩ := proposition_4_8 (subMarket cM cW mk i) (hsub i) hcard
      refine ⟨Pi, hPi, ?_⟩
      have hLP : LPFeasible (subMarket cM cW mk i) (fun m w => βH m.1 w.1) := by
        refine ⟨fun m w => hβH0 _ _, fun m => ?_, fun w => ?_⟩
        · calc ∑ w : {w // cW w = i}, βH m.1 w.1 ≤ ∑ w, βH m.1 w :=
                sum_block_le cW i (fun w => βH m.1 w) (fun w => hβH0 _ _)
            _ ≤ ∑ w, βs m.1 w := Finset.sum_le_sum (fun w _ => hβHle _ _)
            _ ≤ mk.αM m.1 := hβsF.2.1 m.1
        · calc ∑ m : {m // cM m = i}, βH m.1 w.1 ≤ ∑ m, βH m w.1 :=
                sum_block_le cM i (fun m => βH m w.1) (fun m => hβH0 _ _)
            _ ≤ ∑ m, βs m w.1 := Finset.sum_le_sum (fun m _ => hβHle _ _)
            _ ≤ mk.αW w.1 := hβsF.2.2 w.1
      obtain ⟨Qi, hQi, hQiw⟩ := (proposition_4_4 (subMarket cM cW mk i) (hsub i)).2 _ hLP
      rw [← hQiw]
      exact hPiw Qi hQi
    · refine ⟨trivProfile _, trivProfile_feasible _ hmk.delta_pos, ?_⟩
      rw [trivProfile_welfare]
      have hz : ∀ (m : {m // cM m = i}) (w : {w // cW w = i}), βH m.1 w.1 = 0 := by
        intro m w
        by_contra hne
        apply hcard
        have hadj := hβHadj _ _ hne
        clear hne hadj
        rcases i with m₀ | w₀
        · left
          rw [Fintype.card_eq_one_iff]
          refine ⟨m, fun m' => Subtype.ext ?_⟩
          have h1 := center_inl H m'.1 m₀ m'.2
          have h2 := center_inl H m.1 m₀ m.2
          rw [← h1, ← h2]
        · right
          rw [Fintype.card_eq_one_iff]
          refine ⟨w, fun w' => Subtype.ext ?_⟩
          have h1 := center_inr H w'.1 w₀ w'.2
          have h2 := center_inr H w.1 w₀ w.2
          rw [← h1, ← h2]
      simp [lpObj, hz]
  choose P hP hPw using hblock
  refine ⟨glue P, glue_feasible P mk hP, ?_⟩
  intro Q hQ
  obtain ⟨⟨v, hv1, hv2⟩, _⟩ := proposition_4_4 mk hmk
  have h1 : fbWelfare mk Q ≤ v := hv1.2 ⟨Q, hQ, rfl⟩
  obtain ⟨β0, hβ0, hβ0v⟩ := hv2.1
  have h2 : v ≤ lpObj mk βs := by
    rw [← hβ0v]; unfold lpObj
    have := hβsOpt β0 hβ0.1 hβ0.2.1 hβ0.2.2
    linarith
  have h3 : lpObj mk βs = 2 * graphWeight (supportGraph βs) (wtFun (rho mk) βs) := by
    rw [graphWeight_eq (rho mk) βs _ le_rfl, lpObj]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun w _ => ?_))
    classical
    rw [supportGraph_adj_cross]
    split_ifs with h
    · rfl
    · have : βs m w = 0 := le_antisymm (not_lt.mp h) (hβs0 m w)
      rw [this, mul_zero]
  have h5 : graphWeight H (wtFun (rho mk) βs) = ∑ m, ∑ w, rho mk m w * βH m w := by
    rw [graphWeight_eq (rho mk) βs _ hHG]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun w _ => ?_))
    simp only [hβH, restrictB]
    split_ifs <;> simp
  have h6 : 2 * ∑ m, ∑ w, rho mk m w * βH m w =
      ∑ i, lpObj (subMarket cM cW mk i) (fun m w => βH m.1 w.1) := by
    simp only [lpObj, ← Finset.mul_sum]
    congr 1
    rw [← Fintype.sum_fiberwise cM]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [sum_block cW i (fun w => rho mk m.1 w * βH m.1 w) (fun w hw => by
      have : βH m.1 w = 0 := by
        by_contra hne; exact hw ((hβHblock _ _ hne).trans m.2)
      simp [this])]
    rfl
  have h7 : ∑ i, lpObj (subMarket cM cW mk i) (fun m w => βH m.1 w.1) ≤
      ∑ i, 2 * sbWelfare (subMarket cM cW mk i) (P i) := Finset.sum_le_sum (fun i _ => hPw i)
  rw [glue_welfare P mk]
  rw [← Finset.mul_sum] at h7
  linarith
