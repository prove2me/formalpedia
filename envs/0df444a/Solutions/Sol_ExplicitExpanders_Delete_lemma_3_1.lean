-- Prove2me | solution 1 for ExplicitExpanders.Delete.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T21:44:10.070575+00:00
-- url     : https://prove2.me/submissions/98a843f1-ba48-42eb-af62-b116d0cb8731

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods

set_option autoImplicit false

namespace P2MLemma31

open ExplicitExpanders.Delete Finset

section

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- darts with both ends in `T` (twice the number of edges inside `T`). -/
def DT (T : Finset V) : Finset G.Dart := univ.filter (fun d => d.fst ∈ T ∧ d.snd ∈ T)

variable {G}

lemma mem_DT {T : Finset V} {d : G.Dart} : d ∈ DT G T ↔ d.fst ∈ T ∧ d.snd ∈ T := by
  simp [DT]

variable (G)

lemma DT_mono {S T : Finset V} (h : S ⊆ T) : DT G S ⊆ DT G T := by
  intro d hd; rw [mem_DT] at *; exact ⟨h hd.1, h hd.2⟩

lemma DT_empty : DT G (∅ : Finset V) = ∅ := by
  ext d; simp [mem_DT]

lemma DT_union_inter (S T : Finset V) :
    #(DT G S) + #(DT G T) ≤ #(DT G (S ∪ T)) + #(DT G (S ∩ T)) := by
  rw [← card_union_add_card_inter]
  have h1 : DT G S ∪ DT G T ⊆ DT G (S ∪ T) :=
    union_subset (DT_mono G subset_union_left) (DT_mono G subset_union_right)
  have h2 : DT G S ∩ DT G T = DT G (S ∩ T) := by
    ext d; simp only [mem_inter, mem_DT]; tauto
  rw [h2]
  exact Nat.add_le_add_right (card_le_card h1) _

lemma DT_cross {X Y : Finset V} (hXY : Disjoint X Y) {x y : V} (hx : x ∈ X) (hy : y ∈ Y)
    (hadj : G.Adj x y) : #(DT G X) + #(DT G Y) + 2 ≤ #(DT G (X ∪ Y)) := by
  obtain ⟨d1, h1f, h1s⟩ : ∃ d : G.Dart, d.fst = x ∧ d.snd = y := ⟨⟨(x, y), hadj⟩, rfl, rfl⟩
  obtain ⟨d2, h2f, h2s⟩ : ∃ d : G.Dart, d.fst = y ∧ d.snd = x := ⟨⟨(y, x), hadj.symm⟩, rfl, rfl⟩
  have hxY : x ∉ Y := disjoint_left.mp hXY hx
  have hyX : y ∉ X := disjoint_right.mp hXY hy
  have hdisj : Disjoint (DT G X) (DT G Y) := by
    rw [disjoint_left]; intro d h1 h2; rw [mem_DT] at h1 h2
    exact disjoint_left.mp hXY h1.1 h2.1
  have hne : d1 ≠ d2 := by
    intro h; rw [h] at h1f; rw [h1f] at h2f; exact hadj.ne h2f
  have hsub : (DT G X ∪ DT G Y) ∪ {d1, d2} ⊆ DT G (X ∪ Y) := by
    intro d hd
    simp only [mem_union, mem_insert, mem_singleton] at hd
    rw [mem_DT]
    rcases hd with (hd | hd) | hd | hd
    · rw [mem_DT] at hd; exact ⟨mem_union_left _ hd.1, mem_union_left _ hd.2⟩
    · rw [mem_DT] at hd; exact ⟨mem_union_right _ hd.1, mem_union_right _ hd.2⟩
    · subst hd; rw [h1f, h1s]; exact ⟨mem_union_left _ hx, mem_union_right _ hy⟩
    · subst hd; rw [h2f, h2s]; exact ⟨mem_union_right _ hy, mem_union_left _ hx⟩
  have hdisj2 : Disjoint (DT G X ∪ DT G Y) {d1, d2} := by
    rw [disjoint_left]; intro d hd hd2
    simp only [mem_union, mem_insert, mem_singleton] at hd hd2
    rcases hd2 with rfl | rfl <;> rcases hd with hd | hd <;> rw [mem_DT] at hd
    · rw [h1s] at hd; exact hyX hd.2
    · rw [h1f] at hd; exact hxY hd.1
    · rw [h2f] at hd; exact hyX hd.1
    · rw [h2s] at hd; exact hxY hd.2
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj2, card_union_of_disjoint hdisj, card_pair hne] at this
  exact this

lemma DT_insert {T : Finset V} {v t : V} (hv : v ∉ T) (ht : t ∈ T) (hadj : G.Adj t v) :
    #(DT G T) + 2 ≤ #(DT G (insert v T)) := by
  have h := DT_cross G (X := T) (Y := {v}) (disjoint_singleton_right.mpr hv) ht
    (mem_singleton_self v) hadj
  rw [insert_eq, union_comm]; omega

/-- `W` is connected from a centre, by walks inside `W`. -/
def Conn (W : Finset V) : Prop :=
  ∃ c ∈ W, ∀ a ∈ W, ∃ p : G.Walk c a, ∀ x ∈ p.support, x ∈ W

def Sparse (W : Finset V) : Prop := ∀ T ⊆ W, #(DT G T) ≤ 2 * #T

def Dense (T : Finset V) : Prop := 2 * #T ≤ #(DT G T)

lemma exists_adj_out {W T : Finset V} (hW : Conn G W) (hTW : T ⊆ W) {t0 a : V} (ht0 : t0 ∈ T)
    (ha : a ∈ W) (haT : a ∉ T) : ∃ v ∈ W, v ∉ T ∧ ∃ t ∈ T, G.Adj t v := by
  obtain ⟨c, -, hc⟩ := hW
  obtain ⟨p, hp⟩ := hc t0 (hTW ht0)
  obtain ⟨q, hq⟩ := hc a ha
  obtain ⟨d, hd, hd1, hd2⟩ :=
    (p.reverse.append q).exists_boundary_dart (T : Set V) (Finset.mem_coe.mpr ht0)
      (by simpa using haT)
  refine ⟨d.snd, ?_, by simpa using hd2, d.fst, by simpa using hd1, d.adj⟩
  have := (p.reverse.append q).dart_snd_mem_support_of_mem_darts hd
  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse] at this
  rcases this with h | h
  · exact hp _ h
  · exact hq _ h

lemma grow {W : Finset V} (hW : Conn G W) (n : ℕ) : ∀ (T : Finset V), T ⊆ W → T.Nonempty →
    #(W \ T) = n → #(DT G T) + 2 * #(W \ T) ≤ #(DT G W) := by
  induction n with
  | zero =>
    intro T hTW _ hn
    have : W ⊆ T := by
      intro a ha; by_contra h
      have : a ∈ W \ T := mem_sdiff.mpr ⟨ha, h⟩
      rw [card_eq_zero] at hn; simp [hn] at this
    have hWT : T = W := Subset.antisymm hTW this
    subst hWT; simp
  | succ n ih =>
    intro T hTW hT hn
    obtain ⟨a, ha⟩ : (W \ T).Nonempty := by rw [← card_pos]; omega
    rw [mem_sdiff] at ha
    obtain ⟨t0, ht0⟩ := hT
    obtain ⟨v, hvW, hvT, t, ht, hadj⟩ := exists_adj_out G hW hTW ht0 ha.1 ha.2
    have h1 := DT_insert G hvT ht hadj
    have hsub : insert v T ⊆ W := insert_subset hvW hTW
    have hcard : #(W \ insert v T) = n := by
      rw [sdiff_insert, card_erase_of_mem (mem_sdiff.mpr ⟨hvW, hvT⟩)]; omega
    have h2 := ih (insert v T) hsub (insert_nonempty v T) hcard
    rw [hcard] at h2; omega

lemma sparse_of_conn {W : Finset V} (hW : Conn G W) (hb : #(DT G W) ≤ 2 * #W) : Sparse G W := by
  intro T hT
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp [DT_empty]
  · have := grow G hW _ T hT hne rfl
    have h2 := card_sdiff_add_card_eq_card hT
    omega

lemma sparse_mono {W W' : Finset V} (h : W ⊆ W') (hS : Sparse G W') : Sparse G W :=
  fun T hT => hS T (hT.trans h)

lemma inter_nonempty {W : Finset V} (hW : Conn G W) (hS : Sparse G W) (n : ℕ) :
    ∀ (X Y : Finset V), X ⊆ W → Y ⊆ W → X.Nonempty → Y.Nonempty → Dense G X → Dense G Y →
    #(W \ (X ∪ Y)) = n → (X ∩ Y).Nonempty := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y hX hY hXn hYn hXd hYd hn
  by_contra hempty
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hempty
  obtain ⟨x0, hx0⟩ := hXn
  obtain ⟨y0, hy0⟩ := hYn
  have hy0X : y0 ∉ X := disjoint_right.mp hempty hy0
  obtain ⟨v, hvW, hvX, t, ht, hadj⟩ := exists_adj_out G hW hX hx0 (hY hy0) hy0X
  by_cases hvY : v ∈ Y
  · have h1 := DT_cross G hempty ht hvY hadj
    have h2 := hS (X ∪ Y) (union_subset hX hY)
    rw [card_union_of_disjoint hempty] at h2
    unfold Dense at hXd hYd
    omega
  · have hX'd : Dense G (insert v X) := by
      have := DT_insert G hvX ht hadj
      unfold Dense at hXd ⊢; rw [card_insert_of_notMem hvX]; omega
    have hdisj' : Disjoint (insert v X) Y := disjoint_insert_left.mpr ⟨hvY, hempty⟩
    have hlt : #(W \ (insert v X ∪ Y)) < n := by
      rw [← hn]
      have hsub : W \ (insert v X ∪ Y) ⊆ W \ (X ∪ Y) := by
        intro z hz; simp only [mem_sdiff, mem_union, mem_insert] at hz ⊢; tauto
      apply card_lt_card
      rw [ssubset_iff_of_subset hsub]
      exact ⟨v, mem_sdiff.mpr ⟨hvW, by simp [hvX, hvY]⟩, by simp⟩
    obtain ⟨z, hz⟩ := ih _ hlt (insert v X) Y (insert_subset hvW hX) hY (insert_nonempty v X)
      ⟨y0, hy0⟩ hX'd hYd rfl
    rw [mem_inter] at hz
    exact disjoint_left.mp hdisj' hz.1 hz.2

lemma dense_inter {W X Y : Finset V} (hS : Sparse G W) (hX : X ⊆ W) (hY : Y ⊆ W)
    (hXd : Dense G X) (hYd : Dense G Y) : Dense G (X ∩ Y) := by
  have h1 := DT_union_inter G X Y
  have h2 := hS (X ∪ Y) (union_subset hX hY)
  have h3 := card_union_add_card_inter X Y
  unfold Dense at *; omega

end

end P2MLemma31

set_option linter.unusedSectionVars false
namespace P2MLemma31

open ExplicitExpanders.Delete Finset

section

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def bf (x : V) (k : ℕ) : Finset V := by
  classical exact univ.filter (fun w => G.edist x w ≤ (k : ℕ∞))

variable {G}

lemma mem_bf {x w : V} {k : ℕ} : w ∈ bf G x k ↔ G.edist x w ≤ (k : ℕ∞) := by
  classical
  unfold bf; simp

variable (G)

lemma bf_mono {x : V} {k l : ℕ} (h : k ≤ l) : bf G x k ⊆ bf G x l := fun w hw =>
  mem_bf.mpr ((mem_bf.mp hw).trans (by exact_mod_cast h))

lemma conn_bf (x : V) (k : ℕ) : Conn G (bf G x k) := by
  refine ⟨x, mem_bf.mpr (by simp), fun a ha => ?_⟩
  have ha' := mem_bf.mp ha
  have hne : G.edist x a ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top k) ha'
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  refine ⟨p, fun y hy => mem_bf.mpr ?_⟩
  calc G.edist x y ≤ (p.takeUntil y hy).length := SimpleGraph.edist_le _
    _ ≤ p.length := by exact_mod_cast p.length_takeUntil_le_length hy
    _ = G.edist x a := hp
    _ ≤ k := ha'

lemma DT_bf_le (x : V) (k : ℕ) (h : AtMostOneCycleOn G (ball G x k)) :
    #(DT G (bf G x k)) ≤ 2 * #(bf G x k) := by
  classical
  unfold AtMostOneCycleOn at h
  have hS : ball G x k = ((bf G x k : Finset V) : Set V) := by
    ext w; simp [ball, mem_bf]
  rw [hS, Set.ncard_coe_finset] at h
  let e : (G.induce (bf G x k : Set V)).Dart ≃ {d : G.Dart // d ∈ DT G (bf G x k)} :=
    { toFun := fun d => ⟨⟨(d.fst.1, d.snd.1), d.adj⟩, mem_DT.mpr ⟨d.fst.2, d.snd.2⟩⟩
      invFun := fun d => ⟨(⟨d.1.fst, (mem_DT.mp d.2).1⟩, ⟨d.1.snd, (mem_DT.mp d.2).2⟩), d.1.adj⟩
      left_inv := fun d => rfl
      right_inv := fun d => rfl }
  have h1 : Fintype.card (G.induce (bf G x k : Set V)).Dart = #(DT G (bf G x k)) := by
    rw [Fintype.card_congr e, Fintype.card_coe]
  have h2 := (G.induce (bf G x k : Set V)).dart_card_eq_twice_card_edges
  have h3 : #(G.induce (bf G x k : Set V)).edgeFinset =
      (G.induce (bf G x k : Set V)).edgeSet.ncard := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega

lemma dense_of_cycle {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    Dense G c.support.toFinset := by
  unfold Dense
  have hlen : #c.support.toFinset = c.length := by
    have h2 : u ∈ c.support.tail := SimpleGraph.Walk.end_mem_tail_support hc.not_nil
    rw [c.support_eq_cons, List.toFinset_cons, insert_eq_of_mem (List.mem_toFinset.mpr h2),
      List.toFinset_card_of_nodup hc.support_nodup, List.length_tail,
      SimpleGraph.Walk.length_support]
    simp
  have hed : (c.darts.map SimpleGraph.Dart.edge).Nodup := hc.edges_nodup
  have hd : c.darts.Nodup := hed.of_map _
  have hnd : (c.darts ++ c.darts.map SimpleGraph.Dart.symm).Nodup := by
    rw [List.nodup_append]
    refine ⟨hd, hd.map SimpleGraph.Dart.symm_involutive.injective, ?_⟩
    intro a ha b hb hab
    rw [List.mem_map] at hb
    obtain ⟨e, he, rfl⟩ := hb
    subst hab
    have := List.inj_on_of_nodup_map hed ha he (by simp)
    exact e.symm_ne this
  have hsub : (c.darts ++ c.darts.map SimpleGraph.Dart.symm).toFinset ⊆
      DT G c.support.toFinset := by
    intro d hd
    rw [List.mem_toFinset, List.mem_append, List.mem_map] at hd
    rw [mem_DT, List.mem_toFinset, List.mem_toFinset]
    rcases hd with hd | ⟨e, he, rfl⟩
    · exact ⟨c.dart_fst_mem_support_of_mem_darts hd, c.dart_snd_mem_support_of_mem_darts hd⟩
    · exact ⟨c.dart_snd_mem_support_of_mem_darts he, c.dart_fst_mem_support_of_mem_darts he⟩
  have := card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_append, List.length_map,
    SimpleGraph.Walk.length_darts] at this
  omega

lemma exists_dense_of_not_noCycle {b : V} {k : ℕ} (h : ¬ NoCycleOn G (ball G b k)) :
    ∃ T ⊆ bf G b k, T.Nonempty ∧ Dense G T := by
  unfold NoCycleOn SimpleGraph.IsAcyclic at h
  push_neg at h
  obtain ⟨u, c, hc⟩ := h
  have hf : Function.Injective (SimpleGraph.Embedding.induce (G := G) (ball G b k)).toHom :=
    (SimpleGraph.Embedding.induce (G := G) (ball G b k)).injective
  have hc' := hc.map hf
  refine ⟨(c.map (SimpleGraph.Embedding.induce (G := G) (ball G b k)).toHom).support.toFinset,
    ?_, ⟨_, List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support _)⟩, dense_of_cycle G hc'⟩
  intro w hw
  rw [List.mem_toFinset, SimpleGraph.Walk.support_map, List.mem_map] at hw
  obtain ⟨z, -, rfl⟩ := hw
  exact mem_bf.mpr z.2

end

end P2MLemma31

namespace P2MLemma31

open ExplicitExpanders.Delete Finset

section

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def cands (r : ℕ) (b : V) : Finset (Finset V) := by
  classical exact (bf G b (r+1)).powerset.filter (fun T => T.Nonempty ∧ Dense G T)

lemma mem_cands {r : ℕ} {b : V} {T : Finset V} :
    T ∈ cands G r b ↔ T ⊆ bf G b (r+1) ∧ T.Nonempty ∧ Dense G T := by
  classical
  unfold cands; simp

noncomputable def Cyc (r : ℕ) (b : V) : Finset V :=
  if h : (cands G r b).Nonempty then Classical.choose (exists_min_image (cands G r b) card h)
  else ∅

lemma Cyc_spec {r : ℕ} {b : V} (h : ¬ NoCycleOn G (ball G b (r+1))) :
    Cyc G r b ⊆ bf G b (r+1) ∧ (Cyc G r b).Nonempty ∧ Dense G (Cyc G r b) ∧
    ∀ T ⊆ bf G b (r+1), T.Nonempty → Dense G T → #(Cyc G r b) ≤ #T := by
  have hne : (cands G r b).Nonempty := by
    obtain ⟨T, hT, hTn, hTd⟩ := exists_dense_of_not_noCycle G h
    exact ⟨T, (mem_cands G).mpr ⟨hT, hTn, hTd⟩⟩
  have hs := Classical.choose_spec (exists_min_image (cands G r b) card hne)
  have hC : Cyc G r b = Classical.choose (exists_min_image (cands G r b) card hne) := by
    unfold Cyc; rw [dif_pos hne]
  rw [hC]
  obtain ⟨hmem, hmin⟩ := hs
  rw [mem_cands G] at hmem
  exact ⟨hmem.1, hmem.2.1, hmem.2.2, fun T hT hTn hTd => hmin T ((mem_cands G).mpr ⟨hT, hTn, hTd⟩)⟩

lemma sparse_ball {r : ℕ} (hcyc : ∀ v : V, AtMostOneCycleOn G (ball G v (2 * r + 4))) (x : V) :
    Sparse G (bf G x (2 * r + 4)) :=
  sparse_of_conn G (conn_bf G x _) (DT_bf_le G x _ (hcyc x))

lemma Cyc_eq {r : ℕ} (hcyc : ∀ v : V, AtMostOneCycleOn G (ball G v (2 * r + 4))) {b b' : V}
    (hb : ¬ NoCycleOn G (ball G b (r+1))) (hb' : ¬ NoCycleOn G (ball G b' (r+1)))
    (hadj : G.Adj b b') : Cyc G r b = Cyc G r b' := by
  obtain ⟨h1, h2, h3, h4⟩ := Cyc_spec G hb
  obtain ⟨h1', h2', h3', h4'⟩ := Cyc_spec G hb'
  have hW : Conn G (bf G b (r+2)) := conn_bf G b _
  have hSW : Sparse G (bf G b (r+2)) :=
    sparse_mono G (bf_mono G (by omega)) (sparse_ball G hcyc b)
  have hCW : Cyc G r b ⊆ bf G b (r+2) := h1.trans (bf_mono G (by omega))
  have hC'W : Cyc G r b' ⊆ bf G b (r+2) := by
    intro w hw
    have := mem_bf.mp (h1' hw)
    apply mem_bf.mpr
    calc G.edist b w ≤ G.edist b b' + G.edist b' w := SimpleGraph.edist_triangle
      _ ≤ 1 + ((r+1 : ℕ) : ℕ∞) :=
          add_le_add (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr hadj)) this
      _ = ((r+2 : ℕ) : ℕ∞) := by push_cast; ring
  have hI := inter_nonempty G hW hSW _ _ _ hCW hC'W h2 h2' h3 h3' rfl
  have hD := dense_inter G hSW hCW hC'W h3 h3'
  have e1 : Cyc G r b ⊆ Cyc G r b' := by
    have := h4 _ (inter_subset_left.trans h1) hI hD
    have heq := eq_of_subset_of_card_le inter_subset_left this
    intro z hz
    have : z ∈ Cyc G r b ∩ Cyc G r b' := by rw [heq]; exact hz
    exact (mem_inter.mp this).2
  have e2 : Cyc G r b' ⊆ Cyc G r b := by
    have := h4' _ (inter_subset_right.trans h1') hI hD
    have heq := eq_of_subset_of_card_le inter_subset_right this
    intro z hz
    have : z ∈ Cyc G r b ∩ Cyc G r b' := by rw [heq]; exact hz
    exact (mem_inter.mp this).1
  exact Subset.antisymm e1 e2

lemma DT_bad_le {r : ℕ} (hcyc : ∀ v : V, AtMostOneCycleOn G (ball G v (2 * r + 4)))
    (B : Finset V) (hB : ∀ b, b ∈ B ↔ ¬ NoCycleOn G (ball G b (r+1))) :
    #(DT G B) ≤ 2 * #B := by
  classical
  have hcover : DT G B ⊆ (B.image (Cyc G r)).biUnion
      (fun C => DT G (B.filter (fun b => Cyc G r b = C))) := by
    intro d hd
    rw [mem_DT] at hd
    rw [mem_biUnion]
    refine ⟨Cyc G r d.fst, mem_image_of_mem _ hd.1, ?_⟩
    rw [mem_DT]
    have heq := Cyc_eq G hcyc ((hB _).mp hd.1) ((hB _).mp hd.2) d.adj
    simp only [mem_filter]
    exact ⟨⟨hd.1, trivial⟩, ⟨hd.2, heq.symm⟩⟩
  have hclass : ∀ C ∈ B.image (Cyc G r),
      #(DT G (B.filter (fun b => Cyc G r b = C))) ≤ 2 * #(B.filter (fun b => Cyc G r b = C)) := by
    intro C hC
    rw [mem_image] at hC
    obtain ⟨b0, hb0, rfl⟩ := hC
    obtain ⟨-, ⟨c, hc⟩, -, -⟩ := Cyc_spec G ((hB b0).mp hb0)
    refine sparse_ball G hcyc c _ ?_
    intro b hb
    simp only [mem_filter] at hb
    obtain ⟨h1, -, -, -⟩ := Cyc_spec G ((hB b).mp hb.1)
    have : c ∈ bf G b (r+1) := h1 (by rw [hb.2]; exact hc)
    rw [mem_bf] at this ⊢
    rw [SimpleGraph.edist_comm]
    exact this.trans (by exact_mod_cast (by omega : r + 1 ≤ 2 * r + 4))
  calc #(DT G B) ≤ #((B.image (Cyc G r)).biUnion
        (fun C => DT G (B.filter (fun b => Cyc G r b = C)))) := card_le_card hcover
    _ ≤ ∑ C ∈ B.image (Cyc G r), #(DT G (B.filter (fun b => Cyc G r b = C))) := card_biUnion_le
    _ ≤ ∑ C ∈ B.image (Cyc G r), 2 * #(B.filter (fun b => Cyc G r b = C)) := sum_le_sum hclass
    _ = 2 * #B := by rw [← mul_sum, ← card_eq_sum_card_image]

lemma card_fst_mem {d : ℕ} (hreg : G.IsRegularOfDegree d) (S : Finset V) :
    #(univ.filter (fun x : G.Dart => x.fst ∈ S)) = d * #S := by
  rw [card_eq_sum_card_fiberwise (f := fun x : G.Dart => x.fst) (t := S)
    (by intro x hx; simpa using hx)]
  have : ∀ b ∈ S, #{a ∈ univ.filter (fun x : G.Dart => x.fst ∈ S) | a.fst = b} = d := by
    intro b hb
    rw [filter_filter]
    have : (univ.filter (fun a : G.Dart => a.fst ∈ S ∧ a.fst = b)) =
        univ.filter (fun a : G.Dart => a.fst = b) := by
      ext a; simp only [mem_filter, mem_univ, true_and]; constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hb, h⟩
    rw [this, G.dart_fst_fiber_card_eq_degree b, hreg b]
  rw [sum_const_nat this, mul_comm]

lemma card_snd_mem (S : Finset V) :
    #(univ.filter (fun x : G.Dart => x.snd ∈ S)) = #(univ.filter (fun x : G.Dart => x.fst ∈ S)) := by
  apply card_nbij' SimpleGraph.Dart.symm SimpleGraph.Dart.symm
  · intro a ha; simpa using ha
  · intro a ha; simpa using ha
  · intro a _; simp
  · intro a _; simp

lemma bad_le_three_good {d : ℕ} (hd : 3 ≤ d) (hreg : G.IsRegularOfDegree d) (B : Finset V)
    (hB : #(DT G B) ≤ 2 * #B) : #B ≤ 3 * #Bᶜ := by
  have h1 := card_fst_mem G hreg B
  have h2 := card_fst_mem G hreg Bᶜ
  have h3 := card_snd_mem G Bᶜ
  have hsplit : univ.filter (fun x : G.Dart => x.fst ∈ B) ⊆
      DT G B ∪ univ.filter (fun x : G.Dart => x.snd ∈ Bᶜ) := by
    intro x hx; simp only [mem_filter, mem_univ, true_and] at hx
    rw [mem_union, mem_DT]; simp only [mem_filter, mem_univ, true_and, mem_compl]
    by_cases h : x.snd ∈ B
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  have h4 := (card_le_card hsplit).trans (card_union_le _ _)
  rw [h1, h3, h2] at h4
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
  by_contra hlt
  push_neg at hlt
  nlinarith [Nat.mul_le_mul_left e (show #Bᶜ ≤ #B by omega)]

lemma bf_zero (x : V) : bf G x 0 = {x} := by
  ext w; rw [mem_bf, mem_singleton]
  simp only [Nat.cast_zero, nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff]
  exact eq_comm

lemma bf_succ_subset (x : V) (k : ℕ) :
    bf G x (k+1) ⊆ insert x ((G.neighborFinset x).biUnion (fun w => bf G w k)) := by
  intro y hy
  rw [mem_bf] at hy
  rw [mem_insert, mem_biUnion]
  by_cases hxy : y = x
  · exact Or.inl hxy
  right
  have hne : G.edist x y ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hy
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  cases p with
  | nil => exact absurd rfl hxy
  | cons h q =>
    refine ⟨_, (G.mem_neighborFinset _ _).mpr h, mem_bf.mpr ?_⟩
    rw [SimpleGraph.Walk.length_cons] at hp
    have h5 : ((q.length + 1 : ℕ) : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := hp ▸ hy
    have h6 : q.length ≤ k := by
      have := ENat.coe_le_coe.mp h5
      omega
    exact (SimpleGraph.edist_le q).trans (by exact_mod_cast h6)

def gs (d k : ℕ) : ℕ := ∑ i ∈ range (k+1), d^i

lemma gs_succ (d k : ℕ) : gs d (k+1) = d * gs d k + 1 := by
  unfold gs
  rw [sum_range_succ' (fun i => d^i) (k+1), mul_sum]
  simp only [pow_zero]
  congr 1
  apply sum_congr rfl; intro i _; ring

lemma gs_bound {d : ℕ} (hd : 3 ≤ d) (k : ℕ) : 2 * gs d k + 1 ≤ d^(k+1) := by
  induction k with
  | zero => simp only [gs, zero_add, range_one, sum_singleton, pow_zero, pow_one]; omega
  | succ k ih => rw [gs_succ, pow_succ]; nlinarith [Nat.mul_le_mul_right d ih]

lemma card_bf_le {d : ℕ} (hreg : G.IsRegularOfDegree d) (k : ℕ) :
    ∀ x : V, #(bf G x k) ≤ gs d k := by
  induction k with
  | zero => intro x; simp [bf_zero, gs]
  | succ k ih =>
    intro x
    calc #(bf G x (k+1)) ≤ #(insert x ((G.neighborFinset x).biUnion (fun w => bf G w k))) :=
          card_le_card (bf_succ_subset G x k)
      _ ≤ #((G.neighborFinset x).biUnion (fun w => bf G w k)) + 1 := card_insert_le _ _
      _ ≤ (∑ w ∈ G.neighborFinset x, #(bf G w k)) + 1 := by gcongr; exact card_biUnion_le
      _ ≤ (∑ w ∈ G.neighborFinset x, gs d k) + 1 := by gcongr with w; exact ih w
      _ = d * gs d k + 1 := by
          rw [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, hreg x]
      _ = gs d (k+1) := (gs_succ d k).symm

lemma exists_far (Gd : Finset V) (m : ℕ) (hm : 0 < m) : ∃ U ⊆ Gd,
    (∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((m : ℕ) : ℕ∞) ≤ G.edist z z') ∧
    ∀ g ∈ Gd, ∃ u ∈ U, G.edist u g < (m : ℕ∞) := by
  classical
  let F := Gd.powerset.filter
    (fun U => ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((m : ℕ) : ℕ∞) ≤ G.edist z z')
  have hF : F.Nonempty := ⟨∅, by simp [F]⟩
  obtain ⟨U, hU, hmax⟩ := exists_max_image F card hF
  simp only [F, mem_filter, mem_powerset] at hU hmax
  refine ⟨U, hU.1, hU.2, fun g hg => ?_⟩
  by_contra hno
  push_neg at hno
  have hgU : g ∉ U := fun h => by
    have := hno g h
    rw [SimpleGraph.edist_self] at this
    have : m = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp this
    omega
  have hmem : insert g U ⊆ Gd ∧ ∀ z ∈ insert g U, ∀ z' ∈ insert g U, z ≠ z' →
      ((m : ℕ) : ℕ∞) ≤ G.edist z z' := by
    refine ⟨insert_subset hg hU.1, ?_⟩
    intro z hz z' hz' hne
    rw [mem_insert] at hz hz'
    rcases hz with rfl | hz <;> rcases hz' with rfl | hz'
    · exact absurd rfl hne
    · rw [SimpleGraph.edist_comm]; exact hno z' hz'
    · exact hno z hz
    · exact hU.2 z hz z' hz' hne
  have := hmax _ hmem
  rw [card_insert_of_notMem hgU] at this; omega

end

end P2MLemma31

open ExplicitExpanders.Delete in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d r : ℕ) (hd : 3 ≤ d) (hreg : G.IsRegularOfDegree d)
    (hcyc : ∀ v : V, AtMostOneCycleOn G (ball G v (2 * r + 4)))
    (hr : (r : ℝ) ≤ Real.logb ((d : ℝ) - 1) (Fintype.card V)) :
    ∃ U : Finset V,
      (Fintype.card V : ℝ) / (2 * (d : ℝ) ^ (2 * r + 3)) ≤ (U.card : ℝ) ∧
      (∀ z ∈ U, NoCycleOn G (ball G z (r + 1))) ∧
      (∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ G.edist z z') := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Finset V, ∀ b, b ∈ B ↔ ¬ NoCycleOn G (ball G b (r+1)) :=
    ⟨Finset.univ.filter (fun b => ¬ NoCycleOn G (ball G b (r+1))), by simp⟩
  have h1 := P2MLemma31.DT_bad_le G hcyc B hB
  have h2 := P2MLemma31.bad_le_three_good G hd hreg B h1
  obtain ⟨U, hUsub, hUfar, hUcov⟩ := P2MLemma31.exists_far G Bᶜ (2 * r + 3) (by omega)
  refine ⟨U, ?_, ?_, hUfar⟩
  · have hcov : Bᶜ ⊆ U.biUnion (fun u => P2MLemma31.bf G u (2 * r + 2)) := by
      intro g hg
      obtain ⟨u, hu, hlt⟩ := hUcov g hg
      rw [Finset.mem_biUnion]
      refine ⟨u, hu, P2MLemma31.mem_bf.mpr ?_⟩
      have heq : (((2 * r + 3 : ℕ)) : ℕ∞) = ((2 * r + 2 : ℕ) : ℕ∞) + 1 := by push_cast; ring
      rw [heq] at hlt
      exact (ENat.lt_add_one_iff (ENat.coe_ne_top _)).mp hlt
    have h3 : Bᶜ.card ≤ U.card * P2MLemma31.gs d (2 * r + 2) := by
      calc Bᶜ.card ≤ (U.biUnion (fun u => P2MLemma31.bf G u (2 * r + 2))).card :=
            Finset.card_le_card hcov
        _ ≤ ∑ u ∈ U, (P2MLemma31.bf G u (2 * r + 2)).card := Finset.card_biUnion_le
        _ ≤ ∑ u ∈ U, P2MLemma31.gs d (2 * r + 2) :=
            Finset.sum_le_sum (fun u _ => P2MLemma31.card_bf_le G hreg _ u)
        _ = U.card * P2MLemma31.gs d (2 * r + 2) := by rw [Finset.sum_const, smul_eq_mul]
    have h4 := P2MLemma31.gs_bound hd (2 * r + 2)
    have h5 := Finset.card_compl B
    have h6 := Finset.card_le_univ B
    have key : Fintype.card V ≤ 2 * U.card * d ^ (2 * r + 3) := by
      have h7 : 2 * r + 2 + 1 = 2 * r + 3 := by ring
      rw [h7] at h4
      have h8 : B.card + Bᶜ.card = Fintype.card V := by omega
      have h9 := Nat.mul_le_mul_left U.card h4
      nlinarith [h9, h8, h3, h2]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    rw [div_le_iff₀ (mul_pos two_pos (pow_pos hdpos _))]
    have key' : ((Fintype.card V : ℕ) : ℝ) ≤ ((2 * U.card * d ^ (2 * r + 3) : ℕ) : ℝ) := by
      exact_mod_cast key
    push_cast at key'
    linarith
  · intro z hz
    have := Finset.mem_compl.mp (hUsub hz)
    rw [hB] at this
    exact not_not.mp this
