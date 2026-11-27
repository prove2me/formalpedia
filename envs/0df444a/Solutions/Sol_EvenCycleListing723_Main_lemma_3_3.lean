-- Prove2me | solution 1 for EvenCycleListing723.Main.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:01:36.770448+00:00
-- url     : https://prove2.me/submissions/6bd54086-d702-4b5d-9a75-94cf0f5c0b88

import Mathlib
import Definitions.Def_EvenCycleListing723_Main_GraphModel

set_option autoImplicit false

open EvenCycleListing723.Main
open Classical

namespace L33Aux

section Cyc
variable {V : Type*} {G : SimpleGraph V}

lemma walk_of_fun (g : ℕ → V) : ∀ (len a : ℕ), (∀ i, a ≤ i → i < a + len → G.Adj (g i) (g (i+1))) →
    ∃ p : G.Walk (g a) (g (a+len)), p.support = (List.range (len+1)).map (fun i => g (a+i)) ∧
      p.length = len ∧ ∀ e, e ∈ p.edges ↔ ∃ i < len, e = s(g (a+i), g (a+i+1)) := by
  intro len
  induction len with
  | zero =>
    intro a _
    refine ⟨SimpleGraph.Walk.nil, ?_, rfl, ?_⟩
    · simp
    · intro e; simp
  | succ len ih =>
    intro a hadj
    obtain ⟨p, hps, hpl, hpe⟩ := ih (a+1) (fun i h1 h2 => hadj i (by omega) (by omega))
    have hA : G.Adj (g a) (g (a+1)) := hadj a le_rfl (by omega)
    have heq : a + 1 + len = a + (len + 1) := by omega
    refine ⟨(SimpleGraph.Walk.cons hA p).copy rfl (by rw [heq]), ?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons, hps]
      conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      congr 1; omega
    · simp [hpl]
    · intro e
      rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_cons, List.mem_cons, hpe]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact ⟨0, by omega, by simpa using h⟩
        · refine ⟨i+1, by omega, ?_⟩
          rw [h]; congr 2 <;> omega
      · rintro ⟨i, hi, h⟩
        rcases i with _ | i
        · left; simpa using h
        · right; refine ⟨i, by omega, ?_⟩
          rw [h]; congr 2 <;> omega

lemma isCycle_cons_of_path {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hadj : G.Adj b a)
    (hlen : 2 ≤ p.length) : (SimpleGraph.Walk.cons hadj p).IsCycle := by
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨hp, ?_⟩
  intro he
  cases p with
  | nil => simp at hlen
  | cons h' q =>
    rename_i c
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨h1, _⟩ | ⟨h1, _⟩
      · subst h1
        exact hp.2 q.end_mem_support
      · subst h1
        have : q.length = 0 := by
          have := hp.1
          rw [SimpleGraph.Walk.isPath_iff_nil] at this
          exact SimpleGraph.Walk.length_eq_zero_iff.mpr this
        simp [this] at hlen
    · exact hp.2 (q.snd_mem_support_of_mem_edges he)

lemma cycle_of_fun (g : ℕ → V) (N : ℕ) (hN : 3 ≤ N)
    (hinj : ∀ i < N, ∀ i' < N, g i = g i' → i = i')
    (hadj : ∀ i < N, G.Adj (g i) (g (i+1))) (hwrap : g N = g 0) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = N ∧
      ∀ e, e ∈ c.edges ↔ ∃ i < N, e = s(g i, g (i+1)) := by
  obtain ⟨p, hps, hpl, hpe⟩ := walk_of_fun (G := G) g (N-1) 0
    (fun i _ h2 => hadj i (by omega))
  have hcl : G.Adj (g (0 + (N-1))) (g 0) := by
    have := hadj (N-1) (by omega)
    rw [show N - 1 + 1 = N by omega, hwrap] at this
    simpa using this
  have hpath : p.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hps]
    apply List.Nodup.map_on
    · intro i hi i' hi' h
      simp only [List.mem_range] at hi hi'
      simpa using hinj (0+i) (by omega) (0+i') (by omega) h
    · exact List.nodup_range
  refine ⟨_, SimpleGraph.Walk.cons hcl p, isCycle_cons_of_path p hpath hcl (by omega), ?_, ?_⟩
  · simp [hpl]; omega
  · intro e
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons, hpe]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · refine ⟨N-1, by omega, ?_⟩
        rw [h, show N - 1 + 1 = N by omega, hwrap]; simp
      · exact ⟨i, by omega, by simpa using h⟩
    · rintro ⟨i, hi, h⟩
      by_cases hi' : i = N - 1
      · left; subst hi'
        rw [h, show N - 1 + 1 = N by omega, hwrap]; simp
      · right; exact ⟨i, by omega, by simpa using h⟩

lemma cycle_deg_two {v : V} {c : G.Walk v v} (hc : c.IsCycle) {a b1 b2 b3 : V}
    (h1 : s(a, b1) ∈ c.edges) (h2 : s(a, b2) ∈ c.edges) (h3 : s(a, b3) ∈ c.edges)
    (h12 : b1 ≠ b2) (h13 : b3 ≠ b1) : b3 = b2 := by
  by_contra h23
  have ha : a ∈ c.support := c.fst_mem_support_of_mem_edges h1
  have hn := hc.ncard_neighborSet_toSubgraph_eq_two ha
  have hsub : ({b1, b2, b3} : Set V) ⊆ c.toSubgraph.neighborSet a := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [SimpleGraph.Subgraph.mem_neighborSet]
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    rcases hx with rfl | rfl | rfl <;> assumption
  have := Set.ncard_le_ncard hsub (c.finite_neighborSet_toSubgraph)
  rw [hn, Set.ncard_eq_three.mpr ⟨b1, b2, b3, h12, fun h => h13 h.symm, fun h => h23 (h.symm), rfl⟩]
    at this
  omega

end Cyc


lemma exists_parent {W : Type*} {H : SimpleGraph W} (hc : H.Connected) (r v : W) (hv : v ≠ r) :
    ∃ w, H.Adj v w ∧ H.dist r w + 1 = H.dist r v := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact absurd rfl hv
  | cons hadj q =>
    rename_i w
    refine ⟨w, hadj, ?_⟩
    have h1 : H.dist r w ≤ q.length := by
      rw [SimpleGraph.dist_comm]; exact SimpleGraph.dist_le q
    obtain ⟨q', hq'⟩ := hc.exists_walk_length_eq_dist r w
    have h2 : H.dist r v ≤ H.dist r w + 1 := by
      have := SimpleGraph.dist_le (q'.concat hadj.symm)
      simpa [hq'] using this
    rw [SimpleGraph.Walk.length_cons, SimpleGraph.dist_comm] at hp
    omega

section Tree
variable {n : ℕ} {G : SimpleGraph (Fin n)} (T : RootedTreeIn G)

/-- depth in the tree (subtype level) -/
noncomputable def sdep (v : {v // v ∈ T.vertices}) : ℕ := T.tree.dist T.root v

noncomputable def par (v : {v // v ∈ T.vertices}) : {v // v ∈ T.vertices} :=
  if h : ∃ w, T.tree.Adj v w ∧ sdep T w + 1 = sdep T v then h.choose else v

lemma sdep_eq_zero_iff (v : {v // v ∈ T.vertices}) : sdep T v = 0 ↔ v = T.root := by
  unfold sdep
  rw [T.isTree.connected.dist_eq_zero_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

lemma par_spec (v : {v // v ∈ T.vertices}) (hv : 1 ≤ sdep T v) :
    T.tree.Adj v (par T v) ∧ sdep T (par T v) + 1 = sdep T v := by
  have hne : v ≠ T.root := by
    intro h; rw [← sdep_eq_zero_iff] at h; omega
  have hex : ∃ w, T.tree.Adj v w ∧ sdep T w + 1 = sdep T v :=
    exists_parent T.isTree.connected T.root v hne
  unfold par
  rw [dif_pos hex]
  exact hex.choose_spec

lemma sdep_par (v : {v // v ∈ T.vertices}) : sdep T (par T v) = sdep T v - 1 := by
  by_cases hv : 1 ≤ sdep T v
  · have := (par_spec T v hv).2; omega
  · have h0 : sdep T v = 0 := by omega
    have hr : v = T.root := (sdep_eq_zero_iff T v).mp h0
    have hnex : ¬ ∃ w, T.tree.Adj v w ∧ sdep T w + 1 = sdep T v := by
      rintro ⟨w, _, hw⟩; omega
    unfold par; rw [dif_neg hnex]; omega

lemma sdep_iter (v : {v // v ∈ T.vertices}) (s : ℕ) : sdep T ((par T)^[s] v) = sdep T v - s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', sdep_par, ih]; omega

/-- depth on `Fin n` -/
noncomputable def dep (x : Fin n) : ℕ := if hx : x ∈ T.vertices then sdep T ⟨x, hx⟩ else 0

/-- ancestor at depth `i` -/
noncomputable def an (x : Fin n) (i : ℕ) : Fin n :=
  if hx : x ∈ T.vertices then ((par T)^[dep T x - i] ⟨x, hx⟩).val else x

lemma an_eq {x : Fin n} (hx : x ∈ T.vertices) (i : ℕ) :
    an T x i = ((par T)^[sdep T ⟨x, hx⟩ - i] ⟨x, hx⟩).val := by
  unfold an dep; rw [dif_pos hx, dif_pos hx]

lemma dep_eq {x : Fin n} (hx : x ∈ T.vertices) : dep T x = sdep T ⟨x, hx⟩ := by
  unfold dep; rw [dif_pos hx]

lemma an_mem {x : Fin n} (hx : x ∈ T.vertices) (i : ℕ) : an T x i ∈ T.vertices := by
  rw [an_eq T hx]; exact Subtype.prop _

lemma dep_an {x : Fin n} (hx : x ∈ T.vertices) {i : ℕ} (hi : i ≤ dep T x) :
    dep T (an T x i) = i := by
  rw [dep_eq T (an_mem T hx i)]
  have : (⟨an T x i, an_mem T hx i⟩ : {v // v ∈ T.vertices}) =
      (par T)^[sdep T ⟨x, hx⟩ - i] ⟨x, hx⟩ := by
    apply Subtype.ext; simp [an_eq T hx]
  rw [this, sdep_iter]
  rw [dep_eq T hx] at hi
  omega

lemma an_self {x : Fin n} (hx : x ∈ T.vertices) : an T x (dep T x) = x := by
  rw [an_eq T hx, dep_eq T hx]; simp

lemma an_an {x : Fin n} (hx : x ∈ T.vertices) {i i' : ℕ} (hii : i ≤ i') (hi' : i' ≤ dep T x) :
    an T (an T x i') i = an T x i := by
  have : (⟨an T x i', an_mem T hx i'⟩ : {v // v ∈ T.vertices}) =
      (par T)^[sdep T ⟨x, hx⟩ - i'] ⟨x, hx⟩ := by
    apply Subtype.ext; simp [an_eq T hx]
  rw [an_eq T (an_mem T hx i'), this, sdep_iter, ← Function.iterate_add_apply, an_eq T hx]
  rw [dep_eq T hx] at hi'
  congr 2
  omega

lemma adj_an {x : Fin n} (hx : x ∈ T.vertices) {i : ℕ} (hi : i + 1 ≤ dep T x) :
    G.Adj (an T x (i+1)) (an T x i) := by
  rw [an_eq T hx, an_eq T hx]
  rw [dep_eq T hx] at hi
  have hs : sdep T ⟨x, hx⟩ - i = (sdep T ⟨x, hx⟩ - (i+1)) + 1 := by omega
  rw [hs, Function.iterate_succ_apply']
  apply T.subgraph
  apply (par_spec T _ _).1
  rw [sdep_iter]; omega

lemma mem_layer (x : Fin n) (i : ℕ) : x ∈ treeLayer T i ↔ x ∈ T.vertices ∧ dep T x = i := by
  unfold treeLayer
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.prop, ?_⟩
    rw [dep_eq T v.prop]; exact hv
  · rintro ⟨hx, hd⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [dep_eq T hx] at hd; exact hd

lemma an_zero_eq {x y : Fin n} (hx : x ∈ T.vertices) (hy : y ∈ T.vertices) :
    an T x 0 = an T y 0 := by
  have h1 : dep T (an T x 0) = 0 := dep_an T hx (Nat.zero_le _)
  have h2 : dep T (an T y 0) = 0 := dep_an T hy (Nat.zero_le _)
  rw [dep_eq T (an_mem T hx 0), sdep_eq_zero_iff] at h1
  rw [dep_eq T (an_mem T hy 0), sdep_eq_zero_iff] at h2
  have := congrArg Subtype.val (h1.trans h2.symm)
  simpa using this

lemma an_mem_layer {x : Fin n} (hx : x ∈ T.vertices) {i : ℕ} (hi : i ≤ dep T x) :
    an T x i ∈ treeLayer T i := by
  rw [mem_layer]; exact ⟨an_mem T hx i, dep_an T hx hi⟩

end Tree


section Select
variable {n : ℕ} {G : SimpleGraph (Fin n)} (T : RootedTreeIn G)

lemma select_aux (h b : ℕ) (hb : 1 ≤ b) (S : Finset (Fin n)) (hS : S ⊆ treeLayer T h) :
    ∀ s i (y : Fin n), i + s = h → y ∈ treeLayer T i →
      (b-1)*(h-i) + 2 ≤ (S.filter (fun v => an T v i = y)).card →
      S.card ≤ (S.filter (fun v => an T v i = y)).card + (b-1)*i →
      ∃ p : ℕ × Fin n, p.1 < h ∧ p.2 ∈ treeLayer T p.1 ∧
        S.card ≤ (S.filter (fun v => an T v p.1 = p.2)).card + (b-1)*p.1 ∧
        ∀ a, b ≤ (S.filter (fun v => an T v p.1 = p.2 ∧ an T v (p.1+1) ≠ a)).card := by
  intro s
  induction s with
  | zero =>
    intro i y hi hy hc _
    exfalso
    have : (S.filter (fun v => an T v i = y)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro v1 h1 v2 h2
      simp only [Finset.mem_filter] at h1 h2
      have hv1 := (mem_layer T v1 h).mp (hS h1.1)
      have hv2 := (mem_layer T v2 h).mp (hS h2.1)
      have e1 : an T v1 i = v1 := by rw [show i = dep T v1 by omega]; exact an_self T hv1.1
      have e2 : an T v2 i = v2 := by rw [show i = dep T v2 by omega]; exact an_self T hv2.1
      rw [← e1, ← e2, h1.2, h2.2]
    omega
  | succ s ih =>
    intro i y hi hy hc hS'
    by_cases hall : ∀ a, b ≤ (S.filter (fun v => an T v i = y ∧ an T v (i+1) ≠ a)).card
    · exact ⟨(i, y), by simp only; omega, hy, hS', hall⟩
    · push Not at hall
      obtain ⟨a, ha⟩ := hall
      have hsplit : (S.filter (fun v => an T v i = y)).card =
          (S.filter (fun v => an T v i = y ∧ an T v (i+1) = a)).card +
          (S.filter (fun v => an T v i = y ∧ an T v (i+1) ≠ a)).card := by
        rw [← Finset.filter_filter, ← Finset.filter_filter]
        exact (Finset.card_filter_add_card_filter_not _).symm
      have hsub : (S.filter (fun v => an T v i = y ∧ an T v (i+1) = a)).card ≤
          (S.filter (fun v => an T v (i+1) = a)).card := by
        apply Finset.card_le_card
        intro v; simp only [Finset.mem_filter]; tauto
      have hhi : h - i = (h - (i+1)) + 1 := by omega
      rw [hhi, Nat.mul_succ] at hc
      have hgoal2 : S.card ≤ (S.filter (fun v => an T v (i+1) = a)).card + (b-1)*(i+1) := by
        rw [Nat.mul_succ]
        omega
      have hpos : 0 < (S.filter (fun v => an T v (i+1) = a)).card := by omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter] at hv
      have hvL := (mem_layer T v h).mp (hS hv.1)
      have ha_mem : a ∈ treeLayer T (i+1) := by
        rw [← hv.2]; exact an_mem_layer T hvL.1 (by omega)
      apply ih (i+1) a (by omega) ha_mem
      · omega
      · exact hgoal2

lemma select (h b : ℕ) (hh : 0 < h) (hb : 1 ≤ b) (S : Finset (Fin n)) (hS : S ⊆ treeLayer T h)
    (hcard : b*h + 1 ≤ S.card) :
    ∃ p : ℕ × Fin n, p.1 < h ∧ p.2 ∈ treeLayer T p.1 ∧
      S.card ≤ (S.filter (fun v => an T v p.1 = p.2)).card + b*h ∧
      ∀ a, b ≤ (S.filter (fun v => an T v p.1 = p.2 ∧ an T v (p.1+1) ≠ a)).card := by
  have hne : 0 < S.card := by omega
  obtain ⟨v0, hv0⟩ := Finset.card_pos.mp hne
  have hv0L := (mem_layer T v0 h).mp (hS hv0)
  have hfil : S.filter (fun v => an T v 0 = an T v0 0) = S := by
    apply Finset.filter_true_of_mem
    intro v hv
    exact an_zero_eq T ((mem_layer T v h).mp (hS hv)).1 hv0L.1
  have hroot : an T v0 0 ∈ treeLayer T 0 := an_mem_layer T hv0L.1 (Nat.zero_le _)
  have h1 : (b-1)*(h-0) + 2 ≤ (S.filter (fun v => an T v 0 = an T v0 0)).card := by
    rw [hfil, Nat.sub_zero]
    have : b * h = (b-1)*h + h := by
      conv_lhs => rw [show b = (b-1) + 1 by omega]
      ring
    omega
  have h2 : S.card ≤ (S.filter (fun v => an T v 0 = an T v0 0)).card + (b-1)*0 := by
    rw [hfil]; omega
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := select_aux T h b hb S hS h 0 (an T v0 0) (by omega) hroot h1 h2
  refine ⟨p, hp1, hp2, ?_, hp4⟩
  have : (b-1) * p.1 ≤ b * h := Nat.mul_le_mul (by omega) (by omega)
  omega

end Select

section Bip
variable {n : ℕ}

noncomputable def ec (adj : Fin n → Fin n → Prop) (X Y : Finset (Fin n)) : ℕ :=
  ∑ y ∈ Y, (X.filter (fun x => adj x y)).card

lemma ec_comm (adj : Fin n → Fin n → Prop) (X Y : Finset (Fin n)) :
    ec adj X Y = ∑ x ∈ X, (Y.filter (fun y => adj x y)).card := by
  unfold ec
  simp only [Finset.card_filter]
  exact Finset.sum_comm

lemma ec_eq_card (adj : Fin n → Fin n → Prop) (X Y : Finset (Fin n)) :
    ec adj X Y = ((X ×ˢ Y).filter (fun q => adj q.1 q.2)).card := by
  rw [ec_comm, Finset.card_filter, Finset.sum_product]
  simp only [Finset.card_filter]

lemma prune_aux (adj : Fin n → Fin n → Prop) (L R : Finset (Fin n)) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    ∀ N, ∀ X Y : Finset (Fin n), X ⊆ L → Y ⊆ R → X.card + Y.card = N →
      (ec adj L R : ℝ) - a * (L.card - X.card) - b * (R.card - Y.card) ≤ ec adj X Y →
      ∃ X' ⊆ L, ∃ Y' ⊆ R, (ec adj L R : ℝ) - a * L.card - b * R.card ≤ ec adj X' Y' ∧
        (∀ x ∈ X', a ≤ (Y'.filter (fun y => adj x y)).card) ∧
        (∀ y ∈ Y', b ≤ (X'.filter (fun x => adj x y)).card) := by
  intro N
  induction N with
  | zero =>
    intro X Y hX hY hN hE
    have hX0 : X = ∅ := Finset.card_eq_zero.mp (by omega)
    have hY0 : Y = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hX0 hY0
    refine ⟨∅, hX, ∅, hY, ?_, by simp, by simp⟩
    simpa using hE
  | succ N ih =>
    intro X Y hX hY hN hE
    by_cases hbx : ∃ x ∈ X, ((Y.filter (fun y => adj x y)).card : ℝ) < a
    · obtain ⟨x, hx, hxa⟩ := hbx
      have hc := Finset.card_erase_add_one hx
      apply ih (X.erase x) Y ((Finset.erase_subset x X).trans hX) hY (by omega)
      have hsum : ec adj X Y = (Y.filter (fun y => adj x y)).card + ec adj (X.erase x) Y := by
        rw [ec_comm, ec_comm]; exact (Finset.add_sum_erase _ _ hx).symm
      have hcR : ((X.erase x).card : ℝ) = X.card - 1 := by
        rw [← hc]; push_cast; ring
      rw [hcR]
      have : (ec adj X Y : ℝ) = (Y.filter (fun y => adj x y)).card + ec adj (X.erase x) Y := by
        exact_mod_cast hsum
      nlinarith
    · by_cases hby : ∃ y ∈ Y, ((X.filter (fun x => adj x y)).card : ℝ) < b
      · obtain ⟨y, hy, hyb⟩ := hby
        have hc := Finset.card_erase_add_one hy
        apply ih X (Y.erase y) hX ((Finset.erase_subset y Y).trans hY) (by omega)
        have hsum : ec adj X Y = (X.filter (fun x => adj x y)).card + ec adj X (Y.erase y) := by
          unfold ec; exact (Finset.add_sum_erase _ _ hy).symm
        have hcR : ((Y.erase y).card : ℝ) = Y.card - 1 := by
          rw [← hc]; push_cast; ring
        rw [hcR]
        have : (ec adj X Y : ℝ) = (X.filter (fun x => adj x y)).card + ec adj X (Y.erase y) := by
          exact_mod_cast hsum
        nlinarith
      · push Not at hbx hby
        refine ⟨X, hX, Y, hY, ?_, hbx, hby⟩
        have h1 : (0 : ℝ) ≤ a * X.card := by positivity
        have h2 : (0 : ℝ) ≤ b * Y.card := by positivity
        nlinarith

lemma prune (adj : Fin n → Fin n → Prop) (L R : Finset (Fin n)) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    ∃ X' ⊆ L, ∃ Y' ⊆ R, (ec adj L R : ℝ) - a * L.card - b * R.card ≤ ec adj X' Y' ∧
      (∀ x ∈ X', a ≤ (Y'.filter (fun y => adj x y)).card) ∧
      (∀ y ∈ Y', b ≤ (X'.filter (fun x => adj x y)).card) :=
  prune_aux adj L R a b ha hb _ L R subset_rfl subset_rfl rfl (by simp)

/-- valid sequences of `p` pairs `(x_i, y_i)` forming the path `x_0 y_0 x_1 y_1 ...` -/
def Valid (adj : Fin n → Fin n → Prop) (X Y : Finset (Fin n)) (p : ℕ)
    (s : Fin p → Fin n × Fin n) : Prop :=
  (∀ i (hi : i < p), (s ⟨i, hi⟩).1 ∈ X ∧ (s ⟨i, hi⟩).2 ∈ Y ∧ adj (s ⟨i, hi⟩).1 (s ⟨i, hi⟩).2) ∧
  (∀ i (hi : i + 1 < p), adj (s ⟨i+1, hi⟩).1 (s ⟨i, by omega⟩).2) ∧
  (∀ i i' (hi : i < p) (hi' : i' < p), (s ⟨i, hi⟩).1 = (s ⟨i', hi'⟩).1 → i = i') ∧
  (∀ i i' (hi : i < p) (hi' : i' < p), (s ⟨i, hi⟩).2 = (s ⟨i', hi'⟩).2 → i = i')

noncomputable def Qs (adj : Fin n → Fin n → Prop) (X Y : Finset (Fin n)) (p : ℕ) :
    Finset (Fin p → Fin n × Fin n) :=
  Finset.univ.filter (Valid adj X Y p)

lemma Qs_one (adj : Fin n → Fin n → Prop) (X Y : Finset (Fin n)) :
    ec adj X Y ≤ (Qs adj X Y 1).card := by
  rw [ec_eq_card]
  apply Finset.card_le_card_of_injOn (fun q => fun _ : Fin 1 => q)
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hq
    simp only [Qs, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨fun i hi => ⟨hq.1.1, hq.1.2, hq.2⟩, fun i hi => by omega,
      fun i i' hi hi' _ => by omega, fun i i' hi hi' _ => by omega⟩
  · intro q _ q' _ h
    exact congrFun h 0

noncomputable def ext' {p : ℕ} (s : Fin p → Fin n × Fin n) (v : Fin n × Fin n) :
    Fin (p+1) → Fin n × Fin n :=
  fun i => if h : i.1 < p then s ⟨i.1, h⟩ else v

lemma ext'_lt {p : ℕ} (s : Fin p → Fin n × Fin n) (v : Fin n × Fin n) (i : ℕ) (hi : i < p) :
    ext' s v ⟨i, by omega⟩ = s ⟨i, hi⟩ := by
  simp [ext', hi]

lemma ext'_last {p : ℕ} (s : Fin p → Fin n × Fin n) (v : Fin n × Fin n) :
    ext' s v ⟨p, by omega⟩ = v := by
  simp [ext']

lemma Qs_step (adj : Fin n → Fin n → Prop) (X Y : Finset (Fin n)) (p DX DY : ℕ)
    (hX : ∀ x ∈ X, DX ≤ (Y.filter (fun y => adj x y)).card)
    (hY : ∀ y ∈ Y, DY ≤ (X.filter (fun x => adj x y)).card) :
    (Qs adj X Y (p+1)).card * ((DY - (p+1)) * (DX - (p+1))) ≤ (Qs adj X Y (p+2)).card := by
  rw [mul_comm]
  apply Finset.mul_card_image_le_card_of_maps_to
    (f := fun t : Fin (p+2) → Fin n × Fin n => fun i : Fin (p+1) => t ⟨i.1, by omega⟩)
  · intro t ht
    simp only [Qs, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    obtain ⟨h1, h2, h3, h4⟩ := ht
    exact ⟨fun i hi => h1 i (by omega), fun i hi => h2 i (by omega),
      fun i i' hi hi' => h3 i i' (by omega) (by omega),
      fun i i' hi hi' => h4 i i' (by omega) (by omega)⟩
  · intro b hb
    simp only [Qs, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨b1, b2, b3, b4⟩ := hb
    set candX := (X.filter (fun x => adj x (b ⟨p, by omega⟩).2)) \
      (Finset.univ.image (fun i => (b i).1)) with hcandX
    set candY := fun x => (Y.filter (fun y => adj x y)) \
      (Finset.univ.image (fun i => (b i).2)) with hcandY
    have himX : (Finset.univ.image (fun i => (b i).1)).card ≤ p + 1 := by
      refine (Finset.card_image_le).trans ?_
      simp
    have himY : (Finset.univ.image (fun i => (b i).2)).card ≤ p + 1 := by
      refine (Finset.card_image_le).trans ?_
      simp
    have hcX : DY - (p+1) ≤ candX.card := by
      have h1 := hY _ (b1 p (by omega)).2.1
      have h2 := Finset.le_card_sdiff (Finset.univ.image (fun i => (b i).1))
        (X.filter (fun x => adj x (b ⟨p, by omega⟩).2))
      rw [hcandX]
      omega
    have hcY : ∀ x ∈ candX, DX - (p+1) ≤ (candY x).card := by
      intro x hx
      have hxX : x ∈ X := by
        rw [hcandX, Finset.mem_sdiff, Finset.mem_filter] at hx; exact hx.1.1
      have h1 := hX _ hxX
      have h2 := Finset.le_card_sdiff (Finset.univ.image (fun i => (b i).2))
        (Y.filter (fun y => adj x y))
      simp only [hcandY]
      omega
    have hsig : (DY - (p+1)) * (DX - (p+1)) ≤ (candX.sigma candY).card := by
      rw [Finset.card_sigma]
      calc (DY - (p+1)) * (DX - (p+1)) ≤ candX.card * (DX - (p+1)) :=
            Nat.mul_le_mul_right _ hcX
        _ = ∑ _x ∈ candX, (DX - (p+1)) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ candX, (candY x).card := Finset.sum_le_sum hcY
    refine hsig.trans ?_
    apply Finset.card_le_card_of_injOn (fun xy => ext' b (xy.1, xy.2))
    · intro xy hxy
      simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hxy
      obtain ⟨hx, hy⟩ := hxy
      rw [hcandX, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_image] at hx
      simp only [hcandY, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_image] at hy
      push Not at hx hy
      rw [Finset.mem_coe]
      simp only [Qs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro i hi
        by_cases hip : i < p + 1
        · rw [ext'_lt b _ i hip]; exact b1 i hip
        · have : i = p + 1 := by omega
          subst this
          rw [ext'_last]; exact ⟨hx.1.1, hy.1.1, hy.1.2⟩
      · intro i hi
        by_cases hip : i + 1 < p + 1
        · rw [ext'_lt b _ (i+1) hip, ext'_lt b _ i (by omega)]; exact b2 i hip
        · have : i = p := by omega
          subst this
          rw [ext'_last, ext'_lt b _ i (by omega)]; exact hx.1.2
      · intro i i' hi hi' heq
        by_cases hip : i < p + 1 <;> by_cases hip' : i' < p + 1
        · rw [ext'_lt b _ i hip, ext'_lt b _ i' hip'] at heq; exact b3 i i' hip hip' heq
        · have : i' = p + 1 := by omega
          subst this
          rw [ext'_lt b _ i hip, ext'_last] at heq
          exact (hx.2 ⟨i, hip⟩ (Finset.mem_univ _) heq).elim
        · have : i = p + 1 := by omega
          subst this
          rw [ext'_lt b _ i' hip', ext'_last] at heq
          exact (hx.2 ⟨i', hip'⟩ (Finset.mem_univ _) heq.symm).elim
        · omega
      · intro i i' hi hi' heq
        by_cases hip : i < p + 1 <;> by_cases hip' : i' < p + 1
        · rw [ext'_lt b _ i hip, ext'_lt b _ i' hip'] at heq; exact b4 i i' hip hip' heq
        · have : i' = p + 1 := by omega
          subst this
          rw [ext'_lt b _ i hip, ext'_last] at heq
          exact (hy.2 ⟨i, hip⟩ (Finset.mem_univ _) heq).elim
        · have : i = p + 1 := by omega
          subst this
          rw [ext'_lt b _ i' hip', ext'_last] at heq
          exact (hy.2 ⟨i', hip'⟩ (Finset.mem_univ _) heq.symm).elim
        · omega
      · funext i
        exact ext'_lt b _ i.1 i.2
    · intro xy _ xy' _ heq
      have := congrFun heq ⟨p+1, by omega⟩
      simp only [ext'_last] at this
      obtain ⟨x, y⟩ := xy
      obtain ⟨x', y'⟩ := xy'
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rfl

lemma Qs_iter (adj : Fin n → Fin n → Prop) (X Y : Finset (Fin n)) (DX DY M : ℕ)
    (hX : ∀ x ∈ X, DX ≤ (Y.filter (fun y => adj x y)).card)
    (hY : ∀ y ∈ Y, DY ≤ (X.filter (fun x => adj x y)).card) :
    ∀ q ≤ M, (Qs adj X Y 1).card * ((DY - M) * (DX - M)) ^ q ≤ (Qs adj X Y (q+1)).card := by
  intro q
  induction q with
  | zero => intro _; simp
  | succ q ih =>
    intro hq
    have h1 := ih (by omega)
    have h2 := Qs_step adj X Y q DX DY hX hY
    have h3 : (DY - M) * (DX - M) ≤ (DY - (q+1)) * (DX - (q+1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    calc (Qs adj X Y 1).card * ((DY - M) * (DX - M)) ^ (q+1)
        = (Qs adj X Y 1).card * ((DY - M) * (DX - M)) ^ q * ((DY - M) * (DX - M)) := by ring
      _ ≤ (Qs adj X Y (q+1)).card * ((DY - (q+1)) * (DX - (q+1))) := Nat.mul_le_mul h1 h3
      _ ≤ _ := h2

end Bip

section CycleBuild
variable {n : ℕ} {G : SimpleGraph (Fin n)} (T : RootedTreeIn G)

lemma mem_cycleCopies_of_walk (k : ℕ) {v : Fin n} (c : G.Walk v v) (hc : c.IsCycle)
    (hl : c.length = 2 * k) : c.edges.toFinset ∈ cycleCopies G k := by
  unfold cycleCopies
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  refine ⟨?_, ⟨v, c, hc, ?_⟩⟩
  · rw [List.toFinset_card_of_nodup hc.edges_nodup, SimpleGraph.Walk.length_edges, hl]
  · ext e; simp

lemma cycle_build (h k j m : ℕ) (hjh : j < h) (hmk : m + (h - j) = k) (hm1 : 1 ≤ m)
    (R : Finset (Fin n)) (hR : Disjoint R T.vertices)
    (x y : ℕ → Fin n) (hx : ∀ i < m, x i ∈ treeLayer T h) (hy : ∀ i < m, y i ∈ R)
    (hxinj : ∀ i < m, ∀ i' < m, x i = x i' → i = i')
    (hyinj : ∀ i < m, ∀ i' < m, y i = y i' → i = i')
    (hadj1 : ∀ i < m, G.Adj (x i) (y i)) (hadj2 : ∀ i, i + 1 < m → G.Adj (x (i+1)) (y i))
    (u : Fin n) (hu : u ∈ treeLayer T h) (huadj : G.Adj u (y (m-1)))
    (huz : an T u j = an T (x 0) j) (hua : an T u (j+1) ≠ an T (x 0) (j+1))
    (huex : ∀ i < m, 1 ≤ i → u ≠ x i) :
    ∃ E ∈ cycleCopies G k, (∃ v ∈ treeLayer T j, ∃ e ∈ E, v ∈ e) ∧
      (∀ i < m, s(x i, y i) ∈ E) ∧ (∀ i, i + 1 < m → s(x (i+1), y i) ∈ E) := by
  set D := h - j with hD
  have hD1 : 1 ≤ D := by omega
  have hxT : ∀ i < m, x i ∈ T.vertices ∧ dep T (x i) = h := fun i hi => (mem_layer T _ h).mp (hx i hi)
  have huT : u ∈ T.vertices ∧ dep T u = h := (mem_layer T _ h).mp hu
  have hx0 := hxT 0 (by omega)
  have hyT : ∀ i < m, y i ∉ T.vertices := fun i hi => Finset.disjoint_left.mp hR (hy i hi)
  have hdu : ∀ d ≤ h, dep T (an T u d) = d := fun d hd => dep_an T huT.1 (by omega)
  have hdx : ∀ d ≤ h, dep T (an T (x 0) d) = d := fun d hd => dep_an T hx0.1 (by omega)
  have hmu : ∀ d, an T u d ∈ T.vertices := fun d => an_mem T huT.1 d
  have hmx : ∀ d, an T (x 0) d ∈ T.vertices := fun d => an_mem T hx0.1 d
  have hu_self : an T u h = u := by rw [← huT.2]; exact an_self T huT.1
  have hx_self : an T (x 0) h = x 0 := by rw [← hx0.2]; exact an_self T hx0.1
  set N := 2 * m + 2 * D with hN
  set g : ℕ → Fin n := fun i => if i < 2 * m then (if i % 2 = 0 then x (i / 2) else y (i / 2))
    else if i ≤ 2 * m + D then an T u (h - (i - 2 * m)) else an T (x 0) (j + (i - 2 * m - D))
    with hg
  have F1 : ∀ i, i < 2 * m → i % 2 = 0 → g i = x (i / 2) := by
    intro i h1 h2; simp only [hg, if_pos h1, if_pos h2]
  have F2 : ∀ i, i < 2 * m → i % 2 = 1 → g i = y (i / 2) := by
    intro i h1 h2; simp only [hg, if_pos h1, if_neg (show ¬ i % 2 = 0 by omega)]
  have F3 : ∀ i, 2 * m ≤ i → i ≤ 2 * m + D → g i = an T u (h - (i - 2 * m)) := by
    intro i h1 h2; simp only [hg, if_neg (show ¬ i < 2 * m by omega), if_pos h2]
  have F4 : ∀ i, 2 * m + D < i → g i = an T (x 0) (j + (i - 2 * m - D)) := by
    intro i h1; simp only [hg, if_neg (show ¬ i < 2 * m by omega),
      if_neg (show ¬ i ≤ 2 * m + D by omega)]
  have F4' : ∀ i, 2 * m + D ≤ i → g i = an T (x 0) (j + (i - 2 * m - D)) := by
    intro i h1
    rcases Nat.lt_or_ge (2 * m + D) i with h2 | h2
    · exact F4 i h2
    · have : i = 2 * m + D := by omega
      subst this
      rw [F3 _ (by omega) le_rfl, show h - (2 * m + D - 2 * m) = j by omega,
        show j + (2 * m + D - 2 * m - D) = j by omega, huz]
  -- adjacency
  have hadj : ∀ i < N, G.Adj (g i) (g (i+1)) := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) (2 * m) with h1 | h1
    · rcases Nat.mod_two_eq_zero_or_one i with h2 | h2
      · rw [F1 i (by omega) h2, F2 (i+1) h1 (by omega), show (i+1)/2 = i/2 by omega]
        exact hadj1 _ (by omega)
      · rw [F2 i (by omega) h2, F1 (i+1) h1 (by omega), show (i+1)/2 = i/2 + 1 by omega]
        exact (hadj2 _ (by omega)).symm
    · rcases Nat.lt_or_ge i (2 * m) with h2 | h2
      · have hi1 : i = 2 * m - 1 := by omega
        rw [F2 i h2 (by omega), F3 (i+1) (by omega) (by omega), show i / 2 = m - 1 by omega,
          show h - (i + 1 - 2 * m) = h by omega, hu_self]
        exact huadj.symm
      · rcases Nat.lt_or_ge i (2 * m + D) with h3 | h3
        · rw [F3 i h2 (by omega), F3 (i+1) (by omega) (by omega)]
          have e1 : h - (i - 2 * m) = (h - (i + 1 - 2 * m)) + 1 := by omega
          rw [e1]
          exact adj_an T huT.1 (by omega)
        · rw [F4' i h3, F4 (i+1) (by omega), show j + (i + 1 - 2 * m - D) =
            (j + (i - 2 * m - D)) + 1 by omega]
          exact (adj_an T hx0.1 (by omega)).symm
  have hwrap : g N = g 0 := by
    rw [F4 N (by omega), F1 0 (by omega) rfl, show j + (N - 2 * m - D) = h by omega, hx_self]
  -- injectivity
  have hreg : ∀ i < N, (i < 2 * m ∧ i % 2 = 0 ∧ g i = x (i / 2)) ∨
      (i < 2 * m ∧ i % 2 = 1 ∧ g i = y (i / 2)) ∨
      (2 * m ≤ i ∧ i ≤ 2 * m + D ∧ g i = an T u (h - (i - 2 * m))) ∨
      (2 * m + D < i ∧ g i = an T (x 0) (j + (i - 2 * m - D))) := by
    intro i hi
    rcases Nat.lt_or_ge i (2 * m) with h1 | h1
    · rcases Nat.mod_two_eq_zero_or_one i with h2 | h2
      · exact Or.inl ⟨h1, h2, F1 i h1 h2⟩
      · exact Or.inr (Or.inl ⟨h1, h2, F2 i h1 h2⟩)
    · rcases Nat.lt_or_ge (2 * m + D) i with h3 | h3
      · exact Or.inr (Or.inr (Or.inr ⟨h3, F4 i h3⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h3, F3 i h1 h3⟩))
  have key : ∀ i < N, ∀ i' < N, i ≤ i' → g i = g i' → i = i' := by
    intro i hi i' hi' hle heq
    rcases hreg i hi with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a3⟩ <;>
    rcases hreg i' hi' with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b3⟩ <;>
    rw [a3, b3] at heq
    -- (1,1)
    · have := hxinj _ (by omega) _ (by omega) heq; omega
    -- (1,2)
    · exact absurd (heq ▸ (hxT _ (by omega)).1) (hyT _ (by omega))
    -- (1,3)
    · have hd := congrArg (dep T) heq
      rw [(hxT _ (by omega)).2, hdu _ (by omega)] at hd
      have hi'2 : i' = 2 * m := by omega
      subst hi'2
      rw [show h - (2 * m - 2 * m) = h by omega, hu_self] at heq
      by_cases h0 : i / 2 = 0
      · rw [h0] at heq
        exact absurd (by rw [heq]) hua
      · exact absurd heq.symm (huex _ (by omega) (by omega))
    -- (1,4)
    · have hd := congrArg (dep T) heq
      rw [(hxT _ (by omega)).2, hdx _ (by omega)] at hd
      omega
    -- (2,1)
    · exact absurd (heq ▸ (hxT _ (by omega)).1) (hyT _ (by omega))
    -- (2,2)
    · have := hyinj _ (by omega) _ (by omega) heq; omega
    -- (2,3)
    · exact absurd (heq ▸ hmu _) (hyT _ (by omega))
    -- (2,4)
    · exact absurd (heq ▸ hmx _) (hyT _ (by omega))
    -- (3,1)
    · omega
    -- (3,2)
    · omega
    -- (3,3)
    · have hd := congrArg (dep T) heq
      rw [hdu _ (by omega), hdu _ (by omega)] at hd
      omega
    -- (3,4)
    · have hd := congrArg (dep T) heq
      rw [hdu _ (by omega), hdx _ (by omega)] at hd
      set d := j + (i' - 2 * m - D) with hd'
      have hdj : j + 1 ≤ d := by omega
      have hdh : d ≤ h := by omega
      rw [show h - (i - 2 * m) = d by omega] at heq
      have e1 := an_an T huT.1 hdj (by omega : d ≤ dep T u)
      have e2 := an_an T hx0.1 hdj (by omega : d ≤ dep T (x 0))
      rw [heq, e2] at e1
      exact absurd e1.symm hua
    -- (4,1)
    · omega
    -- (4,2)
    · omega
    -- (4,3)
    · omega
    -- (4,4)
    · have hd := congrArg (dep T) heq
      rw [hdx _ (by omega), hdx _ (by omega)] at hd
      omega
  have hinj : ∀ i < N, ∀ i' < N, g i = g i' → i = i' := by
    intro i hi i' hi' heq
    rcases le_total i i' with hle | hle
    · exact key i hi i' hi' hle heq
    · exact (key i' hi' i hi hle heq.symm).symm
  obtain ⟨v, c, hc, hcl, hce⟩ := cycle_of_fun g N (by omega) hinj hadj hwrap
  refine ⟨c.edges.toFinset, mem_cycleCopies_of_walk k c hc (by omega), ?_, ?_, ?_⟩
  · refine ⟨g (2 * m + D), ?_, s(g (2 * m + D), g (2 * m + D + 1)), ?_, Sym2.mem_mk_left _ _⟩
    · rw [F3 _ (by omega) le_rfl, show h - (2 * m + D - 2 * m) = j by omega]
      exact an_mem_layer T huT.1 (by omega)
    · rw [List.mem_toFinset, hce]; exact ⟨_, by omega, rfl⟩
  · intro i hi
    rw [List.mem_toFinset, hce]
    refine ⟨2 * i, by omega, ?_⟩
    rw [F1 (2 * i) (by omega) (by omega), F2 (2 * i + 1) (by omega) (by omega),
      show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega]
  · intro i hi
    rw [List.mem_toFinset, hce]
    refine ⟨2 * i + 1, by omega, ?_⟩
    rw [F2 (2 * i + 1) (by omega) (by omega), F1 (2 * i + 1 + 1) (by omega) (by omega),
      show (2 * i + 1) / 2 = i by omega, show (2 * i + 1 + 1) / 2 = i + 1 by omega,
      Sym2.eq_swap]

end CycleBuild

section Fiber
variable {n : ℕ} {G : SimpleGraph (Fin n)}

lemma cycleCopies_spec {k : ℕ} {E : Finset (Sym2 (Fin n))} (hE : E ∈ cycleCopies G k) :
    E.card = 2 * k ∧ ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ ∀ e, e ∈ c.edges ↔ e ∈ E := by
  unfold cycleCopies at hE
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and] at hE
  obtain ⟨hcard, v, c, hc, hset⟩ := hE
  refine ⟨hcard, v, c, hc, fun e => ?_⟩
  have := congrArg (fun S : Set (Sym2 (Fin n)) => e ∈ S) hset
  simpa using this

lemma fiber_bound (k m : ℕ) (hm : 0 < m) (L R : Finset (Fin n)) (hLR : Disjoint L R)
    (A : Finset (Fin m → Fin n × Fin n)) (C : Finset (Finset (Sym2 (Fin n))))
    (hC : C ⊆ cycleCopies G k)
    (hA : ∀ s ∈ A, (∀ i (hi : i < m), (s ⟨i, hi⟩).1 ∈ L ∧ (s ⟨i, hi⟩).2 ∈ R) ∧
      (∀ i i' (hi : i < m) (hi' : i' < m), (s ⟨i, hi⟩).1 = (s ⟨i', hi'⟩).1 → i = i') ∧
      (∀ i i' (hi : i < m) (hi' : i' < m), (s ⟨i, hi⟩).2 = (s ⟨i', hi'⟩).2 → i = i'))
    (Φ : (Fin m → Fin n × Fin n) → Finset (Sym2 (Fin n)))
    (hΦC : ∀ s ∈ A, Φ s ∈ C)
    (hΦ1 : ∀ s ∈ A, ∀ i (hi : i < m), s((s ⟨i, hi⟩).1, (s ⟨i, hi⟩).2) ∈ Φ s)
    (hΦ2 : ∀ s ∈ A, ∀ i (hi : i + 1 < m), s((s ⟨i+1, hi⟩).1, (s ⟨i, by omega⟩).2) ∈ Φ s) :
    A.card ≤ (2 * k) * C.card := by
  have key : ∀ E ∈ A.image Φ, (A.filter (fun s => Φ s = E)).card ≤ 2 * k := by
    intro E hE
    rw [Finset.mem_image] at hE
    obtain ⟨s0, hs0, hE⟩ := hE
    have hEC : E ∈ cycleCopies G k := hC (hE ▸ hΦC s0 hs0)
    obtain ⟨hEcard, v, c, hc, hce⟩ := cycleCopies_spec hEC
    rw [← hEcard]
    calc (A.filter (fun s => Φ s = E)).card
        ≤ ((L ×ˢ R).filter (fun q => s(q.1, q.2) ∈ E)).card := by
          apply Finset.card_le_card_of_injOn (fun s => s ⟨0, hm⟩)
          · intro s hs
            rw [Finset.mem_coe, Finset.mem_filter] at hs
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
            refine ⟨⟨((hA s hs.1).1 0 hm).1, ((hA s hs.1).1 0 hm).2⟩, ?_⟩
            rw [← hs.2]; exact hΦ1 s hs.1 0 hm
          · intro s hs s' hs' h0
            rw [Finset.mem_coe, Finset.mem_filter] at hs hs'
            obtain ⟨hA1, hA2, hA3⟩ := hA s hs.1
            obtain ⟨hA1', hA2', hA3'⟩ := hA s' hs'.1
            have claim : ∀ i (hi : i < m), s ⟨i, hi⟩ = s' ⟨i, hi⟩ := by
              intro i
              induction i with
              | zero => intro hi; exact h0
              | succ i ih =>
                intro hi
                have IH := ih (by omega)
                -- edges in c
                have ex1 : s((s ⟨i, by omega⟩).2, (s ⟨i, by omega⟩).1) ∈ c.edges := by
                  rw [hce, Sym2.eq_swap, ← hs.2]; exact hΦ1 s hs.1 i (by omega)
                have ex2 : s((s ⟨i, by omega⟩).2, (s ⟨i+1, hi⟩).1) ∈ c.edges := by
                  rw [hce, Sym2.eq_swap, ← hs.2]; exact hΦ2 s hs.1 i hi
                have ex3 : s((s ⟨i, by omega⟩).2, (s' ⟨i+1, hi⟩).1) ∈ c.edges := by
                  rw [hce, Sym2.eq_swap, ← hs'.2, IH]; exact hΦ2 s' hs'.1 i hi
                have hx : (s' ⟨i+1, hi⟩).1 = (s ⟨i+1, hi⟩).1 := by
                  apply cycle_deg_two hc ex1 ex2 ex3
                  · intro h; have := hA2 i (i+1) (by omega) hi h; omega
                  · intro h; rw [IH] at h; have := hA2' (i+1) i hi (by omega) h; omega
                have ey1 : s((s ⟨i+1, hi⟩).1, (s ⟨i, by omega⟩).2) ∈ c.edges := by
                  rw [hce, ← hs.2]; exact hΦ2 s hs.1 i hi
                have ey2 : s((s ⟨i+1, hi⟩).1, (s ⟨i+1, hi⟩).2) ∈ c.edges := by
                  rw [hce, ← hs.2]; exact hΦ1 s hs.1 (i+1) hi
                have ey3 : s((s ⟨i+1, hi⟩).1, (s' ⟨i+1, hi⟩).2) ∈ c.edges := by
                  rw [hce, ← hs'.2, ← hx]; exact hΦ1 s' hs'.1 (i+1) hi
                have hy : (s' ⟨i+1, hi⟩).2 = (s ⟨i+1, hi⟩).2 := by
                  apply cycle_deg_two hc ey1 ey2 ey3
                  · intro h; have := hA3 i (i+1) (by omega) hi h; omega
                  · intro h; rw [IH] at h; have := hA3' (i+1) i hi (by omega) h; omega
                exact Prod.ext hx.symm hy.symm
            funext ⟨i, hi⟩
            exact claim i hi
      _ ≤ E.card := by
          apply Finset.card_le_card_of_injOn (fun q => s(q.1, q.2))
          · intro q hq
            rw [Finset.mem_coe, Finset.mem_filter] at hq
            exact hq.2
          · intro q hq q' hq' heq
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq hq'
            simp only at heq
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨h1, h2⟩ | ⟨h1, _⟩
            · exact Prod.ext h1 h2
            · exfalso
              exact Finset.disjoint_left.mp hLR hq.1.1 (h1 ▸ hq'.1.2)
  have h1 := Finset.card_le_mul_card_image A (2 * k) key
  refine h1.trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
  intro E hE
  rw [Finset.mem_image] at hE
  obtain ⟨s, hs, rfl⟩ := hE
  exact hΦC s hs

end Fiber

lemma alpha_nonneg (k : ℕ) : 0 ≤ alpha k := by
  unfold alpha; positivity

lemma alpha_bound (k q : ℕ) (hk : 2 ≤ k) (hq : q ≤ k - 2) :
    alpha k * (8 * (k : ℝ) ^ 2) * (256 * (k : ℝ) ^ 2) ^ q ≤ 1 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hA : alpha k = 1 / ((2 : ℝ) ^ (6 * k) * (4 * (k : ℝ) ^ 2) ^ (k - 1)) := by
    unfold alpha
    rw [one_div_pow, one_div_mul_one_div, show 2 * k - 2 = 2 * (k - 1) by omega,
      pow_mul (2 * (k : ℝ)) 2 (k - 1),
      show (2 * (k : ℝ)) ^ 2 = 4 * (k : ℝ) ^ 2 by ring]
  have h64 : (64 : ℝ) ^ (q + 2) ≤ (2 : ℝ) ^ (6 * k) := by
    rw [pow_mul]; norm_num
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (4 * (k : ℝ) ^ 2) ^ (q + 1) ≤ (4 * (k : ℝ) ^ 2) ^ (k - 1) :=
    pow_le_pow_right₀ (by nlinarith) (by omega)
  have hpos : 0 < (2 : ℝ) ^ (6 * k) * (4 * (k : ℝ) ^ 2) ^ (k - 1) := by positivity
  rw [hA, div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, div_le_one hpos]
  have hprod : (64 : ℝ) ^ (q + 2) * (4 * (k : ℝ) ^ 2) ^ (q + 1) ≤
      (2 : ℝ) ^ (6 * k) * (4 * (k : ℝ) ^ 2) ^ (k - 1) :=
    mul_le_mul h64 h4 (by positivity) (by positivity)
  refine le_trans ?_ hprod
  have e1 : (64 : ℝ) ^ (q + 2) * (4 * (k : ℝ) ^ 2) ^ (q + 1) =
      16384 * (k : ℝ) ^ 2 * (256 * (k : ℝ) ^ 2) ^ q := by
    have e0 : (256 * (k : ℝ) ^ 2) ^ q = (64 : ℝ) ^ q * (4 * (k : ℝ) ^ 2) ^ q := by
      rw [← mul_pow]; congr 1; ring
    rw [e0]
    ring
  rw [e1]
  have : (0 : ℝ) ≤ (k : ℝ) ^ 2 * (256 * (k : ℝ) ^ 2) ^ q := by positivity
  nlinarith

lemma copiesMeeting_eq {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (S : Finset (Fin n)) :
    copiesMeeting G k S = ((cycleCopies G k).filter (fun E => ∃ v ∈ S, ∃ e ∈ E, v ∈ e)).card := by
  unfold copiesMeeting; congr

lemma crossEdges_eq {n : ℕ} (G : SimpleGraph (Fin n)) (L R : Finset (Fin n)) :
    crossEdges G L R = ec (fun l w => G.Adj l w) L R := by
  rw [ec_eq_card]; unfold crossEdges; congr

set_option maxHeartbeats 1000000 in
theorem main_thm (n h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k - 1)
    (G : SimpleGraph (Fin n)) (T : RootedTreeIn G) (_hdepth : treeDepth T h)
    (R : Finset (Fin n)) (hR : Disjoint R T.vertices)
    (hdL : 16 * (k : ℝ) ^ 2 ≤ averageLeft G (treeLayer T h) R)
    (hdR : 16 * (k : ℝ) ^ 2 ≤ averageRight G (treeLayer T h) R) :
    ∃ j : ℕ, j ≤ h ∧
      alpha k * (treeLayer T h).card * averageLeft G (treeLayer T h) R *
        (averageLeft G (treeLayer T h) R * averageRight G (treeLayer T h) R) ^
          (k - h + j - 1) ≤ (copiesMeeting G k (treeLayer T j) : ℝ) := by
  set L := treeLayer T h with hLdef
  set dL := averageLeft G L R with hdLdef
  set dR := averageRight G L R with hdRdef
  set EF := crossEdges G L R with hEFdef
  have hk2 : 2 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hhkR : (h : ℝ) ≤ k := by exact_mod_cast (show h ≤ k by omega)
  have hdL' : dL = (EF : ℝ) / L.card := rfl
  have hdR' : dR = (EF : ℝ) / R.card := rfl
  have hLpos : 0 < L.card := by
    rcases Nat.eq_zero_or_pos L.card with h0 | h0
    · exfalso
      rw [hdL', h0, Nat.cast_zero, div_zero] at hdL
      nlinarith
    · exact h0
  have hRpos : 0 < R.card := by
    rcases Nat.eq_zero_or_pos R.card with h0 | h0
    · exfalso
      rw [hdR', h0, Nat.cast_zero, div_zero] at hdR
      nlinarith
    · exact h0
  have hLposR : (0 : ℝ) < L.card := by exact_mod_cast hLpos
  have hRposR : (0 : ℝ) < R.card := by exact_mod_cast hRpos
  have hdLe : dL * L.card = EF := by rw [hdL']; field_simp
  have hdRe : dR * R.card = EF := by rw [hdR']; field_simp
  have hEFR : 16 * (k : ℝ) ^ 2 * R.card ≤ EF := by
    rw [← hdRe]; exact mul_le_mul_of_nonneg_right hdR hRposR.le
  have hLRdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro x hxL hxR
    exact Finset.disjoint_left.mp hR hxR ((mem_layer T x h).mp hxL).1
  -- neighbourhoods
  obtain ⟨S, hS⟩ : ∃ S : Fin n → Finset (Fin n), ∀ w, S w = L.filter (fun l => G.Adj l w) :=
    ⟨_, fun _ => rfl⟩
  have hEFsum : EF = ∑ w ∈ R, (S w).card := by
    rw [hEFdef, crossEdges_eq]; unfold ec
    apply Finset.sum_congr rfl; intro w _; rw [hS]
  -- selection (Lemma 4.1)
  have hsel0 : ∀ w : Fin n, ∃ p : ℕ × Fin n, p.1 < h ∧ (k * h + 1 ≤ (S w).card →
      p.2 ∈ treeLayer T p.1 ∧
      (S w).card ≤ ((S w).filter (fun v => an T v p.1 = p.2)).card + k * h ∧
      ∀ a, k ≤ ((S w).filter (fun v => an T v p.1 = p.2 ∧ an T v (p.1+1) ≠ a)).card) := by
    intro w
    by_cases hb : k * h + 1 ≤ (S w).card
    · obtain ⟨p, hp1, hp2, hp3, hp4⟩ := select T h k hh (by omega) (S w)
        (by rw [hS]; exact Finset.filter_subset _ _) hb
      exact ⟨p, hp1, fun _ => ⟨hp2, hp3, hp4⟩⟩
    · exact ⟨(0, w), hh, fun hb' => absurd hb' hb⟩
  choose sel hsel1 hsel2 using hsel0
  obtain ⟨good, hgood⟩ : ∃ good : ℕ → Fin n → Fin n → Prop, ∀ j l w, good j l w ↔
      (G.Adj l w ∧ k * h + 1 ≤ (S w).card ∧ (sel w).1 = j ∧ an T l j = (sel w).2) :=
    ⟨_, fun _ _ _ => Iff.rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : Fin n → ℕ, ∀ w, f w = if k * h + 1 ≤ (S w).card then
      ((S w).filter (fun l => an T l (sel w).1 = (sel w).2)).card else 0 := ⟨_, fun _ => rfl⟩
  have hfw : ∀ w, ((S w).card : ℝ) - k * h ≤ f w := by
    intro w
    rw [hf]
    split_ifs with hb
    · have h1 := (hsel2 w hb).2.1
      have h2 : ((S w).card : ℝ) ≤
          ((S w).filter (fun l => an T l (sel w).1 = (sel w).2)).card + k * h := by
        exact_mod_cast h1
      linarith
    · have h2 : ((S w).card : ℝ) ≤ k * h := by exact_mod_cast (show (S w).card ≤ k * h by omega)
      simp only [Nat.cast_zero]; linarith
  have hej_eq : ∀ j, ec (good j) L R = ∑ w ∈ R, (if (sel w).1 = j then f w else 0) := by
    intro j
    unfold ec
    apply Finset.sum_congr rfl
    intro w _
    rw [hf]
    by_cases hb : k * h + 1 ≤ (S w).card
    · by_cases hj : (sel w).1 = j
      · rw [if_pos hj, if_pos hb, hS]
        subst hj
        congr 1
        ext l
        simp only [Finset.mem_filter, hgood]
        tauto
      · rw [if_neg hj]
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro l _ hl
        exact hj ((hgood _ _ _).mp hl).2.2.1
    · rw [if_neg hb]
      split_ifs <;>
      · apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro l _ hl
        exact hb ((hgood _ _ _).mp hl).2.1
  have hsumj : ∑ j ∈ Finset.range h, ec (good j) L R = ∑ w ∈ R, f w := by
    simp_rw [hej_eq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (hsel1 w))]
  obtain ⟨j, hjmem, hjle⟩ : ∃ j ∈ Finset.range h, ∑ w ∈ R, f w ≤ h * ec (good j) L R := by
    apply Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr (by omega))
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum, hsumj]
  have hjh : j < h := Finset.mem_range.mp hjmem
  set ej := ec (good j) L R with hejdef
  have hEFej : (EF : ℝ) ≤ 2 * k * ej := by
    have h1 : (EF : ℝ) - k * h * R.card ≤ ∑ w ∈ R, (f w : ℝ) := by
      have := Finset.sum_le_sum (fun w (_ : w ∈ R) => hfw w)
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at this
      rw [hEFsum]; push_cast; linarith
    have h2 : (∑ w ∈ R, (f w : ℝ)) ≤ h * ej := by exact_mod_cast hjle
    have h3 : (k : ℝ) * h * R.card ≤ k * k * R.card := by gcongr
    have h4 : (0 : ℝ) ≤ ej := by positivity
    have h5 : (h : ℝ) * ej ≤ k * ej := mul_le_mul_of_nonneg_right hhkR h4
    have h6 : (0 : ℝ) ≤ EF := by positivity
    have h7 : (k : ℝ) * k * R.card = k ^ 2 * R.card := by ring
    linarith
  -- pruning (Lemma 4.2)
  obtain ⟨X, hXL, Y, hYR, he', hdegX, hdegY⟩ := prune (good j) L R ((ej : ℝ) / (4 * L.card))
    ((ej : ℝ) / (4 * R.card)) (by positivity) (by positivity)
  set e' := ec (good j) X Y with he'def
  have he'2 : (ej : ℝ) ≤ 2 * e' := by
    have a1 : (ej : ℝ) / (4 * L.card) * L.card = ej / 4 := by field_simp
    have a2 : (ej : ℝ) / (4 * R.card) * R.card = ej / 4 := by field_simp
    linarith
  set DX := ⌈(ej : ℝ) / (4 * L.card)⌉₊ with hDXdef
  set DY := ⌈(ej : ℝ) / (4 * R.card)⌉₊ with hDYdef
  have hX : ∀ x ∈ X, DX ≤ (Y.filter (fun y => good j x y)).card :=
    fun x hx => Nat.ceil_le.mpr (hdegX x hx)
  have hY : ∀ y ∈ Y, DY ≤ (X.filter (fun x => good j x y)).card :=
    fun y hy => Nat.ceil_le.mpr (hdegY y hy)
  -- path length parameter
  set m := k - h + j with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmk : m ≤ k - 1 := by omega
  -- path count (Lemma 4.3)
  have hQ := Qs_iter (good j) X Y DX DY (m - 1) hX hY (m - 1) le_rfl
  rw [Nat.sub_add_cancel hm1] at hQ
  have hQ1 := Qs_one (good j) X Y
  set c := (DY - (m - 1)) * (DX - (m - 1)) with hcdef
  have hQm : e' * c ^ (m - 1) ≤ (Qs (good j) X Y m).card :=
    le_trans (Nat.mul_le_mul_right _ hQ1) hQ
  -- degree bounds
  have hDXr : (ej : ℝ) ≤ DX * (4 * L.card) := by
    have := Nat.le_ceil ((ej : ℝ) / (4 * L.card))
    rw [div_le_iff₀ (by positivity)] at this; exact this
  have hDYr : (ej : ℝ) ≤ DY * (4 * R.card) := by
    have := Nat.le_ceil ((ej : ℝ) / (4 * R.card))
    rw [div_le_iff₀ (by positivity)] at this; exact this
  have hDX1 : dL ≤ 8 * k * DX := by
    have : dL * L.card ≤ (8 * k * DX) * L.card := by
      calc dL * L.card = EF := hdLe
        _ ≤ 2 * k * ej := hEFej
        _ ≤ 2 * k * (DX * (4 * L.card)) := by gcongr
        _ = (8 * k * DX) * L.card := by ring
    exact le_of_mul_le_mul_right this hLposR
  have hDY1 : dR ≤ 8 * k * DY := by
    have : dR * R.card ≤ (8 * k * DY) * R.card := by
      calc dR * R.card = EF := hdRe
        _ ≤ 2 * k * ej := hEFej
        _ ≤ 2 * k * (DY * (4 * R.card)) := by gcongr
        _ = (8 * k * DY) * R.card := by ring
    exact le_of_mul_le_mul_right this hRposR
  have hDX2 : (2 * k : ℝ) ≤ DX := by
    have : (8 * k) * (2 * k : ℝ) ≤ (8 * k) * DX := by
      calc (8 * k) * (2 * k : ℝ) = 16 * (k : ℝ) ^ 2 := by ring
        _ ≤ dL := hdL
        _ ≤ 8 * k * DX := hDX1
    exact le_of_mul_le_mul_left this (by positivity)
  have hDY2 : (2 * k : ℝ) ≤ DY := by
    have : (8 * k) * (2 * k : ℝ) ≤ (8 * k) * DY := by
      calc (8 * k) * (2 * k : ℝ) = 16 * (k : ℝ) ^ 2 := by ring
        _ ≤ dR := hdR
        _ ≤ 8 * k * DY := hDY1
    exact le_of_mul_le_mul_left this (by positivity)
  have hDXn : m - 1 ≤ DX := by
    have : 2 * k ≤ DX := by exact_mod_cast hDX2
    omega
  have hDYn : m - 1 ≤ DY := by
    have : 2 * k ≤ DY := by exact_mod_cast hDY2
    omega
  have hm1R : ((m - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (show m - 1 ≤ k by omega)
  have hDX3 : dL ≤ 16 * k * ((DX - (m - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hDXn]
    have : 0 ≤ (k : ℝ) * (DX - 2 * ((m - 1 : ℕ) : ℝ)) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hDY3 : dR ≤ 16 * k * ((DY - (m - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hDYn]
    have : 0 ≤ (k : ℝ) * (DY - 2 * ((m - 1 : ℕ) : ℝ)) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hk0 : (0 : ℝ) ≤ 16 * (k : ℝ) ^ 2 := by positivity
  have hdL0 : (0 : ℝ) ≤ dL := le_trans hk0 hdL
  have hdR0 : (0 : ℝ) ≤ dR := le_trans hk0 hdR
  have hcR : dL * dR ≤ 256 * (k : ℝ) ^ 2 * c := by
    have := mul_le_mul hDX3 hDY3 hdR0 (by positivity)
    refine this.trans (le_of_eq ?_)
    rw [hcdef]; push_cast; ring
  have hW : (dL * dR) ^ (m - 1) ≤ (256 * (k : ℝ) ^ 2) ^ (m - 1) * (c : ℝ) ^ (m - 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hcR (m - 1)
  -- cycles (Claim 4.5)
  set C := (cycleCopies G k).filter (fun E => ∃ v ∈ treeLayer T j, ∃ e ∈ E, v ∈ e) with hCdef
  obtain ⟨u0, -⟩ := Finset.card_pos.mp hLpos
  have hexists : ∀ s ∈ Qs (good j) X Y m, ∃ E, E ∈ C ∧
      (∀ i (hi : i < m), s((s ⟨i, hi⟩).1, (s ⟨i, hi⟩).2) ∈ E) ∧
      (∀ i (hi : i + 1 < m), s((s ⟨i+1, hi⟩).1, (s ⟨i, by omega⟩).2) ∈ E) := by
    intro s hs
    simp only [Qs, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨v1, v2, v3, v4⟩ := hs
    obtain ⟨x, hx⟩ : ∃ x : ℕ → Fin n, ∀ i (hi : i < m), x i = (s ⟨i, hi⟩).1 :=
      ⟨fun i => if hi : i < m then (s ⟨i, hi⟩).1 else u0, fun i hi => by simp [hi]⟩
    obtain ⟨y, hy⟩ : ∃ y : ℕ → Fin n, ∀ i (hi : i < m), y i = (s ⟨i, hi⟩).2 :=
      ⟨fun i => if hi : i < m then (s ⟨i, hi⟩).2 else u0, fun i hi => by simp [hi]⟩
    have hg1 : ∀ i (hi : i < m), good j (x i) (y i) := by
      intro i hi; rw [hx i hi, hy i hi]; exact (v1 i hi).2.2
    have hg2 : ∀ i (hi : i + 1 < m), good j (x (i+1)) (y i) := by
      intro i hi; rw [hx _ hi, hy i (by omega)]; exact v2 i hi
    have hchain : ∀ i (hi : i < m), an T (x i) j = an T (x 0) j := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        rw [← ih (by omega)]
        have a := (hgood _ _ _).mp (hg2 i hi)
        have b := (hgood _ _ _).mp (hg1 i (by omega))
        rw [a.2.2.2, b.2.2.2]
    obtain ⟨-, hbig, hsj, hsz⟩ := (hgood _ _ _).mp (hg1 (m-1) (by omega))
    have hz : (sel (y (m-1))).2 = an T (x 0) j := by rw [← hsz, hchain _ (by omega)]
    have hcand := (hsel2 (y (m-1)) hbig).2.2 (an T (x 0) (j+1))
    rw [hsj, hz] at hcand
    have hEx : ((Finset.Ico 1 m).image x).card < ((S (y (m-1))).filter (fun v =>
        an T v j = an T (x 0) j ∧ an T v (j+1) ≠ an T (x 0) (j+1))).card := by
      have := Finset.card_image_le (s := Finset.Ico 1 m) (f := x)
      rw [Nat.card_Ico] at this
      omega
    obtain ⟨u, huC, huE⟩ := Finset.exists_mem_notMem_of_card_lt_card hEx
    rw [Finset.mem_filter, hS, Finset.mem_filter] at huC
    have huex : ∀ i < m, 1 ≤ i → u ≠ x i := by
      intro i hi h1 heq
      apply huE
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_Ico.mpr ⟨h1, hi⟩, heq.symm⟩
    obtain ⟨E, hE, hmeet, hE1, hE2⟩ := cycle_build T h k j m hjh (by omega) hm1 R hR x y
      (fun i hi => hXL (by rw [hx i hi]; exact (v1 i hi).1))
      (fun i hi => hYR (by rw [hy i hi]; exact (v1 i hi).2.1))
      (fun i hi i' hi' heq => by rw [hx i hi, hx i' hi'] at heq; exact v3 i i' hi hi' heq)
      (fun i hi i' hi' heq => by rw [hy i hi, hy i' hi'] at heq; exact v4 i i' hi hi' heq)
      (fun i hi => ((hgood _ _ _).mp (hg1 i hi)).1)
      (fun i hi => ((hgood _ _ _).mp (hg2 i hi)).1)
      u huC.1.1 huC.1.2 huC.2.1 huC.2.2 huex
    refine ⟨E, Finset.mem_filter.mpr ⟨hE, hmeet⟩, ?_, ?_⟩
    · intro i hi
      have := hE1 i hi
      rwa [hx i hi, hy i hi] at this
    · intro i hi
      have := hE2 i hi
      rwa [hx _ hi, hy i (by omega)] at this
  choose! Φ hΦC hΦ1 hΦ2 using hexists
  have hfib := fiber_bound (G := G) k m (by omega) L R hLRdisj (Qs (good j) X Y m) C
    (Finset.filter_subset _ _)
    (by
      intro s hs
      simp only [Qs, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      obtain ⟨v1, _, v3, v4⟩ := hs
      exact ⟨fun i hi => ⟨hXL (v1 i hi).1, hYR (v1 i hi).2.1⟩, v3, v4⟩)
    Φ hΦC hΦ1 hΦ2
  have hCm : copiesMeeting G k (treeLayer T j) = C.card := copiesMeeting_eq G k _
  -- final computation
  refine ⟨j, hjh.le, ?_⟩
  rw [hCm]
  have hα := alpha_bound k (m - 1) hk2 (by omega)
  have hα0 := alpha_nonneg k
  have hQmR : (e' : ℝ) * (c : ℝ) ^ (m - 1) ≤ (Qs (good j) X Y m).card := by exact_mod_cast hQm
  have hfibR : ((Qs (good j) X Y m).card : ℝ) ≤ 2 * k * C.card := by exact_mod_cast hfib
  have hEF' : alpha k * (L.card : ℝ) * dL = alpha k * EF := by
    rw [mul_assoc, mul_comm (L.card : ℝ) dL, hdLe]
  rw [hEF']
  have hZ : (0 : ℝ) ≤ (256 * (k : ℝ) ^ 2) ^ (m - 1) := by positivity
  have hW0 : (0 : ℝ) ≤ (dL * dR) ^ (m - 1) := by positivity
  calc alpha k * (EF : ℝ) * (dL * dR) ^ (m - 1)
      ≤ alpha k * (2 * k * (2 * e')) * (dL * dR) ^ (m - 1) := by
        gcongr
        calc (EF : ℝ) ≤ 2 * k * ej := hEFej
          _ ≤ 2 * k * (2 * e') := by gcongr
    _ ≤ alpha k * (2 * k * (2 * e')) *
          ((256 * (k : ℝ) ^ 2) ^ (m - 1) * (c : ℝ) ^ (m - 1)) := by gcongr
    _ = (alpha k * (4 * k) * (256 * (k : ℝ) ^ 2) ^ (m - 1)) * (e' * (c : ℝ) ^ (m - 1)) := by
        ring
    _ ≤ (alpha k * (4 * k) * (256 * (k : ℝ) ^ 2) ^ (m - 1)) * (2 * k * C.card) := by
        exact mul_le_mul_of_nonneg_left (hQmR.trans hfibR) (by positivity)
    _ = (alpha k * (8 * (k : ℝ) ^ 2) * (256 * (k : ℝ) ^ 2) ^ (m - 1)) * C.card := by ring
    _ ≤ 1 * C.card := by gcongr
    _ = C.card := one_mul _
end L33Aux

theorem solution (n h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k - 1)
    (G : SimpleGraph (Fin n)) (T : RootedTreeIn G) (hdepth : treeDepth T h)
    (R : Finset (Fin n)) (hR : Disjoint R T.vertices)
    (hdL : 16 * (k : ℝ) ^ 2 ≤ averageLeft G (treeLayer T h) R)
    (hdR : 16 * (k : ℝ) ^ 2 ≤ averageRight G (treeLayer T h) R) :
    ∃ j : ℕ, j ≤ h ∧
      alpha k * (treeLayer T h).card * averageLeft G (treeLayer T h) R *
        (averageLeft G (treeLayer T h) R * averageRight G (treeLayer T h) R) ^
          (k - h + j - 1) ≤ (copiesMeeting G k (treeLayer T j) : ℝ) :=
  L33Aux.main_thm n h k hh hk hhk G T hdepth R hR hdL hdR
