-- Prove2me | solution 1 for ChenPairedDomination.Interval.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:23:45.762513+00:00
-- url     : https://prove2.me/submissions/0ebf78c0-97d6-4822-9717-38a3fcda41c0

import Definitions.Def_ChenPairedDomination_Interval_PrefixData

open ChenPairedDomination.Interval

namespace Lemma9Proof

private lemma obs5 {n : ℕ} (G : SimpleGraph (Fin n))
    (R : OrderedRepresentation G)
    (i j : Fin n) (hji : j < i) (hij : G.Adj i j) :
    ∀ k : Fin n, j < k → k ≤ i → G.Adj j k := by
  intro k hjk hki
  obtain ⟨x, hx_i, hx_j⟩ := (R.represents i j hji.ne').mp hij
  rw [R.represents j k hjk.ne]
  refine ⟨R.left k, ⟨R.ordered hjk.le, ?_⟩, ⟨le_rfl, R.nonempty k⟩⟩
  exact (R.ordered hki).trans (hx_i.1.trans hx_j.2)

private lemma exists_edge_across_cut {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ)
    {x y : Fin n} (p : G.Walk x y) (hx : x.val < m) (hy : m ≤ y.val) :
    ∃ u w : Fin n, u.val < m ∧ m ≤ w.val ∧ G.Adj u w := by
  induction p with
  | nil => omega
  | @cons a b c hab p' ih =>
    by_cases hb : b.val < m
    · exact ih hb hy
    · exact ⟨a, b, hx, by omega, hab⟩

private lemma exists_earlier_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    (R : OrderedRepresentation G) (hconn : G.Connected)
    (v : Fin n) (hv : 0 < v.val) :
    ∃ u : Fin n, u < v ∧ G.Adj u v := by
  let z0 : Fin n := ⟨0, by omega⟩
  obtain ⟨p⟩ := hconn z0 v
  obtain ⟨u, w, hu, hw, huw⟩ := exists_edge_across_cut G v.val p hv le_rfl
  have huv : u < v := hu
  have hvw : v ≤ w := hw
  have huw' : u < w := lt_of_lt_of_le huv hvw
  exact ⟨u, huv, obs5 G R w u huw' huw.symm v huv hvw⟩

private lemma exists_neighbor_in_prefix {n : ℕ} (G : SimpleGraph (Fin n))
    (R : OrderedRepresentation G) (hconn : G.Connected)
    (m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) (w : Fin n) (hw : w ∈ prefixVertices m) :
    ∃ z ∈ prefixVertices m, G.Adj w z := by
  simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  by_cases hw0 : 0 < w.val
  · obtain ⟨u, huw, hadj⟩ := exists_earlier_neighbor G R hconn w hw0
    refine ⟨u, ?_, hadj.symm⟩
    simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_trans huw hw
  · let v1 : Fin n := ⟨1, by omega⟩
    obtain ⟨u, huv1, hadj⟩ := exists_earlier_neighbor G R hconn v1 (by dsimp [v1]; omega)
    have huw : u = w := by
      ext
      change u.val < 1 at huv1
      omega
    subst huw
    refine ⟨v1, ?_, hadj⟩
    simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and, v1]
    omega

private lemma pairwise_lt_finRange (n : ℕ) : (List.finRange n).Pairwise (· < ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.pairwise_cons]
    refine ⟨fun x hx => ?_, ih.map Fin.succ (fun a b hab => Fin.succ_lt_succ_iff.mpr hab)⟩
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact Fin.succ_pos y

private lemma headD_filter_le_of_pairwise {n : ℕ} (P : Fin n → Bool) (d w : Fin n)
    (l : List (Fin n)) (hl : l.Pairwise (· < ·)) (hw : w ∈ l) (hPw : P w = true) :
    (l.filter P).headD d ≤ w := by
  induction l with
  | nil => simp at hw
  | cons a tl ih =>
    rw [List.pairwise_cons] at hl
    simp only [List.mem_cons] at hw
    rw [List.filter_cons]
    by_cases hPa : P a = true
    · simp only [hPa, ↓reduceIte, List.headD_cons]
      rcases hw with rfl | hwtl
      · exact le_rfl
      · exact (hl.1 w hwtl).le
    · simp only [hPa, Bool.false_eq_true, ↓reduceIte]
      rcases hw with rfl | hwtl
      · contradiction
      · exact ih hl.2 hwtl

private lemma firstNeighbor_spec {n : ℕ} (G : SimpleGraph (Fin n)) (i w : Fin n)
    (hwi : w < i) (hadj : G.Adj w i) :
    (firstNeighbor G i < i ∧ G.Adj (firstNeighbor G i) i) ∧ firstNeighbor G i ≤ w := by
  classical
  unfold firstNeighbor
  set P : Fin n → Bool := fun k => decide (k < i ∧ G.Adj k i)
  set L := (List.finRange n).filter P
  have hPw : P w = true := by simp [P, hwi, hadj]
  have hwL : w ∈ L := List.mem_filter.mpr ⟨List.mem_finRange w, hPw⟩
  have hle : L.headD i ≤ w :=
    headD_filter_le_of_pairwise P i w (List.finRange n) (pairwise_lt_finRange n) (List.mem_finRange w) hPw
  cases hL : L with
  | nil => simp [hL] at hwL
  | cons a tl =>
    have ha : a ∈ L := by simp [hL]
    simp only [L, P, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ha
    refine ⟨?_, hL ▸ hle⟩
    simpa [hL] using ha

private lemma firstNeighbor_lt_and_adj_of_ne {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n)
    (hne : firstNeighbor G i ≠ i) :
    firstNeighbor G i < i ∧ G.Adj (firstNeighbor G i) i := by
  classical
  unfold firstNeighbor at hne ⊢
  set L := (List.finRange n).filter (fun k => decide (k < i ∧ G.Adj k i))
  cases hL : L with
  | nil =>
    exfalso
    apply hne
    simp [hL]
  | cons a tl =>
    have ha : a ∈ L := by simp [hL]
    simp only [L, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ha
    simpa [hL] using ha

private lemma not_adj_of_lt_firstNeighbor {n : ℕ} (G : SimpleGraph (Fin n)) (i k : Fin n)
    (hFk : firstNeighbor G i = k) (hki : k < i) (v : Fin n) (hvk : v < k) :
    ¬ G.Adj v i := by
  intro hadj
  have hle := (firstNeighbor_spec G i v (lt_trans hvk hki) hadj).2
  rw [hFk] at hle
  exact not_lt_of_ge hle hvk

private lemma find?_some_gt_false {n : ℕ} (P : Fin n → Bool) (l v : Fin n)
    (L : List (Fin n)) (hL : L.Pairwise (fun a b => b < a))
    (hf : L.find? P = some l) (hv : v ∈ L) (hlv : l < v) :
    P v = false := by
  induction L with
  | nil => simp at hf
  | cons a tl ih =>
    rw [List.pairwise_cons] at hL
    simp only [List.mem_cons] at hv
    rw [List.find?_cons] at hf
    cases hPa : P a with
    | false =>
      simp only [hPa] at hf
      rcases hv with rfl | hvtl
      · exact hPa
      · exact ih hL.2 hf hvtl
    | true =>
      simp only [hPa, Option.some.injEq] at hf
      subst hf
      rcases hv with rfl | hvtl
      · exact (lt_irrefl _ hlv).elim
      · exact (lt_asymm hlv (hL.1 v hvtl)).elim

private lemma lastNonneighbor_eq_some {n : ℕ} (G : SimpleGraph (Fin n)) (j l : Fin n)
    (h : lastNonneighbor G j = some l) :
    (l < j ∧ ¬ G.Adj l j) ∧ (∀ v : Fin n, l < v → v < j → G.Adj v j) := by
  classical
  unfold lastNonneighbor at h
  set P : Fin n → Bool := fun k => decide (k < j ∧ ¬ G.Adj k j)
  have hPl : P l = true := List.find?_some h
  have hlj : l < j ∧ ¬ G.Adj l j := by simpa [P] using hPl
  refine ⟨hlj, ?_⟩
  intro v hlv hvj
  have hPair : (List.finRange n).reverse.Pairwise (fun a b => b < a) :=
    List.pairwise_reverse.mpr (pairwise_lt_finRange n)
  have hv_mem : v ∈ (List.finRange n).reverse :=
    List.mem_reverse.mpr (List.mem_finRange v)
  have hPv : P v = false := find?_some_gt_false P l v (List.finRange n).reverse hPair h hv_mem hlv
  simp only [P, decide_eq_false_iff_not, not_and, not_not] at hPv
  exact hPv hvj

private lemma lastNonneighbor_eq_none {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n)
    (h : lastNonneighbor G j = none) :
    ∀ v : Fin n, v < j → G.Adj v j := by
  classical
  unfold lastNonneighbor at h
  intro v hvj
  have hall := List.find?_eq_none.mp h v (List.mem_reverse.mpr (List.mem_finRange v))
  simp only [decide_eq_true_eq, not_and, not_not] at hall
  exact hall hvj

private lemma perfectMatching_pair {V : Type*} [DecidableEq V] (G : SimpleGraph V) (a b : V)
    (hab : G.Adj a b) :
    ∃ M : (G.induce (({a, b} : Finset V) : Set V)).Subgraph, M.IsPerfectMatching := by
  refine ⟨⊤, SimpleGraph.Subgraph.isPerfectMatching_iff.mpr ?_⟩
  rintro ⟨v, hv⟩
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · refine ⟨⟨b, by simp⟩, by simpa using hab, ?_⟩
    rintro ⟨w, hw⟩ hvw
    simp only [SimpleGraph.Subgraph.top_adj, SimpleGraph.induce_adj] at hvw
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (G.ne_of_adj hvw rfl).elim
    · rfl
  · refine ⟨⟨a, by simp⟩, by simpa using hab.symm, ?_⟩
    rintro ⟨w, hw⟩ hvw
    simp only [SimpleGraph.Subgraph.top_adj, SimpleGraph.induce_adj] at hvw
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · rfl
    · exact (G.ne_of_adj hvw rfl).elim

private lemma perfectMatching_erase_pair {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (T : Finset V) (u w : V) (hu : u ∈ T) (hw : w ∈ T)
    (M : (G.induce (T : Set V)).Subgraph) (hM : M.IsPerfectMatching)
    (huw : M.Adj ⟨u, hu⟩ ⟨w, hw⟩) :
    ∃ M₀ : (G.induce (((T.erase u).erase w : Finset V) : Set V)).Subgraph, M₀.IsPerfectMatching := by
  let T₀ := (T.erase u).erase w
  have hsub : ∀ x : T₀, x.1 ∈ T := fun x =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase x.2)
  have hu_uniq := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) ⟨u, hu⟩
  have hw_uniq := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) ⟨w, hw⟩
  let M₀ : (G.induce (T₀ : Set V)).Subgraph := {
    verts := Set.univ
    Adj := fun x y => M.Adj ⟨x.1, hsub x⟩ ⟨y.1, hsub y⟩
    adj_sub := fun hxy => M.adj_sub hxy
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨fun _ _ hxy => M.adj_symm hxy⟩
  }
  refine ⟨M₀, SimpleGraph.Subgraph.isPerfectMatching_iff.mpr ?_⟩
  intro x
  obtain ⟨y, hxy, hy_uniq⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) ⟨x.1, hsub x⟩
  have hy_ne_u : y.1 ≠ u := by
    intro hyu
    have hy_eq : y = ⟨u, hu⟩ := Subtype.ext hyu
    rw [hy_eq] at hxy
    have hxw : (⟨x.1, hsub x⟩ : T) = ⟨w, hw⟩ :=
      hu_uniq.unique hxy.symm huw
    have hx_eq_w : x.1 = w := congrArg Subtype.val hxw
    exact (Finset.mem_erase.mp x.2).1 hx_eq_w
  have hy_ne_w : y.1 ≠ w := by
    intro hyw
    have hy_eq : y = ⟨w, hw⟩ := Subtype.ext hyw
    rw [hy_eq] at hxy
    have hxu : (⟨x.1, hsub x⟩ : T) = ⟨u, hu⟩ :=
      hw_uniq.unique hxy.symm huw.symm
    have hx_eq_u : x.1 = u := congrArg Subtype.val hxu
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp x.2).2).1 hx_eq_u
  have hy_T0 : y.1 ∈ T₀ :=
    Finset.mem_erase.mpr ⟨hy_ne_w, Finset.mem_erase.mpr ⟨hy_ne_u, y.2⟩⟩
  refine ⟨⟨y.1, hy_T0⟩, hxy, ?_⟩
  intro z hxz
  have hz_eq : z.1 = y.1 := congrArg Subtype.val (hy_uniq ⟨z.1, hsub z⟩ hxz)
  exact Subtype.ext hz_eq

private lemma perfectMatching_insert_pair {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (T₀ : Finset V) (a b : V) (ha : a ∉ T₀) (hb : b ∉ T₀) (hab : G.Adj a b)
    (M₀ : (G.induce (T₀ : Set V)).Subgraph) (hM₀ : M₀.IsPerfectMatching) :
    ∃ M' : (G.induce ((insert a (insert b T₀) : Finset V) : Set V)).Subgraph, M'.IsPerfectMatching := by
  let S' := insert a (insert b T₀)
  have hne : a ≠ b := G.ne_of_adj hab
  have haS : a ∈ S' := Finset.mem_insert_self a _
  have hbS : b ∈ S' := Finset.mem_insert_of_mem (Finset.mem_insert_self b _)
  have hT0S : ∀ z ∈ T₀, z ∈ S' := fun z hz =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
  let M' : (G.induce (S' : Set V)).Subgraph := {
    verts := Set.univ
    Adj := fun x y =>
      (x.1 = a ∧ y.1 = b) ∨ (x.1 = b ∧ y.1 = a) ∨
        ∃ (hx : x.1 ∈ T₀) (hy : y.1 ∈ T₀), M₀.Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩
    adj_sub := by
      rintro x y (⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy, hxy⟩)
      · change G.Adj x.1 y.1; rw [hx, hy]; exact hab
      · change G.Adj x.1 y.1; rw [hx, hy]; exact hab.symm
      · exact M₀.adj_sub hxy
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨by
      rintro x y (⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy, hxy⟩)
      · exact Or.inr (Or.inl ⟨hy, hx⟩)
      · exact Or.inl ⟨hy, hx⟩
      · exact Or.inr (Or.inr ⟨hy, hx, M₀.adj_symm hxy⟩)⟩
  }
  refine ⟨M', SimpleGraph.Subgraph.isPerfectMatching_iff.mpr ?_⟩
  intro x
  have hx_mem : x.1 = a ∨ x.1 = b ∨ x.1 ∈ T₀ := by
    simpa [S', Finset.mem_insert] using x.2
  rcases hx_mem with hxa | hxb | hxT0
  · refine ⟨⟨b, hbS⟩, Or.inl ⟨hxa, rfl⟩, ?_⟩
    rintro y (⟨_, hyb⟩ | ⟨hxb, _⟩ | ⟨hxT0, _, _⟩)
    · exact Subtype.ext hyb
    · exact (hne (hxa.symm.trans hxb)).elim
    · exact (ha (hxa ▸ hxT0)).elim
  · refine ⟨⟨a, haS⟩, Or.inr (Or.inl ⟨hxb, rfl⟩), ?_⟩
    rintro y (⟨hxa, _⟩ | ⟨_, hya⟩ | ⟨hxT0, _, _⟩)
    · exact (hne (hxa.symm.trans hxb)).elim
    · exact Subtype.ext hya
    · exact (hb (hxb ▸ hxT0)).elim
  · obtain ⟨w, hxw, hw_uniq⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM₀) ⟨x.1, hxT0⟩
    refine ⟨⟨w.1, hT0S w.1 w.2⟩, Or.inr (Or.inr ⟨hxT0, w.2, hxw⟩), ?_⟩
    rintro y (⟨hxa, _⟩ | ⟨hxb, _⟩ | ⟨_, hyT0, hxy⟩)
    · exact (ha (hxa ▸ hxT0)).elim
    · exact (hb (hxb ▸ hxT0)).elim
    · have hy_eq : y.1 = w.1 := congrArg Subtype.val (hw_uniq ⟨y.1, hyT0⟩ hxy)
      exact Subtype.ext hy_eq

private def PairedDominatesWithin {n : ℕ} (G : SimpleGraph (Fin n))
    (m r : ℕ) (T : Finset (Fin n)) : Prop :=
  T ⊆ prefixVertices m ∧
    (∀ v ∈ prefixVertices r, v ∉ T → ∃ s ∈ T, G.Adj v s) ∧
    ∃ M : (G.induce (T : Set (Fin n))).Subgraph, M.IsPerfectMatching

private lemma pairedDominatesWithin_pred {n : ℕ} (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G)
    (hconn : G.Connected) (m r : ℕ) (hr : 2 ≤ r) (hrm : r ≤ m) (hmn : m + 1 ≤ n)
    (T : Finset (Fin n)) (hT : PairedDominatesWithin G (m + 1) r T) :
    ∃ S' : Finset (Fin n), PairedDominatesWithin G m r S' ∧ S'.card ≤ T.card := by
  let um : Fin n := ⟨m, by omega⟩
  rcases hT with ⟨hTU, hTdom, M, hM⟩
  by_cases hum : um ∈ T
  · obtain ⟨w_sub, huw_M, _⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) ⟨um, hum⟩
    let w := w_sub.1
    have hw_T : w ∈ T := w_sub.2
    have hum_w_adj : G.Adj um w := M.adj_sub huw_M
    have hw_ne_um : w ≠ um := (G.ne_of_adj hum_w_adj).symm
    have hw_lt_m : w.val < m := by
      have hw_U := hTU hw_T
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hw_U
      have : w.val ≠ m := fun h => hw_ne_um (Fin.ext h)
      omega
    have hw_lt_um : w < um := hw_lt_m
    have hw_pref : w ∈ prefixVertices m := by
      simp [prefixVertices, hw_lt_m]
    let T₀ := (T.erase um).erase w
    obtain ⟨M₀, hM₀⟩ := perfectMatching_erase_pair G T um w hum hw_T M hM huw_M
    have hT0_sub : T₀ ⊆ prefixVertices m := by
      intro x hx
      have hx_ne_um : x ≠ um := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hx_T : x ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
      have hx_U := hTU hx_T
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hx_U ⊢
      have : x.val ≠ m := fun h => hx_ne_um (Fin.ext h)
      omega
    have hw_not_T0 : w ∉ T₀ := Finset.notMem_erase w _
    have hcard_T0 : T₀.card + 2 = T.card := by
      have hw_erase : w ∈ T.erase um := Finset.mem_erase.mpr ⟨hw_ne_um, hw_T⟩
      have h1 := Finset.card_erase_add_one hw_erase
      have h2 := Finset.card_erase_add_one hum
      dsimp [T₀]
      omega
    let f := firstNeighbor G um
    obtain ⟨⟨hf_lt_um, hf_adj_um⟩, hf_le_w⟩ := firstNeighbor_spec G um w hw_lt_um hum_w_adj.symm
    have hf_pref : f ∈ prefixVertices m := by
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hf_lt_um
    have hf_dom_um : ∀ v ∈ prefixVertices r, v ≠ f → G.Adj v um → G.Adj v f := by
      intro v hv hvf hv_adj
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hv_lt_um : v < um := by change v.val < m; omega
      have hf_le_v : f ≤ v := (firstNeighbor_spec G um v hv_lt_um hv_adj).2
      have hf_lt_v : f < v := lt_of_le_of_ne hf_le_v hvf.symm
      exact (obs5 G R um f hf_lt_um hf_adj_um.symm v hf_lt_v hv_lt_um.le).symm
    by_cases hf_mem : f ∈ insert w T₀
    · have hdom_wT0 : ∀ v ∈ prefixVertices r, v ∉ insert w T₀ → ∃ s ∈ insert w T₀, G.Adj v s := by
        intro v hv hv_not
        have hv_lt_r : v.val < r := by simpa [prefixVertices] using hv
        have hv_ne_um : v ≠ um := by
          intro h; rw [h] at hv_lt_r; dsimp [um] at hv_lt_r; omega
        have hv_not_T : v ∉ T := by
          intro hvT
          apply hv_not
          by_cases hvw : v = w
          · exact hvw ▸ Finset.mem_insert_self w T₀
          · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvw, Finset.mem_erase.mpr ⟨hv_ne_um, hvT⟩⟩)
        obtain ⟨t, htT, hvt_adj⟩ := hTdom v hv hv_not_T
        by_cases htum : t = um
        · subst htum
          have hvf : v ≠ f := fun h => hv_not (h ▸ hf_mem)
          exact ⟨f, hf_mem, hf_dom_um v hv hvf hvt_adj⟩
        · by_cases htw : t = w
          · exact ⟨w, Finset.mem_insert_self w T₀, htw ▸ hvt_adj⟩
          · exact ⟨t, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨htw, Finset.mem_erase.mpr ⟨htum, htT⟩⟩), hvt_adj⟩
      by_cases hz_ex : ∃ z ∈ prefixVertices m, z ∉ T₀ ∧ G.Adj w z
      · obtain ⟨z, hz_pref, hz_not_T0, hwz_adj⟩ := hz_ex
        let S' := insert z (insert w T₀)
        obtain ⟨M', hM'⟩ := perfectMatching_insert_pair G T₀ z w hz_not_T0 hw_not_T0 hwz_adj.symm M₀ hM₀
        have hS'_paired : PairedDominatesWithin G m r S' := by
          refine ⟨?_, ?_, M', hM'⟩
          · intro x hx
            simp only [S', Finset.mem_insert] at hx
            rcases hx with rfl | rfl | hxT0
            · exact hz_pref
            · exact hw_pref
            · exact hT0_sub hxT0
          · intro v hv hvS'
            have hv_not_wT0 : v ∉ insert w T₀ := fun h => hvS' (Finset.mem_insert_of_mem h)
            obtain ⟨s, hs, hvs⟩ := hdom_wT0 v hv hv_not_wT0
            exact ⟨s, Finset.mem_insert_of_mem hs, hvs⟩
        have hcard_S' : S'.card ≤ T.card := by
          calc S'.card ≤ (insert w T₀).card + 1 := Finset.card_insert_le z _
            _ ≤ (T₀.card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le w T₀) 1
            _ = T.card := hcard_T0
        exact ⟨S', hS'_paired, hcard_S'⟩
      · have hz_ex' : ∀ z ∈ prefixVertices m, z ∉ T₀ → ¬ G.Adj w z :=
          fun z hz hnot hadj => hz_ex ⟨z, hz, hnot, hadj⟩
        have hT0_paired : PairedDominatesWithin G m r T₀ := by
          refine ⟨hT0_sub, ?_, M₀, hM₀⟩
          intro v hv hvT0
          have hv_m : v ∈ prefixVertices m := by
            simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
            omega
          by_cases hvw : v = w
          · obtain ⟨z, hz_pref, hwz_adj⟩ := exists_neighbor_in_prefix G R hconn m (by omega) (by omega) v hv_m
            have hz_T0 : z ∈ T₀ := by
              by_contra hz_not
              exact hz_ex' z hz_pref hz_not (hvw ▸ hwz_adj)
            exact ⟨z, hz_T0, hwz_adj⟩
          · have hv_not_wT0 : v ∉ insert w T₀ := by
              simp [Finset.mem_insert, hvw, hvT0]
            obtain ⟨s, hs, hvs⟩ := hdom_wT0 v hv hv_not_wT0
            simp only [Finset.mem_insert] at hs
            rcases hs with rfl | hsT0
            · exfalso
              exact hz_ex' v hv_m hvT0 hvs.symm
            · exact ⟨s, hsT0, hvs⟩
        exact ⟨T₀, hT0_paired, by omega⟩
    · have hf_ne_w : f ≠ w := fun h => hf_mem (h ▸ Finset.mem_insert_self w T₀)
      have hf_not_T0 : f ∉ T₀ := fun h => hf_mem (Finset.mem_insert_of_mem h)
      have hf_lt_w : f < w := lt_of_le_of_ne hf_le_w hf_ne_w
      have hfw_adj : G.Adj f w := obs5 G R um f hf_lt_um hf_adj_um.symm w hf_lt_w hw_lt_um.le
      let S' := insert f (insert w T₀)
      obtain ⟨M', hM'⟩ := perfectMatching_insert_pair G T₀ f w hf_not_T0 hw_not_T0 hfw_adj M₀ hM₀
      have hS'_paired : PairedDominatesWithin G m r S' := by
        refine ⟨?_, ?_, M', hM'⟩
        · intro x hx
          simp only [S', Finset.mem_insert] at hx
          rcases hx with rfl | rfl | hxT0
          · exact hf_pref
          · exact hw_pref
          · exact hT0_sub hxT0
        · intro v hv hvS'
          simp only [S', Finset.mem_insert, not_or] at hvS'
          rcases hvS' with ⟨hvf, hvw, hvT0⟩
          have hv_lt_r : v.val < r := by simpa [prefixVertices] using hv
          have hv_ne_um : v ≠ um := by
            intro h; rw [h] at hv_lt_r; dsimp [um] at hv_lt_r; omega
          have hv_not_T : v ∉ T := by
            intro hvT
            exact hvT0 (Finset.mem_erase.mpr ⟨hvw, Finset.mem_erase.mpr ⟨hv_ne_um, hvT⟩⟩)
          obtain ⟨t, htT, hvt_adj⟩ := hTdom v hv hv_not_T
          by_cases htum : t = um
          · subst htum
            exact ⟨f, Finset.mem_insert_self f _, hf_dom_um v hv hvf hvt_adj⟩
          · by_cases htw : t = w
            · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_self w T₀), htw ▸ hvt_adj⟩
            · exact ⟨t, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_erase.mpr ⟨htw, Finset.mem_erase.mpr ⟨htum, htT⟩⟩)), hvt_adj⟩
      have hcard_S' : S'.card ≤ T.card := by
        calc S'.card ≤ (insert w T₀).card + 1 := Finset.card_insert_le f _
          _ ≤ (T₀.card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le w T₀) 1
          _ = T.card := hcard_T0
      exact ⟨S', hS'_paired, hcard_S'⟩
  · refine ⟨T, ⟨?_, hTdom, M, hM⟩, le_rfl⟩
    intro x hx
    have hx_U1 := hTU hx
    have hx_ne_um : x ≠ um := fun h => hum (h ▸ hx)
    simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hx_U1 ⊢
    have : x.val ≠ m := fun h => hx_ne_um (Fin.ext h)
    omega

private lemma pairedDominatesWithin_mono_aux {n : ℕ} (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G)
    (hconn : G.Connected) (r : ℕ) (hr : 2 ≤ r) (d : ℕ) (hdn : r + d ≤ n)
    (T : Finset (Fin n)) (hT : PairedDominatesWithin G (r + d) r T) :
    ∃ S' : Finset (Fin n), PairedDominatesOn G (prefixVertices r) S' ∧ S'.card ≤ T.card := by
  induction d generalizing T with
  | zero =>
    rw [Nat.add_zero] at hT
    exact ⟨T, hT, le_rfl⟩
  | succ d ih =>
    rw [← Nat.add_assoc] at hT hdn
    obtain ⟨T', hT', hcard⟩ := pairedDominatesWithin_pred G R hconn (r + d) r hr (Nat.le_add_right r d) hdn T hT
    obtain ⟨S', hS', hcard'⟩ := ih (by omega) T' hT'
    exact ⟨S', hS', le_trans hcard' hcard⟩

private lemma right_lt_left_of_not_adj {n : ℕ} (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G)
    (l j : Fin n) (hlj : l < j) (hnadj : ¬ G.Adj l j) :
    R.right l < R.left j := by
  by_contra hle
  have hle' : R.left j ≤ R.right l := le_of_not_gt hle
  apply hnadj
  rw [R.represents l j hlj.ne]
  exact ⟨R.left j, ⟨R.ordered hlj.le, hle'⟩, ⟨le_rfl, R.nonempty j⟩⟩

private lemma not_adj_ge_of_not_adj {n : ℕ} (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G)
    (l j z : Fin n) (hlj : l < j) (hnadj : ¬ G.Adj l j) (hjz : j ≤ z) :
    ¬ G.Adj l z := by
  intro hadj
  have hlz : l < z := lt_of_lt_of_le hlj hjz
  exact hnadj (obs5 G R z l hlz hadj.symm j hlj hjz)

private lemma adj_l_and_neighbors_of_lt_and_adj_ge {n : ℕ} (G : SimpleGraph (Fin n))
    (R : OrderedRepresentation G) (l j v z : Fin n)
    (hlj : l < j) (hnadj : ¬ G.Adj l j) (hvl : v < l) (hjz : j ≤ z) (hvz : G.Adj v z) :
    G.Adj v l ∧ ∀ u : Fin n, G.Adj l u → v ≠ u → G.Adj v u := by
  have hvz_lt : v < z := lt_trans hvl (lt_of_lt_of_le hlj hjz)
  obtain ⟨p, hp_v, hp_z⟩ := (R.represents v z hvz_lt.ne).mp hvz
  have hrl_lt : R.right l < R.left j := right_lt_left_of_not_adj G R l j hlj hnadj
  have hsub : Set.Icc (R.left l) (R.right l) ⊆ Set.Icc (R.left v) (R.right v) := by
    intro q hq
    refine ⟨le_trans (R.ordered hvl.le) hq.1, ?_⟩
    have h1 : R.left j ≤ R.left z := R.ordered hjz
    linarith [hq.2, hp_z.1, hp_v.2]
  have hvl_adj : G.Adj v l := by
    rw [R.represents v l hvl.ne]
    exact ⟨R.left l, hsub ⟨le_rfl, R.nonempty l⟩, ⟨le_rfl, R.nonempty l⟩⟩
  refine ⟨hvl_adj, ?_⟩
  intro u hlu hvu
  have hlu_ne : l ≠ u := G.ne_of_adj hlu
  obtain ⟨q, hq_l, hq_u⟩ := (R.represents l u hlu_ne).mp hlu
  rw [R.represents v u hvu]
  exact ⟨q, hsub hq_l, hq_u⟩

private lemma extract_T1_of_lastNonneighbor_some {n : ℕ} (G : SimpleGraph (Fin n))
    (R : OrderedRepresentation G) (i j k l : Fin n)
    (hjk : j < k) (hki : k < i)
    (hFk : firstNeighbor G i = k) (hFj : firstNeighbor G k = j)
    (hl : lastNonneighbor G j = some l)
    (T : Finset (Fin n)) (hT : PairedDominatesOn G (prefixVertices (i.val + 1)) T) :
    ∃ T₁ : Finset (Fin n),
      PairedDominatesWithin G (i.val + 1) (l.val + 1) T₁ ∧ T₁.card + 2 = T.card := by
  obtain ⟨⟨hlj, hnadj_lj⟩, _⟩ := lastNonneighbor_eq_some G j l hl
  rcases hT with ⟨hTU, hTdom, M, hM⟩
  have hi_U : i ∈ prefixVertices (i.val + 1) := by simp [prefixVertices]
  have hx_ex : ∃ x ∈ T, k ≤ x ∧ x ≤ i := by
    by_cases hiT : i ∈ T
    · exact ⟨i, hiT, hki.le, le_rfl⟩
    · obtain ⟨x, hxT, hix⟩ := hTdom i hi_U hiT
      have hx_U := hTU hxT
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hx_U
      have hxi : x ≤ i := by change x.val ≤ i.val; omega
      have hkx : k ≤ x := by
        by_contra hlt
        exact not_adj_of_lt_firstNeighbor G i k hFk hki x (lt_of_not_ge hlt) hix.symm
      exact ⟨x, hxT, hkx, hxi⟩
  obtain ⟨x, hxT, hkx, hxi⟩ := hx_ex
  obtain ⟨y_sub, hxy_M, _⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) ⟨x, hxT⟩
  let y := y_sub.1
  have hyT : y ∈ T := y_sub.2
  have hxy_adj : G.Adj x y := M.adj_sub hxy_M
  have hy_ne_x : y ≠ x := (G.ne_of_adj hxy_adj).symm
  have hjy : j ≤ y := by
    by_contra hlt
    have hyj : y < j := lt_of_not_ge hlt
    have hyk : y < k := lt_trans hyj hjk
    have hyx : y < x := lt_of_lt_of_le hyk hkx
    have hyk_adj : G.Adj y k := obs5 G R x y hyx hxy_adj k hyk hkx
    exact not_adj_of_lt_firstNeighbor G k j hFj hjk y hyj hyk_adj
  let T₁ := (T.erase x).erase y
  obtain ⟨M₁, hM₁⟩ := perfectMatching_erase_pair G T x y hxT hyT M hM hxy_M
  have hT1_sub : T₁ ⊆ prefixVertices (i.val + 1) := fun z hz =>
    hTU (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
  have hcard_T1 : T₁.card + 2 = T.card := by
    have hy_erase : y ∈ T.erase x := Finset.mem_erase.mpr ⟨hy_ne_x, hyT⟩
    have h1 := Finset.card_erase_add_one hy_erase
    have h2 := Finset.card_erase_add_one hxT
    dsimp [T₁]
    omega
  have hl_lt_x : l < x := lt_trans hlj (lt_of_lt_of_le hjk hkx)
  have hl_ne_x : l ≠ x := hl_lt_x.ne
  have hl_ne_y : l ≠ y := (lt_of_lt_of_le hlj hjy).ne
  have hl_not_adj_x : ¬ G.Adj l x :=
    not_adj_ge_of_not_adj G R l j x hlj hnadj_lj (le_trans hjk.le hkx)
  have hl_not_adj_y : ¬ G.Adj l y :=
    not_adj_ge_of_not_adj G R l j y hlj hnadj_lj hjy
  have hl_U : l ∈ prefixVertices (i.val + 1) := by
    simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    have : l < i := lt_trans hlj (lt_trans hjk hki)
    exact lt_trans this (Nat.lt_succ_self i.val)
  have hl_dom_T1 : l ∈ T₁ ∨ ∃ u ∈ T₁, G.Adj l u := by
    by_cases hlT1 : l ∈ T₁
    · exact Or.inl hlT1
    · right
      have hl_not_T : l ∉ T := by
        intro hlT
        exact hlT1 (Finset.mem_erase.mpr ⟨hl_ne_y, Finset.mem_erase.mpr ⟨hl_ne_x, hlT⟩⟩)
      obtain ⟨u, huT, hlu_adj⟩ := hTdom l hl_U hl_not_T
      have hu_ne_x : u ≠ x := fun h => hl_not_adj_x (h ▸ hlu_adj)
      have hu_ne_y : u ≠ y := fun h => hl_not_adj_y (h ▸ hlu_adj)
      exact ⟨u, Finset.mem_erase.mpr ⟨hu_ne_y, Finset.mem_erase.mpr ⟨hu_ne_x, huT⟩⟩, hlu_adj⟩
  refine ⟨T₁, ⟨hT1_sub, ?_, M₁, hM₁⟩, hcard_T1⟩
  intro v hv hvT1
  simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have hvl_le : v ≤ l := by change v.val ≤ l.val; omega
  by_cases hvl_eq : v = l
  · subst hvl_eq
    rcases hl_dom_T1 with hlT1 | ⟨u, huT1, hlu⟩
    · exact (hvT1 hlT1).elim
    · exact ⟨u, huT1, hlu⟩
  · have hvl_lt : v < l := lt_of_le_of_ne hvl_le hvl_eq
    have hv_ne_x : v ≠ x := (lt_trans hvl_lt (lt_trans hlj (lt_of_lt_of_le hjk hkx))).ne
    have hv_ne_y : v ≠ y := (lt_trans hvl_lt (lt_of_lt_of_le hlj hjy)).ne
    have hv_not_T : v ∉ T := by
      intro hvT
      exact hvT1 (Finset.mem_erase.mpr ⟨hv_ne_y, Finset.mem_erase.mpr ⟨hv_ne_x, hvT⟩⟩)
    have hv_U : v ∈ prefixVertices (i.val + 1) := by
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      have : v < i := lt_trans hvl_lt (lt_trans hlj (lt_trans hjk hki))
      exact lt_trans this (Nat.lt_succ_self i.val)
    obtain ⟨t, htT, hvt_adj⟩ := hTdom v hv_U hv_not_T
    by_cases htxy : t = x ∨ t = y
    · have hjt : j ≤ t := by
        rcases htxy with rfl | rfl
        · exact le_trans hjk.le hkx
        · exact hjy
      obtain ⟨hvl_adj, hvu_all⟩ :=
        adj_l_and_neighbors_of_lt_and_adj_ge G R l j v t hlj hnadj_lj hvl_lt hjt hvt_adj
      rcases hl_dom_T1 with hlT1 | ⟨u, huT1, hlu_adj⟩
      · exact ⟨l, hlT1, hvl_adj⟩
      · have hvu_ne : v ≠ u := fun h => hvT1 (h ▸ huT1)
        exact ⟨u, huT1, hvu_all u hlu_adj hvu_ne⟩
    · have htxy' : t ≠ x ∧ t ≠ y := not_or.mp htxy
      exact ⟨t, Finset.mem_erase.mpr ⟨htxy'.2, Finset.mem_erase.mpr ⟨htxy'.1, htT⟩⟩, hvt_adj⟩

private lemma two_le_card_of_pairedDominatesOn {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (U T : Finset V) (hU : U.Nonempty) (hT : PairedDominatesOn G U T) :
    2 ≤ T.card := by
  rcases hT with ⟨_, hdom, M, hM⟩
  obtain ⟨u, hu⟩ := hU
  have hT_nonempty : T.Nonempty := by
    by_cases huT : u ∈ T
    · exact ⟨u, huT⟩
    · obtain ⟨s, hsT, _⟩ := hdom u hu huT
      exact ⟨s, hsT⟩
  obtain ⟨v, hvT⟩ := hT_nonempty
  obtain ⟨w, hvw, _⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) ⟨v, hvT⟩
  have hadj : G.Adj v w.1 := M.adj_sub hvw
  have hne : v ≠ w.1 := G.ne_of_adj hadj
  exact Finset.one_lt_card.mpr ⟨v, hvT, w.1, w.2, hne⟩

end Lemma9Proof

open Lemma9Proof in
theorem solution
    {n : ℕ} (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G)
    (hconn : G.Connected) (i j k : Fin n) (hjk : j < k) (hki : k < i)
    (hFk : firstNeighbor G i = k) (hFj : firstNeighbor G k = j) :
    (∀ l : Fin n, 1 ≤ l.val → lastNonneighbor G j = some l →
      ∀ S : Finset (Fin n), MinimumPairedDominatesOn G (prefixVertices (l.val + 1)) S →
        MinimumPairedDominatesOn G (prefixVertices (i.val + 1)) (S ∪ {j, k})) ∧
    (lastNonneighbor G j = some ⟨0, by omega⟩ →
      MinimumPairedDominatesOn G (prefixVertices (i.val + 1))
        {⟨0, by omega⟩, ⟨1, by omega⟩, j, k}) ∧
    (lastNonneighbor G j = none →
      MinimumPairedDominatesOn G (prefixVertices (i.val + 1)) {j, k}) := by
  have hki_adj : G.Adj k i := by
    have h := (firstNeighbor_lt_and_adj_of_ne G i (by rw [hFk]; exact hki.ne)).2
    rwa [hFk] at h
  have hjk_adj : G.Adj j k := by
    have h := (firstNeighbor_lt_and_adj_of_ne G k (by rw [hFj]; exact hjk.ne)).2
    rwa [hFj] at h
  have hdom_jk_gt : ∀ v : Fin n, j < v → v ≤ i → v ≠ k → G.Adj v j ∨ G.Adj v k := by
    intro v hjv hvi hvk
    by_cases hvk_lt : v < k
    · left
      exact (obs5 G R k j hjk hjk_adj.symm v hjv hvk_lt.le).symm
    · right
      have hkv : k < v := lt_of_le_of_ne (le_of_not_gt hvk_lt) hvk.symm
      exact (obs5 G R i k hki hki_adj.symm v hkv hvi).symm
  have hj_lt_i : j.val < i.val := lt_trans hjk hki
  have hk_lt_i : k.val < i.val := hki
  refine ⟨?_, ?_, ?_⟩
  · intro l hl1 hl_some S hS
    obtain ⟨⟨hlj, hnadj_lj⟩, hdom_lj⟩ := lastNonneighbor_eq_some G j l hl_some
    rcases hS with ⟨⟨hSU, hSdom, M_S, hM_S⟩, hS_min⟩
    have hj_not_S : j ∉ S := by
      intro hjS
      have hjU := hSU hjS
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hjU
      change l.val < j.val at hlj
      omega
    have hk_not_S : k ∉ S := by
      intro hkS
      have hkU := hSU hkS
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hkU
      have : l.val < k.val := lt_trans hlj hjk
      omega
    have hS_union_eq : S ∪ {j, k} = insert j (insert k S) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    obtain ⟨M', hM'⟩ := perfectMatching_insert_pair G S j k hj_not_S hk_not_S hjk_adj M_S hM_S
    have hpaired : PairedDominatesOn G (prefixVertices (i.val + 1)) (S ∪ {j, k}) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with hxS | rfl | rfl
        · have hxU := hSU hxS
          simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hxU
          have : l.val < i.val := lt_trans hlj (lt_trans hjk hki)
          omega
        · omega
        · omega
      · intro v hv hv_not
        simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hv_not
        rcases hv_not with ⟨hvS, hvj, hvk⟩
        by_cases hvl : v.val < l.val + 1
        · have hv_Ul : v ∈ prefixVertices (l.val + 1) := by
            simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hvl
          obtain ⟨s, hsS, hvs⟩ := hSdom v hv_Ul hvS
          exact ⟨s, Finset.mem_union_left _ hsS, hvs⟩
        · have hlv : l < v := by change l.val < v.val; omega
          by_cases hvj_lt : v < j
          · exact ⟨j, by simp, hdom_lj v hlv hvj_lt⟩
          · have hjv : j < v := lt_of_le_of_ne (le_of_not_gt hvj_lt) (Ne.symm hvj)
            have hvi : v ≤ i := by change v.val ≤ i.val; omega
            rcases hdom_jk_gt v hjv hvi hvk with hvj_adj | hvk_adj
            · exact ⟨j, by simp, hvj_adj⟩
            · exact ⟨k, by simp, hvk_adj⟩
      · rw [hS_union_eq]
        exact ⟨M', hM'⟩
    refine ⟨hpaired, ?_⟩
    intro T hT
    obtain ⟨T₁, hT₁, hcard_T1⟩ := extract_T1_of_lastNonneighbor_some G R i j k l hjk hki hFk hFj hl_some T hT
    let d := i.val - l.val
    have h_eq : (l.val + 1) + d = i.val + 1 := by
      have : l.val < i.val := lt_trans hlj (lt_trans hjk hki)
      omega
    rw [← h_eq] at hT₁
    obtain ⟨S', hS', hcard_S'⟩ := pairedDominatesWithin_mono_aux G R hconn (l.val + 1) (by omega) d
      (by omega) T₁ hT₁
    have hS_le_S' : S.card ≤ S'.card := hS_min S' hS'
    have hcard_union : (S ∪ {j, k}).card ≤ S.card + 2 := by
      rw [hS_union_eq]
      calc (insert j (insert k S)).card ≤ (insert k S).card + 1 := Finset.card_insert_le j _
        _ ≤ (S.card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le k S) 1
        _ = S.card + 2 := by omega
    omega
  · intro hl_zero
    let z0 : Fin n := ⟨0, by omega⟩
    let z1 : Fin n := ⟨1, by omega⟩
    obtain ⟨⟨hz0_j, hnadj_z0_j⟩, hdom_z0_j⟩ := lastNonneighbor_eq_some G j z0 hl_zero
    obtain ⟨u, huz1, hu_z1_adj⟩ := exists_earlier_neighbor G R hconn z1 (by dsimp [z1]; omega)
    have hu_eq_z0 : u = z0 := by
      ext
      change u.val < 1 at huz1
      dsimp [z0]
      omega
    subst hu_eq_z0
    have hz1_ne_j : z1 ≠ j := fun h => hnadj_z0_j (h ▸ hu_z1_adj)
    have hz1_lt_j : z1 < j := by
      change 1 < j.val
      change 0 < j.val at hz0_j
      have : j.val ≠ 1 := fun h => hz1_ne_j (Fin.ext h.symm)
      omega
    have hz0_not_jk : z0 ∉ ({j, k} : Finset (Fin n)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hz0_j.ne, (lt_trans hz0_j hjk).ne⟩
    have hz1_not_jk : z1 ∉ ({j, k} : Finset (Fin n)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hz1_lt_j.ne, (lt_trans hz1_lt_j hjk).ne⟩
    obtain ⟨M_jk, hM_jk⟩ := perfectMatching_pair G j k hjk_adj
    obtain ⟨M4, hM4⟩ := perfectMatching_insert_pair G {j, k} z0 z1 hz0_not_jk hz1_not_jk hu_z1_adj M_jk hM_jk
    have hpaired4 : PairedDominatesOn G (prefixVertices (i.val + 1)) {z0, z1, j, k} := by
      refine ⟨?_, ?_, M4, hM4⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl | rfl | rfl
        · dsimp [z0]; omega
        · have : 1 < i.val := lt_trans hz1_lt_j hj_lt_i
          dsimp [z1]; omega
        · omega
        · omega
      · intro v hv hv_not
        simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv_not
        rcases hv_not with ⟨hvz0, hvz1, hvj, hvk⟩
        have hz0_lt_v : z0 < v := by
          change 0 < v.val
          have : v.val ≠ 0 := fun h => hvz0 (Fin.ext h)
          omega
        by_cases hvj_lt : v < j
        · exact ⟨j, by simp, hdom_z0_j v hz0_lt_v hvj_lt⟩
        · have hjv : j < v := lt_of_le_of_ne (le_of_not_gt hvj_lt) (Ne.symm hvj)
          have hvi : v ≤ i := by change v.val ≤ i.val; omega
          rcases hdom_jk_gt v hjv hvi hvk with hvj_adj | hvk_adj
          · exact ⟨j, by simp, hvj_adj⟩
          · exact ⟨k, by simp, hvk_adj⟩
    refine ⟨hpaired4, ?_⟩
    intro T hT
    obtain ⟨T₁, ⟨_, hT1_dom, M₁, hM₁⟩, hcard_T1⟩ :=
      extract_T1_of_lastNonneighbor_some G R i j k z0 hjk hki hFk hFj hl_zero T hT
    have hz0_U1 : z0 ∈ prefixVertices (z0.val + 1) := by simp [prefixVertices, z0]
    have hT1_nonempty : T₁.Nonempty := by
      by_cases hz0_T1 : z0 ∈ T₁
      · exact ⟨z0, hz0_T1⟩
      · obtain ⟨s, hsT1, _⟩ := hT1_dom z0 hz0_U1 hz0_T1
        exact ⟨s, hsT1⟩
    obtain ⟨a, haT1⟩ := hT1_nonempty
    obtain ⟨b, hab_M1, _⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM₁) ⟨a, haT1⟩
    have hab_ne : a ≠ b.1 := G.ne_of_adj (M₁.adj_sub hab_M1)
    have h2_le_T1 : 2 ≤ T₁.card := Finset.one_lt_card.mpr ⟨a, haT1, b.1, b.2, hab_ne⟩
    have hcard_4 : ({z0, z1, j, k} : Finset (Fin n)).card ≤ 4 := by
      calc ({z0, z1, j, k} : Finset (Fin n)).card ≤ ({z1, j, k} : Finset (Fin n)).card + 1 :=
            Finset.card_insert_le z0 _
        _ ≤ ({j, k} : Finset (Fin n)).card + 1 + 1 :=
            Nat.add_le_add_right (Finset.card_insert_le z1 _) 1
        _ ≤ 2 + 1 + 1 := Nat.add_le_add_right (Nat.add_le_add_right Finset.card_le_two 1) 1
        _ = 4 := rfl
    exact le_trans hcard_4 (by omega)
  · intro hl_none
    have hdom_all_lt_j := lastNonneighbor_eq_none G j hl_none
    obtain ⟨M_jk, hM_jk⟩ := perfectMatching_pair G j k hjk_adj
    have hpaired2 : PairedDominatesOn G (prefixVertices (i.val + 1)) {j, k} := by
      refine ⟨?_, ?_, M_jk, hM_jk⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl
        · omega
        · omega
      · intro v hv hv_not
        simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv_not
        rcases hv_not with ⟨hvj, hvk⟩
        by_cases hvj_lt : v < j
        · exact ⟨j, by simp, hdom_all_lt_j v hvj_lt⟩
        · have hjv : j < v := lt_of_le_of_ne (le_of_not_gt hvj_lt) (Ne.symm hvj)
          have hvi : v ≤ i := by change v.val ≤ i.val; omega
          rcases hdom_jk_gt v hjv hvi hvk with hvj_adj | hvk_adj
          · exact ⟨j, by simp, hvj_adj⟩
          · exact ⟨k, by simp, hvk_adj⟩
    refine ⟨hpaired2, ?_⟩
    intro T hT
    have hi_mem : i ∈ prefixVertices (i.val + 1) := by simp [prefixVertices]
    have h2 : 2 ≤ T.card := two_le_card_of_pairedDominatesOn G (prefixVertices (i.val + 1)) T ⟨i, hi_mem⟩ hT
    exact le_trans Finset.card_le_two h2
