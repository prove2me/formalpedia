-- Prove2me | solution 1 for ChenPairedDomination.Interval.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:23:37.062812+00:00
-- url     : https://prove2.me/submissions/43fcfc3d-74a2-497e-8e75-75098a0aada6

import Definitions.Def_ChenPairedDomination_Interval_PrefixData

open ChenPairedDomination.Interval

namespace Lemma8Proof

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
    (r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n) (w : Fin n) (hw : w ∈ prefixVertices r) :
    ∃ z ∈ prefixVertices r, G.Adj w z := by
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

end Lemma8Proof

open Lemma8Proof in
theorem solution
    {n : ℕ} (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G)
    (hconn : G.Connected) (r : ℕ) (hr : 2 ≤ r) (hrn : r + 1 ≤ n)
    (S T : Finset (Fin n))
    (hS : MinimumPairedDominatesOn G (prefixVertices r) S)
    (hT : MinimumPairedDominatesOn G (prefixVertices (r + 1)) T) :
    S.card ≤ T.card := by
  let ur : Fin n := ⟨r, by omega⟩
  rcases hT with ⟨⟨hTU, hTdom, M, hM⟩, _⟩
  by_cases hur : ur ∈ T
  · obtain ⟨w_sub, huw_M, _⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) ⟨ur, hur⟩
    let w := w_sub.1
    have hw_T : w ∈ T := w_sub.2
    have hur_w_adj : G.Adj ur w := M.adj_sub huw_M
    have hw_ne_ur : w ≠ ur := (G.ne_of_adj hur_w_adj).symm
    have hw_lt_r : w.val < r := by
      have hw_U := hTU hw_T
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hw_U
      have : w.val ≠ r := fun h => hw_ne_ur (Fin.ext h)
      omega
    have hw_lt_ur : w < ur := hw_lt_r
    have hw_pref : w ∈ prefixVertices r := by
      simp [prefixVertices, hw_lt_r]
    let T₀ := (T.erase ur).erase w
    obtain ⟨M₀, hM₀⟩ := perfectMatching_erase_pair G T ur w hur hw_T M hM huw_M
    have hT0_sub : T₀ ⊆ prefixVertices r := by
      intro x hx
      have hx_ne_ur : x ≠ ur := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hx_T : x ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
      have hx_U := hTU hx_T
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hx_U ⊢
      have : x.val ≠ r := fun h => hx_ne_ur (Fin.ext h)
      omega
    have hw_not_T0 : w ∉ T₀ := Finset.notMem_erase w _
    have hcard_T0 : T₀.card + 2 = T.card := by
      have hw_erase : w ∈ T.erase ur := Finset.mem_erase.mpr ⟨hw_ne_ur, hw_T⟩
      have h1 := Finset.card_erase_add_one hw_erase
      have h2 := Finset.card_erase_add_one hur
      dsimp [T₀]
      omega
    let f := firstNeighbor G ur
    obtain ⟨⟨hf_lt_ur, hf_adj_ur⟩, hf_le_w⟩ := firstNeighbor_spec G ur w hw_lt_ur hur_w_adj.symm
    have hf_pref : f ∈ prefixVertices r := by
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hf_lt_ur
    have hf_dom_ur : ∀ v ∈ prefixVertices r, v ≠ f → G.Adj v ur → G.Adj v f := by
      intro v hv hvf hv_adj
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hv_lt_ur : v < ur := hv
      have hf_le_v : f ≤ v := (firstNeighbor_spec G ur v hv_lt_ur hv_adj).2
      have hf_lt_v : f < v := lt_of_le_of_ne hf_le_v hvf.symm
      exact (obs5 G R ur f hf_lt_ur hf_adj_ur.symm v hf_lt_v hv_lt_ur.le).symm
    by_cases hf_mem : f ∈ insert w T₀
    · have hdom_wT0 : ∀ v ∈ prefixVertices r, v ∉ insert w T₀ → ∃ s ∈ insert w T₀, G.Adj v s := by
        intro v hv hv_not
        have hv_lt_r : v.val < r := by
          simpa [prefixVertices] using hv
        have hv_U1 : v ∈ prefixVertices (r + 1) := by
          simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        have hv_ne_ur : v ≠ ur := by
          intro h; rw [h] at hv_lt_r; exact Nat.lt_irrefl r hv_lt_r
        have hv_not_T : v ∉ T := by
          intro hvT
          apply hv_not
          by_cases hvw : v = w
          · exact hvw ▸ Finset.mem_insert_self w T₀
          · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvw, Finset.mem_erase.mpr ⟨hv_ne_ur, hvT⟩⟩)
        obtain ⟨t, htT, hvt_adj⟩ := hTdom v hv_U1 hv_not_T
        by_cases htur : t = ur
        · subst htur
          have hvf : v ≠ f := fun h => hv_not (h ▸ hf_mem)
          exact ⟨f, hf_mem, hf_dom_ur v hv hvf hvt_adj⟩
        · by_cases htw : t = w
          · exact ⟨w, Finset.mem_insert_self w T₀, htw ▸ hvt_adj⟩
          · exact ⟨t, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨htw, Finset.mem_erase.mpr ⟨htur, htT⟩⟩), hvt_adj⟩
      by_cases hz_ex : ∃ z ∈ prefixVertices r, z ∉ T₀ ∧ G.Adj w z
      · obtain ⟨z, hz_pref, hz_not_T0, hwz_adj⟩ := hz_ex
        let S' := insert z (insert w T₀)
        obtain ⟨M', hM'⟩ := perfectMatching_insert_pair G T₀ z w hz_not_T0 hw_not_T0 hwz_adj.symm M₀ hM₀
        have hS'_paired : PairedDominatesOn G (prefixVertices r) S' := by
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
        exact le_trans (hS.2 S' hS'_paired) hcard_S'
      · have hz_ex' : ∀ z ∈ prefixVertices r, z ∉ T₀ → ¬ G.Adj w z :=
          fun z hz hnot hadj => hz_ex ⟨z, hz, hnot, hadj⟩
        have hT0_paired : PairedDominatesOn G (prefixVertices r) T₀ := by
          refine ⟨hT0_sub, ?_, M₀, hM₀⟩
          intro v hv hvT0
          by_cases hvw : v = w
          · obtain ⟨z, hz_pref, hwz_adj⟩ := exists_neighbor_in_prefix G R hconn r hr (by omega) v hv
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
              exact hz_ex' v hv hvT0 hvs.symm
            · exact ⟨s, hsT0, hvs⟩
        exact le_trans (hS.2 T₀ hT0_paired) (by omega)
    · have hf_ne_w : f ≠ w := fun h => hf_mem (h ▸ Finset.mem_insert_self w T₀)
      have hf_not_T0 : f ∉ T₀ := fun h => hf_mem (Finset.mem_insert_of_mem h)
      have hf_lt_w : f < w := lt_of_le_of_ne hf_le_w hf_ne_w
      have hfw_adj : G.Adj f w := obs5 G R ur f hf_lt_ur hf_adj_ur.symm w hf_lt_w hw_lt_ur.le
      let S' := insert f (insert w T₀)
      obtain ⟨M', hM'⟩ := perfectMatching_insert_pair G T₀ f w hf_not_T0 hw_not_T0 hfw_adj M₀ hM₀
      have hS'_paired : PairedDominatesOn G (prefixVertices r) S' := by
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
          have hv_U1 : v ∈ prefixVertices (r + 1) := by
            simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
            omega
          have hv_ne_ur : v ≠ ur := by
            intro h; rw [h] at hv_lt_r; exact Nat.lt_irrefl r hv_lt_r
          have hv_not_T : v ∉ T := by
            intro hvT
            exact hvT0 (Finset.mem_erase.mpr ⟨hvw, Finset.mem_erase.mpr ⟨hv_ne_ur, hvT⟩⟩)
          obtain ⟨t, htT, hvt_adj⟩ := hTdom v hv_U1 hv_not_T
          by_cases htur : t = ur
          · subst htur
            exact ⟨f, Finset.mem_insert_self f _, hf_dom_ur v hv hvf hvt_adj⟩
          · by_cases htw : t = w
            · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_self w T₀), htw ▸ hvt_adj⟩
            · exact ⟨t, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_erase.mpr ⟨htw, Finset.mem_erase.mpr ⟨htur, htT⟩⟩)), hvt_adj⟩
      have hcard_S' : S'.card ≤ T.card := by
        calc S'.card ≤ (insert w T₀).card + 1 := Finset.card_insert_le f _
          _ ≤ (T₀.card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le w T₀) 1
          _ = T.card := hcard_T0
      exact le_trans (hS.2 S' hS'_paired) hcard_S'
  · have hT_paired_r : PairedDominatesOn G (prefixVertices r) T := by
      refine ⟨?_, ?_, M, hM⟩
      · intro x hx
        have hx_U1 := hTU hx
        have hx_ne_ur : x ≠ ur := fun h => hur (h ▸ hx)
        simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hx_U1 ⊢
        have : x.val ≠ r := fun h => hx_ne_ur (Fin.ext h)
        omega
      · intro v hv hvT
        have hv_lt_r : v.val < r := by simpa [prefixVertices] using hv
        have hv_U1 : v ∈ prefixVertices (r + 1) := by
          simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        exact hTdom v hv_U1 hvT
    exact hS.2 T hT_paired_r
