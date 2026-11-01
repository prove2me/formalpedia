-- Prove2me | solution 1 for CostlySeeding.EdgeQuery.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T05:43:30.323196+00:00
-- url     : https://prove2.me/submissions/e5463336-7260-4f97-b614-4c10918ed8e8

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

open CostlySeeding.EdgeQuery

namespace L3Aux

/-! ### The untruncated PROBE explores the whole percolation component -/

lemma componentSize_le {n : ℕ} (st : ProbeState n) (v : Fin n) : componentSize st v ≤ n := by
  unfold componentSize
  exact (Finset.card_le_univ _).trans (by simp)

lemma pn_spec {n : ℕ} (v : Fin n) (tau : ℕ) (htau : n < tau) (X : Finset (Fin n)) :
    ∀ (ws : List (Fin n)) (st : ProbeState n),
      (probeNeighbors v tau X ws st).explored = st.explored ∧
      (∀ u, u ∈ (probeNeighbors v tau X ws st).vertices ↔ u ∈ st.vertices ∨ (u ∈ ws ∧ u ∉ X)) ∧
      (∀ e, e ∈ (probeNeighbors v tau X ws st).edges ↔
        e ∈ st.edges ∨ ∃ w ∈ ws, w ∉ X ∧ e = s(v, w))
  | [], st => by simp [probeNeighbors]
  | w :: ws, st => by
    have hlt : componentSize st v < tau := lt_of_le_of_lt (componentSize_le st v) htau
    simp only [probeNeighbors, if_pos hlt]
    by_cases hw : w ∈ X
    · simp only [if_pos hw]
      obtain ⟨h1, h2, h3⟩ := pn_spec v tau htau X ws
        (⟨st.vertices, st.edges, st.explored, st.queries + 1⟩ : ProbeState n)
      refine ⟨h1, ?_, ?_⟩
      · intro u; rw [h2 u]; simp only [List.mem_cons]
        constructor
        · rintro (h | ⟨h, h'⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h, h'⟩
        · rintro (h | ⟨h | h, h'⟩)
          · exact Or.inl h
          · subst h; exact absurd hw h'
          · exact Or.inr ⟨h, h'⟩
      · intro e; rw [h3 e]; simp only [List.mem_cons]
        constructor
        · rintro (h | ⟨w', hw', h', he⟩)
          · exact Or.inl h
          · exact Or.inr ⟨w', Or.inr hw', h', he⟩
        · rintro (h | ⟨w', hw' | hw', h', he⟩)
          · exact Or.inl h
          · subst hw'; exact absurd hw h'
          · exact Or.inr ⟨w', hw', h', he⟩
    · simp only [if_neg hw]
      obtain ⟨h1, h2, h3⟩ := pn_spec v tau htau X ws
        (⟨insert w st.vertices, insert (s(v, w)) st.edges, st.explored, st.queries + 1⟩ :
          ProbeState n)
      refine ⟨h1, ?_, ?_⟩
      · intro u; rw [h2 u]; simp only [Finset.mem_insert, List.mem_cons]
        constructor
        · rintro ((h | h) | ⟨h, h'⟩)
          · subst h; exact Or.inr ⟨Or.inl rfl, hw⟩
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h, h'⟩
        · rintro (h | ⟨h | h, h'⟩)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨h, h'⟩
      · intro e; rw [h3 e]; simp only [Finset.mem_insert, List.mem_cons]
        constructor
        · rintro ((h | h) | ⟨w', hw', h', he⟩)
          · exact Or.inr ⟨w, Or.inl rfl, hw, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨w', Or.inr hw', h', he⟩
        · rintro (h | ⟨w', hw' | hw', h', he⟩)
          · exact Or.inl (Or.inr h)
          · subst hw'; exact Or.inl (Or.inl he)
          · exact Or.inr ⟨w', hw', h', he⟩

lemma edgeCoin_symm {n : ℕ} (s : ProbeSeed n) (u w : Fin n) : edgeCoin s u w = edgeCoin s w u := by
  unfold edgeCoin
  rcases lt_trichotomy u w with h | h | h
  · rw [if_pos h.le, if_neg (not_le.2 h)]
  · subst h; rfl
  · rw [if_neg (not_le.2 h), if_pos h.le]

lemma chooseRank_mem {n : ℕ} (e : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (h : A.Nonempty) :
    chooseRank e A h ∈ A := by
  unfold chooseRank
  obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 (Finset.min'_mem (A.image e) (h.image e))
  rw [← hae]; simpa using ha

lemma mem_orderedNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : ProbeSeed n) (X : Finset (Fin n)) (v w : Fin n) :
    w ∈ orderedNeighbors G s X v ↔
      G.Adj v w ∧ (if w ∈ X then s.redo v w = true else edgeCoin s v w = true) := by
  unfold orderedNeighbors
  rw [List.mem_mergeSort, Finset.mem_toList, Finset.mem_filter]
  simp

/-- Invariant of the untruncated exploration. -/
def Inv {n : ℕ} (G : SimpleGraph (Fin n)) (s : ProbeSeed n) (V : Finset (Fin n))
    (st : ProbeState n) : Prop :=
  (∀ u w, s(u, w) ∈ st.edges → G.Adj u w ∧ edgeCoin s u w = true) ∧
  st.explored ⊆ st.vertices ∧
  (∀ u ∈ st.explored, ∀ w, G.Adj u w → edgeCoin s u w = true → s(u, w) ∈ st.edges) ∧
  V ⊆ st.vertices ∧
  (∀ u w, s(u, w) ∈ st.edges → u ∈ st.vertices ∧ w ∈ st.vertices)

lemma loop_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (tau : ℕ)
    (htau : n < tau) (s : ProbeSeed n) (V : Finset (Fin n)) :
    ∀ (fuel : ℕ) (st : ProbeState n), Inv G s V st → n ≤ st.explored.card + fuel →
      Inv G s V (probeLoop G tau s fuel st) ∧
        (probeLoop G tau s fuel st).vertices ⊆ (probeLoop G tau s fuel st).explored
  | 0, st, hI, hc => by
    refine ⟨hI, ?_⟩
    simp only [probeLoop]
    have : st.explored = Finset.univ := by
      apply Finset.eq_univ_of_card
      have := Finset.card_le_univ st.explored
      rw [Fintype.card_fin] at this ⊢; omega
    rw [this]; exact Finset.subset_univ _
  | fuel + 1, st, hI, hc => by
    simp only [probeLoop]
    split_ifs with hU
    · -- one exploration step
      set v := chooseRank (s.pick (Fin.ofNat (n + 1) (n - (fuel + 1)))) (st.vertices \ st.explored) hU
        with hv
      have hvU : v ∈ st.vertices \ st.explored := chooseRank_mem _ _ hU
      rw [Finset.mem_sdiff] at hvU
      set X := insert v st.explored with hX
      set st0 : ProbeState n := { st with explored := X } with hst0
      obtain ⟨h1, h2, h3⟩ := pn_spec v tau htau X (orderedNeighbors G s X v) st0
      have e1 : st0.explored = X := rfl
      have e2 : st0.vertices = st.vertices := rfl
      have e3 : st0.edges = st.edges := rfl
      rw [e1] at h1
      simp only [e2] at h2
      simp only [e3] at h3
      apply loop_spec G tau htau s V fuel _ ?_ ?_
      · obtain ⟨I1, I2, I3, I4, I5⟩ := hI
        have hnb : ∀ w, w ∉ X → (w ∈ orderedNeighbors G s X v ↔ G.Adj v w ∧ edgeCoin s v w = true) := by
          intro w hw
          rw [mem_orderedNeighbors, if_neg hw]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro u w he
          rw [h3] at he
          rcases he with he | ⟨w', hw', hw'X, he⟩
          · exact I1 u w he
          · have := (hnb w' hw'X).1 hw'
            rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact this
            · exact ⟨this.1.symm, by rw [edgeCoin_symm]; exact this.2⟩
        · intro u hu
          rw [h1] at hu
          rw [h2]; left
          rw [hX, Finset.mem_insert] at hu
          rcases hu with rfl | hu
          · exact hvU.1
          · exact I2 hu
        · intro u hu w hadj hcoin
          rw [h1, hX, Finset.mem_insert] at hu
          rw [h3]
          rcases hu with huv | hu
          · rw [huv] at hadj hcoin ⊢
            by_cases hwX : w ∈ X
            · left
              rw [hX, Finset.mem_insert] at hwX
              rcases hwX with hwv | hwX
              · rw [hwv] at hadj; exact absurd hadj G.irrefl
              · have := I3 w hwX v hadj.symm (by rw [edgeCoin_symm]; exact hcoin)
                rw [Sym2.eq_swap]; exact this
            · right; exact ⟨w, (hnb w hwX).2 ⟨hadj, hcoin⟩, hwX, rfl⟩
          · left; exact I3 u hu w hadj hcoin
        · intro u hu; rw [h2]; left; exact I4 hu
        · intro u w he
          rw [h3] at he
          rw [h2, h2]
          rcases he with he | ⟨w', hw', hw'X, he⟩
          · exact ⟨Or.inl (I5 u w he).1, Or.inl (I5 u w he).2⟩
          · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨Or.inl hvU.1, Or.inr ⟨hw', hw'X⟩⟩
            · exact ⟨Or.inr ⟨hw', hw'X⟩, Or.inl hvU.1⟩
      · rw [h1, hX, Finset.card_insert_of_notMem hvU.2]; omega
    · refine ⟨hI, ?_⟩
      intro u hu
      by_contra h
      exact hU ⟨u, Finset.mem_sdiff.2 ⟨hu, h⟩⟩

/-- The coin of an unordered pair. -/
def coinE {n : ℕ} (s : ProbeSeed n) : Sym2 (Fin n) → Bool :=
  Sym2.lift ⟨fun u w => edgeCoin s u w, fun u w => edgeCoin_symm s u w⟩

/-- The open edges of the percolation encoded by the coins of a seed. -/
def Aof {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ProbeSeed n) :
    Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter (fun e => coinE s e = true)

lemma adj_Aof {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ProbeSeed n)
    (u w : Fin n) :
    (SimpleGraph.fromEdgeSet (Aof G s : Set (Sym2 (Fin n)))).Adj u w ↔
      G.Adj u w ∧ edgeCoin s u w = true := by
  rw [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe, Aof, Finset.mem_filter,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  have hc : coinE s s(u, w) = edgeCoin s u w := rfl
  rw [hc]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, G.ne_of_adj h1⟩

lemma reach_final {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ProbeSeed n)
    (V : Finset (Fin n)) (v : Fin n) (hv : v ∈ V) (t : Fin n) :
    (SimpleGraph.fromEdgeSet ((probeCopy G V (n + 1) s).1 : Set (Sym2 (Fin n)))).Reachable v t ↔
      (SimpleGraph.fromEdgeSet (Aof G s : Set (Sym2 (Fin n)))).Reachable v t := by
  set r := probeLoop G (n + 1) s n
    (⟨V, ∅, ∅, 0⟩ : ProbeState n) with hr
  have hinit : Inv G s V (⟨V, ∅, ∅, 0⟩ : ProbeState n) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u w h; simp at h
    · intro u h; simp at h
    · intro u h; simp at h
    · exact le_refl _
    · intro u w h; simp at h
  obtain ⟨⟨I1, I2, I3, I4, I5⟩, hcov⟩ :=
    loop_spec G (n + 1) (Nat.lt_succ_self n) s V n _ hinit (by simp)
  have hE : (probeCopy G V (n + 1) s).1 = r.edges := rfl
  rw [hE]
  constructor
  · intro h
    apply h.mono
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    rw [adj_Aof]
    exact I1 a b hab.1
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    have key : ∀ a, Relation.ReflTransGen
        (SimpleGraph.fromEdgeSet (Aof G s : Set (Sym2 (Fin n)))).Adj a t →
        a ∈ r.vertices →
        (SimpleGraph.fromEdgeSet (r.edges : Set (Sym2 (Fin n)))).Reachable a t := by
      intro a hat
      induction hat using Relation.ReflTransGen.head_induction_on with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | head hadj _ ih =>
        rename_i a b _
        intro ha
        rw [adj_Aof] at hadj
        have hab : s(a, b) ∈ r.edges := I3 a (hcov ha) b hadj.1 hadj.2
        have hb : b ∈ r.vertices := (I5 a b hab).2
        have hadj' : (SimpleGraph.fromEdgeSet (r.edges : Set (Sym2 (Fin n)))).Adj a b := by
          rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨hab, G.ne_of_adj hadj.1⟩
        exact (SimpleGraph.Adj.reachable hadj').trans (ih hb)
    exact key v h (I4 hv)

lemma Y_uncut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ProbeSeed n)
    (V : Finset (Fin n)) (v : Fin n) (hv : v ∈ V) (S : Finset (Fin n)) :
    Y (probeCopy G V (n + 1) s).1 v S = Y (Aof G s) v S := by
  unfold Y
  congr 1
  apply propext
  constructor
  · rintro ⟨t, ht, h⟩; exact ⟨t, ht, (reach_final G s V v hv t).1 h⟩
  · rintro ⟨t, ht, h⟩; exact ⟨t, ht, (reach_final G s V v hv t).2 h⟩

/-! ### The coins realise independent bond percolation -/

def seedEquiv (n : ℕ) : ProbeSeed n ≃
    (Fin (n + 1) → Equiv.Perm (Fin n)) ×
      (Fin n → Equiv.Perm (Fin n)) ×
      (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool) where
  toFun s := (s.pick, s.order, s.coin, s.redo)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv := by intro s; cases s; rfl
  right_inv := by intro t; rcases t with ⟨a, b, c, d⟩; rfl

lemma sum_bitW (p : ℝ) : ∑ b : Bool, bitW p b = 1 := by
  simp [bitW]

lemma bitW_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : 0 ≤ bitW p b := by
  cases b <;> simp [bitW] <;> linarith

lemma sum_bits (n : ℕ) (p : ℝ) :
    ∑ c : Fin n → Fin n → Bool, ∏ v : Fin n, ∏ w : Fin n, bitW p (c v w) = 1 := by
  rw [← Fintype.prod_sum (fun (v : Fin n) (r : Fin n → Bool) => ∏ w : Fin n, bitW p (r w))]
  apply Finset.prod_eq_one
  intro v _
  rw [← Fintype.prod_sum (fun (w : Fin n) (b : Bool) => bitW p b)]
  apply Finset.prod_eq_one
  intro w _
  exact sum_bitW p

lemma sum_perms (m n : ℕ) :
    ∑ _f : Fin m → Equiv.Perm (Fin n),
      ∏ _t : Fin m, (1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) = 1 := by
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.prod_const, Finset.card_univ, Fintype.card_fun]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [div_pow, one_pow, mul_one_div, div_self (pow_ne_zero _ hc.ne')]

lemma sum_four {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → ℝ) (g : B → ℝ) (h : C → ℝ) (k : D → ℝ) :
    ∑ x : A × B × C × D, f x.1 * g x.2.1 * h x.2.2.1 * k x.2.2.2 =
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, k d) := by
  simp only [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]


/-- `Aof` only depends on the coin matrix. -/
def AofC {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Fin n → Fin n → Bool) :
    Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter (fun e => Sym2.lift
    ⟨fun u w => if u ≤ w then c u w else c w u, fun u w => by
      show (if u ≤ w then c u w else c w u) = (if w ≤ u then c w u else c u w)
      rcases lt_trichotomy u w with h | h | h
      · rw [if_pos h.le, if_neg (not_le.2 h)]
      · subst h; rfl
      · rw [if_neg (not_le.2 h), if_pos h.le]⟩ e = true)

lemma Aof_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ProbeSeed n) :
    Aof G s = AofC G s.coin := rfl

lemma AofC_eq_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Fin n → Bool) (A : Finset (Sym2 (Fin n))) (hA : A ⊆ G.edgeFinset) :
    AofC G c = A ↔ ∀ v w, v < w → G.Adj v w → c v w = decide (s(v, w) ∈ A) := by
  have hmem : ∀ v w, s(v, w) ∈ AofC G c ↔ G.Adj v w ∧ (if v ≤ w then c v w else c w v) = true := by
    intro v w
    unfold AofC
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    rfl
  constructor
  · intro h v w hvw hadj
    have := hmem v w
    rw [h, if_pos hvw.le] at this
    by_cases hA' : s(v, w) ∈ A
    · simp only [hA', decide_true]; exact (this.1 hA').2
    · simp only [hA', decide_false]
      by_contra hc
      exact hA' (this.2 ⟨hadj, by simpa using hc⟩)
  · intro h
    ext e
    induction e using Sym2.ind with
    | h v w =>
    rw [hmem]
    by_cases hadj : G.Adj v w
    · rcases lt_trichotomy v w with hvw | hvw | hvw
      · rw [if_pos hvw.le, h v w hvw hadj]; simp [hadj]
      · subst hvw; exact absurd hadj G.irrefl
      · rw [if_neg (not_le.2 hvw), h w v hvw hadj.symm, Sym2.eq_swap]; simp [hadj]
    · simp only [hadj, false_and, false_iff]
      intro hA'
      have := hA hA'
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      exact hadj this

lemma indicator_prod {n : ℕ} (P : Fin n → Fin n → Prop) [∀ v w, Decidable (P v w)] :
    (if ∀ v w, P v w then (1 : ℝ) else 0) =
      ∏ v : Fin n, ∏ w : Fin n, (if P v w then (1 : ℝ) else 0) := by
  by_cases h : ∀ v w, P v w
  · rw [if_pos h]
    symm
    apply Finset.prod_eq_one; intro v _
    apply Finset.prod_eq_one; intro w _
    rw [if_pos (h v w)]
  · rw [if_neg h]
    push Not at h
    obtain ⟨v, w, hvw⟩ := h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    apply Finset.prod_eq_zero (Finset.mem_univ w)
    rw [if_neg hvw]

lemma prod_pairs_eq_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : Sym2 (Fin n) → ℝ) :
    ∏ v : Fin n, ∏ w : Fin n, (if v < w ∧ G.Adj v w then g s(v, w) else 1) =
      ∏ e ∈ G.edgeFinset, g e := by
  rw [← Finset.prod_product' (s := Finset.univ) (t := Finset.univ)
    (f := fun v w => if v < w ∧ G.Adj v w then g s(v, w) else 1)]
  rw [← Finset.prod_filter]
  have himg : ((Finset.univ ×ˢ Finset.univ).filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ G.Adj x.1 x.2)).image
      (fun x => s(x.1, x.2)) = G.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Prod.exists]
    constructor
    · rintro ⟨x, y, ⟨_, hxy⟩, he⟩
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy
      · exact hxy.symm
    · intro hab
      rcases lt_trichotomy a b with h | h | h
      · exact ⟨a, b, ⟨h, hab⟩, rfl⟩
      · subst h; exact absurd hab G.irrefl
      · exact ⟨b, a, ⟨h, hab.symm⟩, Sym2.eq_swap⟩
  rw [← himg, Finset.prod_image]
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
  simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Set.mem_setOf_eq] at hab hcd
  simp only at he
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd (hab.1.trans hcd.1) (lt_irrefl _)

lemma coin_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℝ)
    (A : Finset (Sym2 (Fin n))) (hA : A ⊆ G.edgeFinset) :
    ∑ c : Fin n → Fin n → Bool, (∏ v : Fin n, ∏ w : Fin n, bitW p (c v w)) *
      (if AofC G c = A then (1 : ℝ) else 0) = percW G p A := by
  have hind : ∀ c : Fin n → Fin n → Bool, (if AofC G c = A then (1 : ℝ) else 0) =
      ∏ v : Fin n, ∏ w : Fin n,
        (if (v < w → G.Adj v w → c v w = decide (s(v, w) ∈ A)) then (1 : ℝ) else 0) := by
    intro c
    rw [← indicator_prod]
    congr 1
    exact propext (AofC_eq_iff G c A hA)
  simp only [hind, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (v : Fin n) (r : Fin n → Bool) => ∏ w : Fin n, bitW p (r w) *
    (if (v < w → G.Adj v w → r w = decide (s(v, w) ∈ A)) then (1 : ℝ) else 0))]
  have hrow : ∀ v : Fin n, ∑ r : Fin n → Bool, ∏ w : Fin n, bitW p (r w) *
      (if (v < w → G.Adj v w → r w = decide (s(v, w) ∈ A)) then (1 : ℝ) else 0) =
      ∏ w : Fin n, (if v < w ∧ G.Adj v w then (if s(v, w) ∈ A then p else 1 - p) else 1) := by
    intro v
    rw [← Fintype.prod_sum (fun (w : Fin n) (b : Bool) => bitW p b *
      (if (v < w → G.Adj v w → b = decide (s(v, w) ∈ A)) then (1 : ℝ) else 0))]
    apply Finset.prod_congr rfl
    intro w _
    rw [Fintype.sum_bool]
    by_cases h : v < w ∧ G.Adj v w
    · rw [if_pos h]
      by_cases hA' : s(v, w) ∈ A
      · simp [h.1, h.2, hA', bitW]
      · simp [h.1, h.2, hA', bitW]
    · rw [if_neg h]
      have : (v < w → G.Adj v w → ∀ b : Bool, b = decide (s(v, w) ∈ A)) ∨ True := Or.inr trivial
      by_cases h1 : v < w
      · have h2 : ¬ G.Adj v w := fun h2 => h ⟨h1, h2⟩
        simp [h1, h2, bitW]
      · simp [h1, bitW]
  simp only [hrow]
  rw [prod_pairs_eq_edges G (fun e => if e ∈ A then p else 1 - p)]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  unfold percW
  rw [if_pos hA]
  have h1 : G.edgeFinset.filter (fun e => e ∈ A) = A := by
    ext e; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩
  have h2 : (G.edgeFinset.filter (fun e => ¬ e ∈ A)).card = G.edgeFinset.card - A.card := by
    rw [Finset.filter_not, h1, Finset.card_sdiff_of_subset hA]
  rw [h1, h2]

lemma sum_seedW (n : ℕ) (p : ℝ) : ∑ s : ProbeSeed n, seedW p s = 1 := by
  rw [← (seedEquiv n).symm.sum_comp]
  have := sum_four
    (fun (a : Fin (n + 1) → Equiv.Perm (Fin n)) =>
      ∏ _t : Fin (n + 1), (1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)))
    (fun (b : Fin n → Equiv.Perm (Fin n)) =>
      ∏ _t : Fin n, (1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)))
    (fun (c : Fin n → Fin n → Bool) => ∏ v : Fin n, ∏ w : Fin n, bitW p (c v w))
    (fun (c : Fin n → Fin n → Bool) => ∏ v : Fin n, ∏ w : Fin n, bitW p (c v w))
  simp only [sum_perms, sum_bits, mul_one] at this
  rw [← this]
  rfl

lemma seedW_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ProbeSeed n) :
    0 ≤ seedW p s := by
  unfold seedW
  have h1 : ∀ v w : Fin n, 0 ≤ bitW p (s.coin v w) := fun _ _ => bitW_nonneg p hp0 hp1 _
  have h2 : ∀ v w : Fin n, 0 ≤ bitW p (s.redo v w) := fun _ _ => bitW_nonneg p hp0 hp1 _
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  · exact Finset.prod_nonneg fun _ _ => by positivity
  · exact Finset.prod_nonneg fun _ _ => by positivity
  · exact Finset.prod_nonneg fun v _ => Finset.prod_nonneg fun w _ => h1 v w
  · exact Finset.prod_nonneg fun v _ => Finset.prod_nonneg fun w _ => h2 v w

lemma sum_ssW (n T : ℕ) (p : ℝ) :
    ∑ ss : Fin T → ProbeSeed n, ∏ i : Fin T, seedW p (ss i) = 1 := by
  rw [← Fintype.sum_pow, sum_seedW, one_pow]

lemma ssW_nonneg (n T : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ss : Fin T → ProbeSeed n) :
    0 ≤ ∏ i : Fin T, seedW p (ss i) :=
  Finset.prod_nonneg fun i _ => seedW_nonneg n p hp0 hp1 (ss i)


lemma seed_pushforward {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℝ)
    (A : Finset (Sym2 (Fin n))) (hA : A ⊆ G.edgeFinset) :
    ∑ s : ProbeSeed n, seedW p s * (if Aof G s = A then (1 : ℝ) else 0) = percW G p A := by
  rw [← (seedEquiv n).symm.sum_comp]
  have := sum_four
    (fun (a : Fin (n + 1) → Equiv.Perm (Fin n)) =>
      ∏ _t : Fin (n + 1), (1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)))
    (fun (b : Fin n → Equiv.Perm (Fin n)) =>
      ∏ _t : Fin n, (1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)))
    (fun (c : Fin n → Fin n → Bool) => (∏ v : Fin n, ∏ w : Fin n, bitW p (c v w)) *
      (if AofC G c = A then (1 : ℝ) else 0))
    (fun (c : Fin n → Fin n → Bool) => ∏ v : Fin n, ∏ w : Fin n, bitW p (c v w))
  simp only [sum_perms, sum_bits, coin_sum G p A hA, mul_one, one_mul] at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro x _
  simp only [seedW, seedEquiv, Equiv.coe_fn_symm_mk, Aof_eq]
  ac_rfl

lemma seed_expect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℝ)
    (F : Finset (Sym2 (Fin n)) → ℝ) :
    ∑ s : ProbeSeed n, seedW p s * F (Aof G s) =
      ∑ A ∈ G.edgeFinset.powerset, percW G p A * F A := by
  have h1 : ∀ s : ProbeSeed n, seedW p s * F (Aof G s) =
      ∑ A ∈ G.edgeFinset.powerset, seedW p s * (if Aof G s = A then (1 : ℝ) else 0) * F A := by
    intro s
    have hmem : Aof G s ∈ G.edgeFinset.powerset :=
      Finset.mem_powerset.2 (Finset.filter_subset _ _)
    rw [Finset.sum_eq_single (Aof G s)]
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; simp
    · intro h; exact absurd hmem h
  simp only [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Finset.sum_mul, seed_pushforward G p A (Finset.mem_powerset.1 hA)]

lemma Y_expect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℝ)
    (v : Fin n) (S : Finset (Fin n)) :
    ∑ s : ProbeSeed n, seedW p s * Y (Aof G s) v S = phi G p v S := by
  rw [seed_expect G p (fun A => Y A v S)]
  unfold phi Y
  apply Finset.sum_congr rfl
  intro A _
  congr 1
  congr 1
  apply propext
  constructor
  · rintro ⟨t, ht, h⟩; exact ⟨t, ht, h.symm⟩
  · rintro ⟨t, ht, h⟩; exact ⟨t, ht, h.symm⟩

/-! ### Hoeffding over independent copies -/

lemma hoeffding_weighted {α : Type} [Fintype α] (w : α → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) (y : α → ℝ) (a b : ℝ) (hy : ∀ x, a ≤ y x ∧ y x ≤ b)
    (h0 : ∑ x, w x * y x = 0) (t : ℝ) :
    ∑ x, w x * Real.exp (t * y x) ≤ Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  classical
  letI : MeasurableSpace α := ⊤
  have hsum : ∑ x, ENNReal.ofReal (w x) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hw0 x), hw1, ENNReal.ofReal_one]
  set pm := PMF.ofFintype (fun x => ENNReal.ofReal (w x)) hsum with hpm
  set μ := pm.toMeasure with hμ
  have hint : ∀ g : α → ℝ, ∫ x, g x ∂μ = ∑ x, w x * g x := by
    intro g
    rw [hμ, PMF.integral_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [hpm, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hw0 x), smul_eq_mul]
  have hmean : ∫ x, y x ∂μ = 0 := by rw [hint]; exact h0
  have hb : ∀ᵐ x ∂μ, y x ∈ Set.Icc a b :=
    Filter.Eventually.of_forall fun x => ⟨(hy x).1, (hy x).2⟩
  have hsg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (Measurable.aemeasurable (measurable_from_top (f := y))) hb hmean
  have hm := hsg.mgf_le t
  rw [ProbabilityTheory.mgf, hint] at hm
  have hc : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) * t ^ 2 / 2 = (b - a) ^ 2 * t ^ 2 / 8 := by
    push_cast
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    ring
  rw [hc] at hm
  exact hm

lemma prod_copies {α : Type} [Fintype α] (T : ℕ) (f : α → ℝ) :
    ∑ ss : Fin T → α, ∏ i, f (ss i) = (∑ x, f x) ^ T := by
  rw [Fintype.sum_pow]

lemma copies_upper {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : ℕ) (hT : 0 < T)
    (g : ProbeSeed n → ℝ) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (r : ℝ) (hr : 0 < r) :
    ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) *
      (if T * r ≤ ∑ i, (g (ss i) - ∑ x, seedW p x * g x) then (1 : ℝ) else 0) ≤
      Real.exp (-2 * T * r ^ 2) := by
  set μ := ∑ x, seedW p x * g x with hμ
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  set t := 4 * r with ht
  have ht0 : 0 < t := by positivity
  have hw0 := seedW_nonneg n p hp0 hp1
  have hw1 := sum_seedW n p
  -- one-copy MGF
  have h1 := hoeffding_weighted (seedW p) hw0 hw1 (fun x => g x - μ) (-μ) (1 - μ)
    (fun x => ⟨by linarith [(hg x).1], by linarith [(hg x).2]⟩) (by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, hμ, sub_self]) t
  have hlen : (1 - μ - -μ) ^ 2 * t ^ 2 / 8 = t ^ 2 / 8 := by ring
  rw [hlen] at h1
  calc ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) *
        (if T * r ≤ ∑ i, (g (ss i) - μ) then (1 : ℝ) else 0)
      ≤ ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) *
        (Real.exp (t * ∑ i, (g (ss i) - μ)) * Real.exp (-(t * (T * r)))) := by
        apply Finset.sum_le_sum
        intro ss _
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => hw0 _)
        split_ifs with h
        · rw [← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        · positivity
    _ = (∑ x, seedW p x * Real.exp (t * (g x - μ))) ^ T * Real.exp (-(t * (T * r))) := by
        rw [← prod_copies, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ss _
        rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
        ring
    _ ≤ (Real.exp (t ^ 2 / 8)) ^ T * Real.exp (-(t * (T * r))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact pow_le_pow_left₀ (Finset.sum_nonneg fun x _ =>
          mul_nonneg (hw0 x) (Real.exp_pos _).le) h1 T
    _ = Real.exp (-2 * T * r ^ 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        rw [ht]; ring

lemma copies_lower {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : ℕ) (hT : 0 < T)
    (g : ProbeSeed n → ℝ) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (r : ℝ) (hr : 0 < r) :
    ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) *
      (if T * r ≤ ∑ i, ((∑ x, seedW p x * g x) - g (ss i)) then (1 : ℝ) else 0) ≤
      Real.exp (-2 * T * r ^ 2) := by
  have h := copies_upper p hp0 hp1 T hT (fun x => 1 - g x)
    (fun x => ⟨by linarith [(hg x).2], by linarith [(hg x).1]⟩) r hr
  have hw1 := sum_seedW n p
  have hμ : ∑ x, seedW p x * (1 - g x) = 1 - ∑ x, seedW p x * g x := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hw1]
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro ss _
  have hs : ∑ i, ((∑ x, seedW p x * g x) - g (ss i)) =
      ∑ i, ((1 - g (ss i)) - ∑ x, seedW p x * (1 - g x)) := by
    rw [hμ]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hs]

/-! ### Numerics -/

lemma log_five : (1.594 : ℝ) < Real.log 5 := by
  have h2 := Real.log_two_gt_d9
  have h : (2 : ℝ) ^ 23 < 5 ^ 10 := by norm_num
  have := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith

set_option maxHeartbeats 1000000 in
lemma num3 (n k : ℕ) (hk : 1 ≤ k) (hn : 5 ≤ n) (eps δ ρ : ℝ) (heps : 0 < eps)
    (hδ : 2 * Real.log n ≤ δ) (hρpar : rhoPar n k eps δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (m : ℕ) (hm1 : (n : ℝ) * ρ ≤ m) (hm2 : (m : ℝ) < n * ρ + 1) (T : ℕ)
    (hT : TPar n k eps δ ≤ T) (hr1 : eps * ρ * n / m < 1) :
    (m : ℝ) * (n.choose k : ℝ) * (2 * Real.exp (-2 * T * (eps * ρ * n / m) ^ 2)) ≤
      Real.exp (-δ) := by
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL5 : (1.594 : ℝ) < Real.log n := by
    have := Real.log_le_log (by norm_num) hnR
    linarith [log_five]
  set L := Real.log n with hL
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hδL : 2 * L * L ≤ δ * k * L := by
    have h0 : 0 ≤ L := by linarith
    have : 2 * L ≤ δ * k := by
      have : δ ≤ δ * k := le_mul_of_one_le_right (by linarith) hkR
      linarith
    exact mul_le_mul_of_nonneg_right this h0
  set D := δ * k * L + Real.log 2 with hD
  have hD5 : (5.3 : ℝ) ≤ D := by nlinarith
  set x := (n : ℝ) * ρ with hx
  have hρ' : (2 + eps) * D ≤ 2 * eps ^ 2 * x := by
    have h := hρpar
    unfold rhoPar at h
    rw [div_le_iff₀ (by positivity)] at h
    rw [hx]; linarith
  have hx0 : 0 < x := by
    have : 0 < (2 + eps) * D := by positivity
    by_contra h; push Not at h
    have : 2 * eps ^ 2 * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hx0 hm1
  have hex : eps * x < m := by
    have : eps * ρ * n = eps * x := by rw [hx]; ring
    rw [this, div_lt_one hm0] at hr1; exact hr1
  -- x ≥ 5
  have hx5 : 5 ≤ x := by
    by_contra h
    push Not at h
    rcases le_or_gt eps 1 with he1 | he1
    · have : 2 * eps ^ 2 * x ≤ 2 * x := by
        have : eps ^ 2 ≤ 1 := by nlinarith
        nlinarith
      nlinarith
    · -- x (eps - 1) < 1
      have h1 : x * (eps - 1) < 1 := by nlinarith
      have h2 : (2 + eps) * 5.3 ≤ 2 * eps ^ 2 * x := by nlinarith
      nlinarith
  -- ratio x/m ≥ 5/6
  have hratio : (5 / 6 : ℝ) ≤ x / m := by
    rw [le_div_iff₀ hm0]; linarith
  have hTlow : 3 * (δ + Real.log 2) * (k + 1) * L / eps ^ 2 ≤ T := by
    have := Nat.le_ceil (3 * (δ + Real.log 2) * (k + 1) * Real.log n / eps ^ 2)
    have hT' : ((TPar n k eps δ : ℕ) : ℝ) ≤ T := by exact_mod_cast hT
    unfold TPar at hT'
    linarith
  set r := eps * ρ * n / m with hr
  have hrx : r = eps * (x / m) := by rw [hr, hx]; ring
  clear_value r x D L
  have hexpo : 2 * (δ + Real.log 2) * (k + 1) ≤ 2 * T * r ^ 2 := by
    have hA : 0 < δ + Real.log 2 := by linarith
    have h1 : 3 * (δ + Real.log 2) * (k + 1) * L ≤ T * eps ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hTlow; exact hTlow
    have h2 : (25 / 36 : ℝ) ≤ (x / m) ^ 2 := by nlinarith
    have h3 : T * r ^ 2 = T * eps ^ 2 * (x / m) ^ 2 := by rw [hrx]; ring
    have h4 : 3 * (δ + Real.log 2) * (k + 1) * L * (25 / 36) ≤ T * eps ^ 2 * (x / m) ^ 2 := by
      apply mul_le_mul h1 h2 (by norm_num) (by positivity)
    have h5 : (δ + Real.log 2) * (k + 1) ≤ 3 * (δ + Real.log 2) * (k + 1) * L * (25 / 36) := by
      have : 0 ≤ (δ + Real.log 2) * (k + 1) := by positivity
      nlinarith
    linarith only [h3, h4, h5]
  have hK : δ + Real.log 2 + (k + 1) * L ≤ 2 * (δ + Real.log 2) * (k + 1) := by
    have : (k + 1) * L ≤ (k + 1) * (δ + Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have hA : 0 ≤ δ + Real.log 2 := by linarith
    have : (δ + Real.log 2) * 1 ≤ (δ + Real.log 2) * (k + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hA
    linarith
  have hmn : (m : ℝ) ≤ n := by
    have : (n : ℝ) * ρ ≤ n * 1 := mul_le_mul_of_nonneg_left hρ1 hnpos.le
    have hmn' : m ≤ n := by
      have : (m : ℝ) < n + 1 := by linarith
      exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
    exact_mod_cast hmn'
  have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow n k
  have hnk : Real.exp ((k + 1) * L) = (n : ℝ) ^ (k + 1) := by
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul, hL,
      Real.exp_log hnpos]
  have hfinal : (n : ℝ) * (n : ℝ) ^ k * (2 * Real.exp (-(δ + Real.log 2 + (k + 1) * L))) =
      Real.exp (-δ) := by
    rw [show -(δ + Real.log 2 + (k + 1) * L) = -δ + (-Real.log 2 + -((k + 1) * L)) by ring,
      Real.exp_add, Real.exp_add, Real.exp_neg (Real.log 2), Real.exp_neg ((k + 1) * L), hnk,
      Real.exp_log (by norm_num)]
    have : (0 : ℝ) < (n : ℝ) ^ (k + 1) := by positivity
    field_simp
    ring
  calc (m : ℝ) * (n.choose k : ℝ) * (2 * Real.exp (-2 * T * r ^ 2))
      ≤ (n : ℝ) * (n : ℝ) ^ k * (2 * Real.exp (-(δ + Real.log 2 + (k + 1) * L))) := by
        apply mul_le_mul (mul_le_mul hmn hchoose (by positivity) (by positivity)) _
          (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.2
        linarith
    _ = Real.exp (-δ) := hfinal

end L3Aux

open L3Aux

lemma percW_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset (Sym2 (Fin n))) :
    0 ≤ percW G p A := by
  unfold percW
  split_ifs
  · exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  · exact le_refl _

lemma sum_percW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) : ∑ A ∈ G.edgeFinset.powerset, percW G p A = 1 := by
  have h : ∀ A ∈ G.edgeFinset.powerset,
      percW G p A = p ^ A.card * (1 - p) ^ (G.edgeFinset.card - A.card) := by
    intro A hA
    unfold percW
    rw [if_pos (Finset.mem_powerset.1 hA)]
  rw [Finset.sum_congr rfl h, Finset.sum_pow_mul_eq_add_pow]
  simp

lemma phi_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) (S : Finset (Fin n)) :
    0 ≤ phi G p v S := by
  unfold phi
  apply Finset.sum_nonneg
  intro A _
  apply mul_nonneg (percW_nonneg G p hp0 hp1 A)
  split_ifs <;> norm_num

lemma phi_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) (S : Finset (Fin n)) :
    phi G p v S ≤ 1 := by
  unfold phi
  calc _ ≤ ∑ A ∈ G.edgeFinset.powerset, percW G p A := by
        apply Finset.sum_le_sum
        intro A _
        have := percW_nonneg G p hp0 hp1 A
        split_ifs <;> simp [this]
    _ = 1 := sum_percW G p


lemma Y_bounds {n : ℕ} (E : Finset (Sym2 (Fin n))) (v : Fin n) (S : Finset (Fin n)) :
    0 ≤ Y E v S ∧ Y E v S ≤ 1 := by
  unfold Y; split_ifs <;> norm_num

lemma phi_eq_mean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℝ)
    (v : Fin n) (S : Finset (Fin n)) :
    phi G p v S = ∑ x : ProbeSeed n, seedW p x * Y (Aof G x) v S := (Y_expect G p v S).symm

theorem solution (n k T : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (eps delta rho : ℝ) (heps : 0 < eps) (hdelta : 2 * Real.log n ≤ delta)
    (hrho0 : 0 < rho) (hrhoPar : rhoPar n k eps delta ≤ rho)
    (hrho1 : rho ≤ 1) (hT : TPar n k eps delta ≤ T)
    (Vrho : Finset (Fin n)) (hV : Vrho.card = Nat.ceil ((n : ℝ) * rho)) :
    1 - Real.exp (-delta) ≤
      seedEventProb (T := T) p (fun ss =>
        ∀ S : Finset (Fin n), S.card = k →
          |GamUncut G Vrho rho ss S - GamRho G p Vrho rho S| ≤ eps * n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hTpos : 0 < T := by
    refine lt_of_lt_of_le ?_ hT
    unfold TPar
    apply Nat.ceil_pos.2
    have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : 0 < delta := by linarith
    positivity
  have hTR : (0 : ℝ) < T := by exact_mod_cast hTpos
  set m := Vrho.card with hm
  have hm1 : (n : ℝ) * rho ≤ m := by rw [hV]; exact Nat.le_ceil _
  have hm2 : (m : ℝ) < n * rho + 1 := by rw [hV]; exact Nat.ceil_lt_add_one (by positivity)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm1
  set r := eps * rho * n / m with hr
  have hr0 : 0 < r := by positivity
  set w : (Fin T → ProbeSeed n) → ℝ := fun ss => ∏ i, seedW p (ss i) with hw
  have hw0 : ∀ ss, 0 ≤ w ss := fun ss => Finset.prod_nonneg fun i _ => seedW_nonneg n p hp0 hp1 _
  have hw1 : ∑ ss, w ss = 1 := sum_ssW n T p
  set g : Fin n → Finset (Fin n) → ProbeSeed n → ℝ := fun v S x => Y (Aof G x) v S with hg
  have hgb : ∀ v S x, 0 ≤ g v S x ∧ g v S x ≤ 1 := fun v S x => Y_bounds _ v S
  set P : (Fin T → ProbeSeed n) → Prop := fun ss =>
    ∀ S : Finset (Fin n), S.card = k →
      |GamUncut G Vrho rho ss S - GamRho G p Vrho rho S| ≤ eps * n with hP
  -- deterministic transfer
  have hgood : ∀ ss : Fin T → ProbeSeed n,
      (∀ v ∈ Vrho, ∀ S : Finset (Fin n), S.card = k →
        |(1 / (T : ℝ)) * ∑ i, g v S (ss i) - phi G p v S| ≤ r) → P ss := by
    intro ss h S hS
    have hU : GamUncut G Vrho rho ss S - GamRho G p Vrho rho S =
        (1 / rho) * ∑ v ∈ Vrho, ((1 / (T : ℝ)) * ∑ i, g v S (ss i) - phi G p v S) := by
      unfold GamUncut GamCut GamRho
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      exact Y_uncut G (ss i) Vrho v hv S
    rw [hU, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / rho)]
    calc 1 / rho * |∑ v ∈ Vrho, ((1 / (T : ℝ)) * ∑ i, g v S (ss i) - phi G p v S)|
        ≤ 1 / rho * ∑ v ∈ Vrho, r := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v hv => h v hv S hS)
      _ = eps * n := by
          rw [Finset.sum_const, nsmul_eq_mul, ← hm, hr]
          field_simp
  have hphi : ∀ v S, phi G p v S = ∑ x : ProbeSeed n, seedW p x * g v S x :=
    fun v S => phi_eq_mean G p v S
  unfold seedEventProb
  by_cases hr1 : 1 ≤ r
  · -- every sketch is good
    have : ∀ ss, P ss := by
      intro ss
      apply hgood
      intro v _ S _
      have h1 : 0 ≤ (1 / (T : ℝ)) * ∑ i, g v S (ss i) :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hgb v S _).1)
      have h2 : (1 / (T : ℝ)) * ∑ i, g v S (ss i) ≤ 1 := by
        rw [one_div, inv_mul_le_iff₀ hTR]
        calc ∑ i, g v S (ss i) ≤ ∑ _i : Fin T, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hgb v S _).2
          _ = T * 1 := by simp
      have h3 := phi_nonneg G p hp0 hp1 v S
      have h4 := phi_le_one G p hp0 hp1 v S
      rw [abs_le]; constructor <;> linarith
    have hsum : ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) * (if P ss then (1 : ℝ) else 0) =
        ∑ ss, w ss := by
      apply Finset.sum_congr rfl; intro ss _; rw [if_pos (this ss), mul_one]
    rw [hsum, hw1]
    have := Real.exp_pos (-delta)
    linarith
  · push Not at hr1
    have hnum := num3 n k hk hn eps delta rho heps hdelta hrhoPar hrho1 m hm1 hm2 T hT hr1
    rw [← hr] at hnum
    set up : Fin n → Finset (Fin n) → (Fin T → ProbeSeed n) → ℝ := fun v S ss =>
      if T * r ≤ ∑ i, (g v S (ss i) - ∑ x, seedW p x * g v S x) then 1 else 0 with hup
    set lo : Fin n → Finset (Fin n) → (Fin T → ProbeSeed n) → ℝ := fun v S ss =>
      if T * r ≤ ∑ i, ((∑ x, seedW p x * g v S x) - g v S (ss i)) then 1 else 0 with hlo
    have hind : ∀ ss, (if P ss then (0 : ℝ) else 1) ≤
        ∑ v ∈ Vrho, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (up v S ss + lo v S ss) := by
      intro ss
      have hnn : ∀ v S, 0 ≤ up v S ss + lo v S ss := by
        intro v S; simp only [hup, hlo]; split_ifs <;> norm_num
      by_cases hPs : P ss
      · rw [if_pos hPs]
        exact Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun S _ => hnn v S
      · rw [if_neg hPs]
        have : ¬ ∀ v ∈ Vrho, ∀ S : Finset (Fin n), S.card = k →
            |(1 / (T : ℝ)) * ∑ i, g v S (ss i) - phi G p v S| ≤ r := fun h => hPs (hgood ss h)
        push Not at this
        obtain ⟨v, hv, S, hS, hbad⟩ := this
        have hdev : (1 / (T : ℝ)) * ∑ i, g v S (ss i) - phi G p v S =
            (1 / (T : ℝ)) * ∑ i, (g v S (ss i) - ∑ x, seedW p x * g v S x) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, hphi]
          field_simp
        rw [hdev, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / T)] at hbad
        have hbad' : T * r < |∑ i, (g v S (ss i) - ∑ x, seedW p x * g v S x)| := by
          rw [one_div, lt_inv_mul_iff₀ hTR] at hbad; exact hbad
        rw [lt_abs] at hbad'
        have hneg : -∑ i, (g v S (ss i) - ∑ x, seedW p x * g v S x) =
            ∑ i, ((∑ x, seedW p x * g v S x) - g v S (ss i)) := by
          rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
        have hone : 1 ≤ up v S ss + lo v S ss := by
          have hu0 : 0 ≤ up v S ss := by simp only [hup]; split_ifs <;> norm_num
          have hl0 : 0 ≤ lo v S ss := by simp only [hlo]; split_ifs <;> norm_num
          rcases hbad' with h | h
          · have : up v S ss = 1 := by simp only [hup]; rw [if_pos h.le]
            linarith
          · rw [hneg] at h
            have : lo v S ss = 1 := by simp only [hlo]; rw [if_pos h.le]
            linarith
        calc (1 : ℝ) ≤ up v S ss + lo v S ss := hone
          _ ≤ ∑ S' ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (up v S' ss + lo v S' ss) :=
              Finset.single_le_sum (fun S' _ => hnn v S')
                (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩)
          _ ≤ _ := Finset.single_le_sum
              (f := fun v' => ∑ S' ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
                (up v' S' ss + lo v' S' ss))
              (fun v' _ => Finset.sum_nonneg fun S' _ => hnn v' S') hv
    have hsplit : ∀ ss, (if P ss then (1 : ℝ) else 0) = 1 - (if P ss then (0 : ℝ) else 1) := by
      intro ss; split_ifs <;> norm_num
    have hbound : ∀ v S, ∑ ss, w ss * up v S ss + ∑ ss, w ss * lo v S ss ≤
        2 * Real.exp (-2 * T * r ^ 2) := by
      intro v S
      have h1 := copies_upper p hp0 hp1 T hTpos (g v S) (hgb v S) r hr0
      have h2 := copies_lower p hp0 hp1 T hTpos (g v S) (hgb v S) r hr0
      have e1 : ∑ ss, w ss * up v S ss = ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) *
          (if T * r ≤ ∑ i, (g v S (ss i) - ∑ x, seedW p x * g v S x) then (1 : ℝ) else 0) := rfl
      have e2 : ∑ ss, w ss * lo v S ss = ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) *
          (if T * r ≤ ∑ i, ((∑ x, seedW p x * g v S x) - g v S (ss i)) then (1 : ℝ) else 0) := rfl
      rw [e1, e2]; linarith
    calc 1 - Real.exp (-delta)
        ≤ 1 - ∑ v ∈ Vrho, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (∑ ss, w ss * up v S ss + ∑ ss, w ss * lo v S ss) := by
          have : ∑ v ∈ Vrho, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              (∑ ss, w ss * up v S ss + ∑ ss, w ss * lo v S ss) ≤
              (m : ℝ) * (n.choose k : ℝ) * (2 * Real.exp (-2 * T * r ^ 2)) := by
            calc _ ≤ ∑ v ∈ Vrho, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
                  2 * Real.exp (-2 * T * r ^ 2) :=
                  Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun S _ => hbound v S
              _ = _ := by
                  rw [Finset.sum_const, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
                    Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← hm]
                  ring
          linarith
      _ ≤ 1 - ∑ ss, w ss * (if P ss then (0 : ℝ) else 1) := by
          have : ∑ ss, w ss * (if P ss then (0 : ℝ) else 1) ≤
              ∑ v ∈ Vrho, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
                (∑ ss, w ss * up v S ss + ∑ ss, w ss * lo v S ss) := by
            calc _ ≤ ∑ ss, w ss * ∑ v ∈ Vrho, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
                  (up v S ss + lo v S ss) :=
                  Finset.sum_le_sum fun ss _ => mul_le_mul_of_nonneg_left (hind ss) (hw0 ss)
              _ = ∑ v ∈ Vrho, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
                    ∑ ss, w ss * (up v S ss + lo v S ss) := by
                  simp only [Finset.mul_sum]
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro v _
                  rw [Finset.sum_comm]
              _ = _ := by
                  apply Finset.sum_congr rfl; intro v _
                  apply Finset.sum_congr rfl; intro S _
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl; intro ss _
                  ring
          linarith
      _ = ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) * (if P ss then (1 : ℝ) else 0) := by
          simp only [hsplit, mul_sub, mul_one, Finset.sum_sub_distrib]
          rw [hw1]

