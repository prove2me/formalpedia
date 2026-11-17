-- Prove2me | solution 1 for EDPHardness.IntegralityGap.short_paths_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T08:09:51.170209+00:00
-- url     : https://prove2.me/submissions/44e536a6-a67a-4956-abd7-33060fcc6a1c

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

open SimpleGraph Finset

theorem walk_split_count_one {V : Type*} [DecidableEq V] {G : SimpleGraph V} {e : Sym2 V} :
    ∀ {x y : V} (W : G.Walk x y), W.edges.count e = 1 →
      ∃ (a b : V) (_ : G.Adj a b) (W1 : G.Walk x a) (W2 : G.Walk b y),
        e = s(a, b) ∧ e ∉ W1.edges ∧ e ∉ W2.edges ∧ W1.length + W2.length + 1 = W.length
  | _, _, .nil, h => by simp at h
  | x, y, .cons (v := z) hxz W', h => by
    by_cases hx : s(x, z) = e
    · subst hx
      have h0 : W'.edges.count s(x, z) = 0 := by
        simp [Walk.edges_cons] at h; omega
      exact ⟨x, z, hxz, .nil, W', rfl, by simp, List.count_eq_zero.mp h0, by simp⟩
    · have h1 : W'.edges.count e = 1 := by
        simpa [Walk.edges_cons, List.count_cons, hx] using h
      obtain ⟨a, b, hab, W1, W2, he, h1', h2', hl⟩ := walk_split_count_one W' h1
      refine ⟨a, b, hab, .cons hxz W1, W2, he, ?_, h2', ?_⟩
      · simp only [Walk.edges_cons, List.mem_cons, not_or]
        exact ⟨fun h => hx h.symm, h1'⟩
      · simp only [Walk.length_cons]; omega

theorem cycle_of_count_one {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (W : G.Walk u u) (e : Sym2 V) (h : W.edges.count e = 1) :
    ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ p.length ≤ W.length ∧ e ∈ p.edges := by
  obtain ⟨a, b, hab, W1, W2, rfl, h1, h2, hl⟩ := walk_split_count_one W h
  have hq : s(a, b) ∉ (W2.append W1).bypass.edges := fun hm => by
    have := Walk.edges_bypass_subset_edges _ hm
    rw [Walk.edges_append, List.mem_append] at this
    rcases this with h' | h'
    · exact h2 h'
    · exact h1 h'
  refine ⟨a, Walk.cons hab (W2.append W1).bypass, ?_, ?_, by simp⟩
  · rw [Walk.cons_isCycle_iff]; exact ⟨Walk.bypass_isPath _, hq⟩
  · have := Walk.length_bypass_le_length (W2.append W1)
    simp only [Walk.length_append] at this
    simp only [Walk.length_cons]; omega

variable {n m c : ℕ} (H : Hyp n m c)

/-- The hyperedges containing `w`. -/
def vset (w : Fin n) : Finset (Fin m) := univ.filter (fun i => w ∈ (H i).1)

/-- Contraction map `G(H) → G′` (sources/sinks go to their first/last hyperedge). -/
noncomputable def phi (d : Fin m) : Node n m → Fin m
  | .s w => if h : (vset H w).Nonempty then (vset H w).min' h else d
  | .t w => if h : (vset H w).Nonempty then (vset H w).max' h else d
  | .l i => i
  | .r i => i

theorem gapRel_phi (d : Fin m) {x z : Node n m} (h : GapRel H x z) :
    phi H d x = phi H d z ∨
      ∃ a b : Fin m, a < b ∧ x = .r a ∧ z = .l b ∧ (gapGraph H).Adj (.r a) (.l b) := by
  cases h with
  | special i => left; rfl
  | first w i hv hmin =>
    left
    have hi : i ∈ vset H w := by simp [vset, hv]
    have hne : (vset H w).Nonempty := ⟨i, hi⟩
    simp only [phi, dif_pos hne]
    apply le_antisymm (Finset.min'_le _ _ hi)
    apply Finset.le_min'
    intro j hj
    simp only [vset, mem_filter, mem_univ, true_and] at hj
    by_contra hlt; push Not at hlt; exact hmin j hlt hj
  | last w i hv hmax =>
    left
    have hi : i ∈ vset H w := by simp [vset, hv]
    have hne : (vset H w).Nonempty := ⟨i, hi⟩
    simp only [phi, dif_pos hne]
    apply le_antisymm (Finset.le_max' _ _ hi)
    apply Finset.max'_le
    intro j hj
    simp only [vset, mem_filter, mem_univ, true_and] at hj
    by_contra hlt; push Not at hlt; exact hmax j hlt hj
  | consec w a b hab ha hb hbt =>
    right
    refine ⟨a, b, hab, rfl, rfl, ?_⟩
    simp only [gapGraph, SimpleGraph.fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true,
      true_and]
    exact Or.inl (GapRel.consec w a b hab ha hb hbt)
  | isolated w hv =>
    left
    have hne : ¬ (vset H w).Nonempty := by
      rintro ⟨i, hi⟩
      simp only [vset, mem_filter, mem_univ, true_and] at hi
      exact hv i hi
    simp only [phi, dif_neg hne]

theorem adj_phi (d : Fin m) {x z : Node n m} (h : (gapGraph H).Adj x z) :
    phi H d x = phi H d z ∨
      ∃ a b : Fin m, a < b ∧ (gapGraph H).Adj (.r a) (.l b) ∧ s(x, z) = s(Node.r a, Node.l b) := by
  simp only [gapGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h' | h'
  · rcases gapRel_phi H d h' with e | ⟨a, b, hab, rfl, rfl, hadj⟩
    · exact Or.inl e
    · exact Or.inr ⟨a, b, hab, hadj, rfl⟩
  · rcases gapRel_phi H d h' with e | ⟨a, b, hab, rfl, rfl, hadj⟩
    · exact Or.inl e.symm
    · exact Or.inr ⟨a, b, hab, hadj, Sym2.eq_swap⟩

theorem contracted_adj_of {a b : Fin m} (hab : a < b) (h : (gapGraph H).Adj (.r a) (.l b)) :
    (contracted H).Adj a b := by
  simp only [contracted, SimpleGraph.fromRel_adj]
  exact ⟨hab.ne, Or.inl h⟩

theorem sym2_lt_eq {a b a' b' : Fin m} (hab : a < b) (hab' : a' < b') :
    s(a', b') = s(a, b) ↔ a' = a ∧ b' = b := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (h | ⟨rfl, rfl⟩)
    · exact h
    · exact absurd (hab.trans hab') (lt_irrefl _)
  · intro h; exact Or.inl h

theorem sym2_node_eq {a b a' b' : Fin m} :
    s(Node.r a', Node.l b') = (s(Node.r a, Node.l b) : Sym2 (Node n m)) ↔ a' = a ∧ b' = b := by
  rw [Sym2.eq_iff]
  simp

theorem contract_walk (d : Fin m) {a b : Fin m} (hab : a < b) :
    ∀ {x y : Node n m} (p : (gapGraph H).Walk x y),
      ∃ q : (contracted H).Walk (phi H d x) (phi H d y),
        q.length ≤ p.length ∧ q.edges.count s(a, b) = p.edges.count s(Node.r a, Node.l b)
  | _, _, .nil => ⟨.nil, by simp, by simp⟩
  | x, y, .cons (v := z) hxz p' => by
    obtain ⟨q', hl, hc⟩ := contract_walk d hab p'
    rcases adj_phi H d hxz with heq | ⟨a', b', hab', hadj, hs⟩
    · refine ⟨q'.copy heq.symm rfl, ?_, ?_⟩
      · simp only [Walk.length_copy, Walk.length_cons]; omega
      · have hne : s(x, z) ≠ s(Node.r a, Node.l b) := by
          intro hxe
          rw [Sym2.eq_iff] at hxe
          rcases hxe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hab.ne heq
          · exact hab.ne heq.symm
        simp [Walk.edges_cons, hc, hne]
    · have hadj' : (contracted H).Adj (phi H d x) (phi H d z) := by
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact contracted_adj_of H hab' hadj
        · exact (contracted_adj_of H hab' hadj).symm
      refine ⟨.cons hadj' q', ?_, ?_⟩
      · simp only [Walk.length_cons]; omega
      · have key : s(phi H d x, phi H d z) = s(a', b') := by
          rw [Sym2.eq_iff] at hs
          rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        simp only [Walk.edges_cons, List.count_cons, hc, key, hs, beq_iff_eq,
          sym2_lt_eq hab hab', sym2_node_eq]

/-- `a, b` are consecutive hyperedges of `v`. -/
def VCons (v : Fin n) (a b : Fin m) : Prop :=
  v ∈ (H a).1 ∧ v ∈ (H b).1 ∧ ∀ j, a < j → j < b → v ∉ (H j).1

theorem canon_walk (v : Fin n) (hne : (vset H v).Nonempty) {a b : Fin m} (hab : a < b)
    (hnc : ¬ VCons H v a b) (i : Fin m) (hi : v ∈ (H i).1) :
    ∃ q : (contracted H).Walk ((vset H v).min' hne) i,
      q.length + 1 ≤ ((vset H v).filter (· ≤ i)).card ∧ q.edges.count s(a, b) = 0 := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
  have hiv : i ∈ vset H v := by simp [vset, hi]
  by_cases hA : ((vset H v).filter (· < i)).Nonempty
  · set a0 := ((vset H v).filter (· < i)).max' hA with ha0
    have ha0m := Finset.max'_mem _ hA
    rw [← ha0] at ha0m
    simp only [mem_filter, vset, mem_univ, true_and] at ha0m
    obtain ⟨hva0, ha0i⟩ := ha0m
    obtain ⟨q0, hl0, hc0⟩ := ih a0 ha0i hva0
    have hbt : ∀ j, a0 < j → j < i → v ∉ (H j).1 := by
      intro j h1 h2 hj
      have : j ≤ a0 := Finset.le_max' _ _ (by simp [vset, hj, h2])
      exact absurd (lt_of_lt_of_le h1 this) (lt_irrefl _)
    have hadjG : (gapGraph H).Adj (.r a0) (.l i) := by
      simp only [gapGraph, SimpleGraph.fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true,
        true_and]
      exact Or.inl (GapRel.consec v a0 i ha0i hva0 hi hbt)
    refine ⟨q0.concat (contracted_adj_of H ha0i hadjG), ?_, ?_⟩
    · rw [Walk.length_concat]
      have : ((vset H v).filter (· ≤ a0)).card < ((vset H v).filter (· ≤ i)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨i, by simp [hiv], by simp [ha0i]⟩
        · intro j hj
          simp only [mem_filter] at hj ⊢
          exact ⟨hj.1, hj.2.trans ha0i.le⟩
      omega
    · rw [Walk.edges_concat, List.concat_eq_append, List.count_append, hc0]
      have : s(a0, i) ≠ s(a, b) := by
        intro h
        rw [sym2_lt_eq hab ha0i] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hnc ⟨hva0, hi, hbt⟩
      simp [this]
  · have hmin : (vset H v).min' hne = i := by
      apply le_antisymm (Finset.min'_le _ _ hiv)
      by_contra hlt; push Not at hlt
      exact hA ⟨(vset H v).min' hne, Finset.mem_filter.mpr ⟨Finset.min'_mem _ hne, hlt⟩⟩
    refine ⟨(Walk.nil : (contracted H).Walk i i).copy hmin.symm rfl, ?_, by simp⟩
    simp only [Walk.length_copy, Walk.length_nil, zero_add, Finset.one_le_card]
    exact ⟨i, by simp [hiv]⟩

theorem short_cycle_of_bad_edge (v : Fin n) (P : (gapGraph H).Walk (.s v) (.t v))
    (hP : P.IsPath) (L : ℕ) (hlen : P.length + 1 ≤ L) (hdeg : degH H v ≤ L) {a b : Fin m}
    (hab : a < b) (hmem : s(Node.r a, Node.l b) ∈ P.edges) (hnc : ¬ VCons H v a b) :
    ∃ (x : Fin m) (p : (contracted H).Walk x x), p.IsCycle ∧ p.length ≤ 2 * L ∧
      s(a, b) ∈ p.edges := by
  obtain ⟨Q, hQl, hQc⟩ := contract_walk H a hab P
  rw [List.count_eq_one_of_mem hP.isTrail.edges_nodup hmem] at hQc
  have hC : ∃ Cw : (contracted H).Walk (phi H a (.s v)) (phi H a (.t v)),
      Cw.length ≤ L ∧ Cw.edges.count s(a, b) = 0 := by
    by_cases hne : (vset H v).Nonempty
    · have hm := Finset.max'_mem _ hne
      have hvm : v ∈ (H ((vset H v).max' hne)).1 := by
        simpa [vset] using hm
      obtain ⟨q, hql, hqc⟩ := canon_walk H v hne hab hnc _ hvm
      refine ⟨q.copy (by simp [phi, hne]) (by simp [phi, hne]), ?_, by simpa using hqc⟩
      rw [Walk.length_copy]
      have : ((vset H v).filter (· ≤ (vset H v).max' hne)).card ≤ degH H v :=
        Finset.card_filter_le _ _
      omega
    · refine ⟨(Walk.nil : (contracted H).Walk a a).copy (by simp [phi, hne])
        (by simp [phi, hne]), by simp, by simp⟩
  obtain ⟨Cw, hCl, hCc⟩ := hC
  obtain ⟨x, p, hp, hpl, hpe⟩ := cycle_of_count_one (Q.append Cw.reverse) s(a, b)
    (by rw [Walk.edges_append, List.count_append, Walk.edges_reverse, List.count_reverse,
      hQc, hCc])
  refine ⟨x, p, hp, ?_, hpe⟩
  rw [Walk.length_append, Walk.length_reverse] at hpl
  omega


theorem gap_adj_iff (x z : Node n m) :
    (gapGraph H).Adj x z ↔ x ≠ z ∧ (GapRel H x z ∨ GapRel H z x) := by
  simp [gapGraph]

theorem nbr_s {w : Fin n} {z : Node n m} (h : (gapGraph H).Adj (.s w) z) :
    (∃ i, z = .l i ∧ w ∈ (H i).1 ∧ ∀ j < i, w ∉ (H j).1) ∨ (z = .t w ∧ ∀ i, w ∉ (H i).1) := by
  rw [gap_adj_iff] at h
  rcases h with ⟨_, h | h⟩
  · cases h with
    | first _ i hv hmin => exact Or.inl ⟨i, rfl, hv, hmin⟩
    | isolated _ hv => exact Or.inr ⟨rfl, hv⟩
  · cases h

theorem nbr_t {w : Fin n} {z : Node n m} (h : (gapGraph H).Adj (.t w) z) :
    (∃ i, z = .r i ∧ w ∈ (H i).1 ∧ ∀ j, i < j → w ∉ (H j).1) ∨
      (z = .s w ∧ ∀ i, w ∉ (H i).1) := by
  rw [gap_adj_iff] at h
  rcases h with ⟨_, h | h⟩
  · cases h
  · cases h with
    | last _ i hv hmax => exact Or.inl ⟨i, rfl, hv, hmax⟩
    | isolated _ hv => exact Or.inr ⟨rfl, hv⟩

theorem nbr_l {i : Fin m} {z : Node n m} (h : (gapGraph H).Adj (.l i) z) :
    z = .r i ∨ (∃ w, z = .s w ∧ w ∈ (H i).1 ∧ ∀ j < i, w ∉ (H j).1) ∨
      (∃ a, z = .r a ∧ a < i) := by
  rw [gap_adj_iff] at h
  rcases h with ⟨_, h | h⟩
  · cases h with
    | special _ => exact Or.inl rfl
  · cases h with
    | first w _ hv hmin => exact Or.inr (Or.inl ⟨w, rfl, hv, hmin⟩)
    | consec w a _ hab _ _ _ => exact Or.inr (Or.inr ⟨a, rfl, hab⟩)

theorem nbr_r {i : Fin m} {z : Node n m} (h : (gapGraph H).Adj (.r i) z) :
    z = .l i ∨ (∃ w, z = .t w ∧ w ∈ (H i).1 ∧ ∀ j, i < j → w ∉ (H j).1) ∨
      (∃ b, z = .l b ∧ i < b) := by
  rw [gap_adj_iff] at h
  rcases h with ⟨_, h | h⟩
  · cases h with
    | last w _ hv hmax => exact Or.inr (Or.inl ⟨w, rfl, hv, hmax⟩)
    | consec w _ b hab _ _ _ => exact Or.inr (Or.inr ⟨b, rfl, hab⟩)
  · cases h with
    | special _ => exact Or.inl rfl

theorem s_unique {w : Fin n} {z z' : Node n m} (h : (gapGraph H).Adj (.s w) z)
    (h' : (gapGraph H).Adj (.s w) z') : z = z' := by
  rcases nbr_s H h with ⟨i, rfl, hi, hmin⟩ | ⟨rfl, hv⟩ <;>
    rcases nbr_s H h' with ⟨i', rfl, hi', hmin'⟩ | ⟨rfl, hv'⟩
  · congr 1
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · exact absurd hi (hmin' i hlt)
    · exact heq
    · exact absurd hi' (hmin i' hgt)
  · exact absurd hi (hv' i)
  · exact absurd hi' (hv i')
  · rfl

theorem t_unique {w : Fin n} {z z' : Node n m} (h : (gapGraph H).Adj (.t w) z)
    (h' : (gapGraph H).Adj (.t w) z') : z = z' := by
  rcases nbr_t H h with ⟨i, rfl, hi, hmax⟩ | ⟨rfl, hv⟩ <;>
    rcases nbr_t H h' with ⟨i', rfl, hi', hmax'⟩ | ⟨rfl, hv'⟩
  · congr 1
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · exact absurd hi' (hmax i' hlt)
    · exact heq
    · exact absurd hi (hmax' i hgt)
  · exact absurd hi (hv' i)
  · exact absurd hi' (hv i')
  · rfl

theorem dead_end {y x e : Node n m} (huniq : ∀ z z', (gapGraph H).Adj x z →
      (gapGraph H).Adj x z' → z = z')
    (hyx : (gapGraph H).Adj y x) (p : (gapGraph H).Walk x e)
    (hp : (Walk.cons hyx p).IsPath) (hne : e ≠ x) : False := by
  cases p with
  | nil => exact hne rfl
  | cons h' p'' =>
    rename_i z'
    have hz : z' = y := huniq _ _ h' hyx.symm
    subst hz
    rw [Walk.cons_isPath_iff] at hp
    apply hp.2
    simp

theorem filter_cons_eq (q q' : Fin m → Bool) (i : Fin m)
    (hq : ∀ j, q j = true ↔ (j = i ∨ q' j = true)) (hq' : ∀ j, q' j = true → i < j) :
    (List.finRange m).filter q = i :: (List.finRange m).filter q' := by
  refine @List.Pairwise.eq_of_mem_iff _ (· < ·)
    ⟨fun _ _ h1 h2 => absurd h1 (lt_asymm h2)⟩ ⟨lt_irrefl⟩ _ _ ?_ ?_ ?_
  · exact (List.pairwise_lt_finRange m).filter _
  · rw [List.pairwise_cons]
    exact ⟨fun j hj => hq' j (List.mem_filter.mp hj).2, (List.pairwise_lt_finRange m).filter _⟩
  · intro j
    simp only [List.mem_filter, List.mem_finRange, true_and, List.mem_cons, hq]

/-- The canonical support from `ℓ_i` on (hyperedges `j ≥ i` of `v`). -/
def lst (v : Fin n) (i : Fin m) : List (Node n m) :=
  ((List.finRange m).filter (fun j => decide (v ∈ (H j).1 ∧ i ≤ j))).flatMap
    (fun j => [Node.l j, Node.r j])

theorem claim_l (v : Fin n) (i : Fin m) : v ∈ (H i).1 →
    ∀ (p : (gapGraph H).Walk (.l i) (.t v)), p.IsPath →
      (∀ a b, a < b → s(Node.r a, Node.l b) ∈ p.edges → VCons H v a b) →
      Node.s v ∉ p.support → (∀ j, v ∈ (H j).1 → j < i → Node.r j ∉ p.support) →
      p.support = lst H v i ++ [Node.t v] := by
  induction i using WellFoundedGT.induction with
  | _ i ih =>
  intro hi p hp hbad hs hr
  cases p with
  | cons h1 p1 =>
    rename_i z
    rcases nbr_l H h1 with rfl | ⟨w, rfl, hw, hwmin⟩ | ⟨a, rfl, hai⟩
    · cases p1 with
      | cons h2 p2 =>
        rename_i z2
        have hp1 := (Walk.cons_isPath_iff _ _).mp hp
        have hp2 := (Walk.cons_isPath_iff _ _).mp hp1.1
        rcases nbr_r H h2 with rfl | ⟨w, rfl, hw, hwmax⟩ | ⟨b, rfl, hib⟩
        · exfalso; apply hp1.2; simp
        · by_cases hwv : w = v
          · subst hwv
            cases p2 with
            | nil =>
              have hfl : (List.finRange m).filter (fun j => decide (w ∈ (H j).1 ∧ i ≤ j)) = [i] := by
                rw [filter_cons_eq _ (fun _ => false) i]
                · simp
                · intro j
                  simp only [decide_eq_true_eq, Bool.false_eq_true, or_false]
                  constructor
                  · rintro ⟨hj, hij⟩
                    rcases hij.lt_or_eq with hlt | heq
                    · exact absurd hj (hwmax j hlt)
                    · exact heq.symm
                  · rintro rfl; exact ⟨hi, le_rfl⟩
                · simp
              rw [lst, hfl]
              simp
            | cons h' p' =>
              exact False.elim (((Walk.cons_isPath_iff _ _).mp hp2.1).2 p'.end_mem_support)
          · exfalso
            exact dead_end H (fun z z' h h' => t_unique H h h') h2 p2 hp1.1
              (by simp [Ne, Ne.symm hwv])
        · have hvc : VCons H v i b := hbad i b hib (by simp)
          obtain ⟨-, hvb, hbt⟩ := hvc
          have hrec := ih b hib hvb p2 hp2.1
            (fun a b' hab' hm => hbad a b' hab' (by simp [hm]))
            (fun hm => hs (by simp [hm]))
            (by
              intro j hj hjb hm
              rcases lt_trichotomy j i with hlt | rfl | hgt
              · exact hr j hj hlt (by simp [hm])
              · exact hp2.2 hm
              · exact hbt j hgt hjb hj)
          have hfl : (List.finRange m).filter (fun j => decide (v ∈ (H j).1 ∧ i ≤ j)) =
              i :: (List.finRange m).filter (fun j => decide (v ∈ (H j).1 ∧ b ≤ j)) := by
            apply filter_cons_eq
            · intro j
              simp only [decide_eq_true_eq]
              constructor
              · rintro ⟨hj, hij⟩
                rcases hij.lt_or_eq with hlt | heq
                · right
                  refine ⟨hj, ?_⟩
                  by_contra hjb; push Not at hjb
                  exact hbt j hlt hjb hj
                · left; exact heq.symm
              · rintro (rfl | ⟨hj, hbj⟩)
                · exact ⟨hi, le_rfl⟩
                · exact ⟨hj, (hib.trans_le hbj).le⟩
            · intro j hj
              simp only [decide_eq_true_eq] at hj
              exact hib.trans_le hj.2
          simp only [Walk.support_cons, hrec, lst, hfl, List.flatMap_cons]
          simp
    · exfalso
      by_cases hwv : w = v
      · subst hwv; apply hs; simp
      · exact dead_end H (fun z z' h h' => s_unique H h h') h1 p1 hp (by simp)
    · exfalso
      have hvc : VCons H v a i := hbad a i hai (by simp [Sym2.eq_swap])
      exact hr a hvc.1 hai (by simp)

/-- Structural lemma: a non-canonical `s(v)`–`t(v)` path uses a regular edge
`(r_a, ℓ_b)`, `a < b`, joining two hyperedges that are not consecutive hyperedges of `v`. -/
theorem noncanonical_bad_edge (v : Fin n) (P : (gapGraph H).Walk (.s v) (.t v))
    (hP : P.IsPath) (hne : P.support ≠ canonicalSupport H v) :
    ∃ a b : Fin m, a < b ∧ s(Node.r a, Node.l b) ∈ P.edges ∧ ¬ VCons H v a b := by
  by_contra hcon
  apply hne
  have hbad : ∀ a b, a < b → s(Node.r a, Node.l b) ∈ P.edges → VCons H v a b :=
    fun a b hab hm => by
      by_contra h; exact hcon ⟨a, b, hab, hm, h⟩
  cases P with
  | cons h1 p1 =>
    have hp1 := (Walk.cons_isPath_iff _ _).mp hP
    rcases nbr_s H h1 with ⟨i, rfl, hi, hmin⟩ | ⟨rfl, hv⟩
    · have hrec := claim_l H v i hi p1 hp1.1
        (fun a b hab hm => hbad a b hab (by simp [hm])) hp1.2
        (fun j hj hji _ => hmin j hji hj)
      have hfl : (List.finRange m).filter (fun j => decide (v ∈ (H j).1)) =
          (List.finRange m).filter (fun j => decide (v ∈ (H j).1 ∧ i ≤ j)) := by
        apply List.filter_congr
        intro j _
        by_cases hj : v ∈ (H j).1
        · have : i ≤ j := by
            by_contra hlt; push Not at hlt; exact hmin j hlt hj
          simp [hj, this]
        · simp [hj]
      simp only [Walk.support_cons, hrec, canonicalSupport, hfl, lst]
    · cases p1 with
      | nil =>
        have : (List.finRange m).filter (fun j => decide (v ∈ (H j).1)) = [] := by
          rw [List.filter_eq_nil_iff]; intro j _; simpa using hv j
        simp [canonicalSupport, this]
      | cons h' p' =>
        exact False.elim (((Walk.cons_isPath_iff _ _).mp hp1.1).2 p'.end_mem_support)


theorem short_paths_bound_aux (n c : ℕ) (hc : 2 ≤ c) (hβ₁ : 0 < beta1 n c) (hβ₂ : 0 < beta2 n c)
    (hg : 10 * beta2 n c * c ≤ (gParam n c : ℝ))
    (H : Hyp n (numEdges n c) c) (hE₂ : ¬ E2 n c H) (hE₃ : ¬ E3 n c (2 * gParam n c) H)
    (R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1)) :
    ((Finset.univ.filter
        (fun v : R.routed => (R.path v).support ≠ canonicalSupport H v ∧
          (R.path v).length < gParam n c)).card : ℝ)
      ≤ (n : ℝ) / beta1 n c +
        2 * gParam n c * c * (6 * beta2 n c * (c : ℝ) ^ 2) ^ (2 * gParam n c + 2) := by
  classical
  let m := numEdges n c
  let g := gParam n c
  let X : ℝ := 6 * beta2 n c * (c : ℝ) ^ 2
  let T : Finset R.routed := Finset.univ.filter
    (fun v : R.routed => (R.path v).support ≠ canonicalSupport H v ∧
      (R.path v).length < gParam n c)
  let T1 : Finset R.routed := T.filter (fun v => 10 * beta2 n c * c < (degH H v.1 : ℝ))
  let T2 : Finset R.routed := T.filter (fun v => ¬ (10 * beta2 n c * c < (degH H v.1 : ℝ)))
  have hTsplit : T.card = T1.card + T2.card :=
    (Finset.card_filter_add_card_filter_not (s := T)
      (fun v => 10 * beta2 n c * c < (degH H v.1 : ℝ))).symm
  have hT1 : (T1.card : ℝ) ≤ (n : ℝ) / beta1 n c := by
    have h1 : T1.card ≤
        (Finset.univ.filter (fun v : Fin n => 10 * beta2 n c * c < (degH H v : ℝ))).card := by
      apply Finset.card_le_card_of_injOn (fun v => v.1)
      · intro v hv
        simp only [T1, Finset.mem_coe, Finset.mem_filter] at hv
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hv.2
      · intro a _ b _ h; exact Subtype.ext h
    have h2 := hE₂
    simp only [E2, gt_iff_lt, not_lt] at h2
    calc (T1.card : ℝ) ≤ _ := by exact_mod_cast h1
      _ ≤ _ := h2
  let CS : Set (Finset (Sym2 (Fin m))) := {S | ∃ (u : Fin m) (p : (contracted H).Walk u u),
    p.IsCycle ∧ p.length ≤ 2 * g ∧ p.edges.toFinset = S}
  have hfin : CS.Finite := Set.toFinite CS
  let CSF : Finset (Finset (Sym2 (Fin m))) := hfin.toFinset
  have hK : (CSF.card : ℝ) ≤ X ^ (2 * g + 1) := by
    have h3 : (CS.ncard : ℝ) ≤ X ^ (2 * g + 1) := by
      simpa [E3, gt_iff_lt, not_lt, cycleCount, CS, g, m, X] using hE₃
    rwa [Set.ncard_eq_toFinset_card CS hfin] at h3
  let U := (CSF ×ˢ ((Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m)))).filter
    (fun t => t.2.1 < t.2.2 ∧ s(t.2.1, t.2.2) ∈ t.1)
  have key : ∀ v ∈ T2, ∃ t ∈ U, s(Node.r t.2.1, Node.l t.2.2) ∈ (R.path v).edges := by
    intro v hv
    simp only [T2, T, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
    obtain ⟨⟨hne, hlen⟩, hdeg⟩ := hv
    obtain ⟨a, b, hab, hmem, hnc⟩ :=
      noncanonical_bad_edge H v.1 (R.path v) (R.isPath v) hne
    have hdeg' : degH H v.1 ≤ g := by
      have : (degH H v.1 : ℝ) ≤ g := hdeg.trans hg
      exact_mod_cast this
    obtain ⟨x, p, hp, hpl, hpe⟩ := short_cycle_of_bad_edge H v.1 (R.path v) (R.isPath v) g
      (Nat.succ_le_of_lt hlen) hdeg' hab hmem hnc
    refine ⟨(p.edges.toFinset, a, b), ?_, hmem⟩
    simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      CSF, Set.Finite.mem_toFinset, List.mem_toFinset]
    exact ⟨⟨x, p, hp, hpl, rfl⟩, hab, hpe⟩
  have hT2 : T2.card ≤ (c - 1) * U.card := by
    by_cases hne : T2.Nonempty
    · obtain ⟨v0, hv0⟩ := hne
      obtain ⟨t0, _, _⟩ := key v0 hv0
      have key' : ∀ v : R.routed,
          ∃ t, v ∈ T2 → t ∈ U ∧ s(Node.r t.2.1, Node.l t.2.2) ∈ (R.path v).edges := by
        intro v
        by_cases hv : v ∈ T2
        · obtain ⟨t, htU, htE⟩ := key v hv
          exact ⟨t, fun _ => ⟨htU, htE⟩⟩
        · exact ⟨t0, fun h => absurd h hv⟩
      choose f hf using key'
      apply Finset.card_le_mul_card_image_of_maps_to (f := f) (t := U)
      · intro v hv; exact (hf v hv).1
      · intro t _
        calc (T2.filter (fun v => f v = t)).card ≤ (Finset.univ.filter
              (fun i : R.routed => s(Node.r t.2.1, Node.l t.2.2) ∈ (R.path i).edges)).card := by
              apply Finset.card_le_card
              intro v hv
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
              rw [← hv.2]; exact (hf v hv.1).2
          _ ≤ c - 1 := R.congestion _
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  have hUc : U.card ≤ (2 * g) * CSF.card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := fun t => t.1) (t := CSF)
    · intro t ht
      simp only [U, Finset.mem_filter, Finset.mem_product] at ht
      exact ht.1.1
    · intro S hS
      obtain ⟨u, p, hp, hpl, rfl⟩ := (Set.Finite.mem_toFinset hfin).mp hS
      calc (U.filter (fun t => t.1 = p.edges.toFinset)).card ≤ p.edges.toFinset.card := by
            apply Finset.card_le_card_of_injOn (fun t => s(t.2.1, t.2.2))
            · intro t ht
              simp only [U, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at ht
              simp only [Finset.mem_coe]
              rw [← ht.2]; exact ht.1.2.2
            · rintro ⟨S1, a1, b1⟩ ht ⟨S2, a2, b2⟩ ht' heq
              simp only [U, Finset.coe_filter, Finset.mem_filter, Finset.mem_product,
                Set.mem_ofPred_eq] at ht ht'
              simp only at heq
              rw [sym2_lt_eq ht'.1.2.1 ht.1.2.1] at heq
              obtain ⟨rfl, rfl⟩ := heq
              have : S1 = S2 := ht.2.trans ht'.2.symm
              subst this; rfl
        _ ≤ p.edges.length := List.toFinset_card_le _
        _ ≤ 2 * g := by rw [Walk.length_edges]; exact hpl
  have hcnt : (T2.card : ℝ) ≤ ((c - 1 : ℕ) : ℝ) * (2 * g * CSF.card) := by
    have := hT2.trans (Nat.mul_le_mul_left _ hUc)
    exact_mod_cast this
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hXpos : 0 < X := mul_pos (mul_pos (by norm_num) hβ₂) (pow_pos hcpos 2)
  have h2g_nn : (0 : ℝ) ≤ 2 * (g : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg g)
  have hfinal : (T2.card : ℝ) ≤ 2 * g * c * X ^ (2 * g + 2) := by
    rcases Nat.eq_zero_or_pos CSF.card with h0 | hpos
    · rw [h0] at hcnt
      simp only [Nat.cast_zero, mul_zero] at hcnt
      exact hcnt.trans (mul_nonneg (mul_nonneg h2g_nn hcpos.le) (pow_nonneg hXpos.le _))
    · have hK1 : (1 : ℝ) ≤ X ^ (2 * g + 1) := le_trans (by exact_mod_cast hpos) hK
      have hX1 : 1 ≤ X := by
        by_contra hlt; push Not at hlt
        have := pow_lt_one₀ hXpos.le hlt (by omega : 2 * g + 1 ≠ 0)
        linarith
      have hpow : X ^ (2 * g + 1) ≤ X ^ (2 * g + 2) := pow_le_pow_right₀ hX1 (by omega)
      have hc1 : ((c - 1 : ℕ) : ℝ) ≤ c := by exact_mod_cast Nat.sub_le c 1
      have h1_nonneg : (0 : ℝ) ≤ 2 * (g : ℝ) * (CSF.card : ℝ) :=
        mul_nonneg h2g_nn (Nat.cast_nonneg _)
      have h2_le : 2 * (g : ℝ) * (CSF.card : ℝ) ≤ 2 * (g : ℝ) * X ^ (2 * g + 2) :=
        mul_le_mul_of_nonneg_left (hK.trans hpow) h2g_nn
      calc (T2.card : ℝ) ≤ ((c - 1 : ℕ) : ℝ) * (2 * g * CSF.card) := hcnt
        _ ≤ c * (2 * g * X ^ (2 * g + 2)) :=
            mul_le_mul hc1 h2_le h1_nonneg hcpos.le
        _ = 2 * g * c * X ^ (2 * g + 2) := by ring
  calc (T.card : ℝ) = T1.card + T2.card := by exact_mod_cast hTsplit
    _ ≤ _ := add_le_add hT1 hfinal

end EDPHardness.IntegralityGap

open EDPHardness.IntegralityGap

theorem solution (n c : ℕ) (hc : 2 ≤ c) (hβ₁ : 0 < beta1 n c) (hβ₂ : 0 < beta2 n c)
    (hg : 10 * beta2 n c * c ≤ (gParam n c : ℝ))
    (H : Hyp n (numEdges n c) c) (hE₂ : ¬ E2 n c H) (hE₃ : ¬ E3 n c (2 * gParam n c) H)
    (R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1)) :
    ((Finset.univ.filter
        (fun v : R.routed => (R.path v).support ≠ canonicalSupport H v ∧
          (R.path v).length < gParam n c)).card : ℝ)
      ≤ (n : ℝ) / beta1 n c +
        2 * gParam n c * c * (6 * beta2 n c * (c : ℝ) ^ 2) ^ (2 * gParam n c + 2) :=
  short_paths_bound_aux n c hc hβ₁ hβ₂ hg H hE₂ hE₃ R
