-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.tree_extension_attach
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-19T12:35:34.109004+00:00
-- url     : https://prove2.me/submissions/58bc745b-db2d-407b-b923-91275abb74c5

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

-- SUBMISSION FILE: CycleLengthsExp.ManyLengths.tree_extension_attach (eaeaa519).
-- Zero axioms, zero sorry. A2 (ext_parent_tree_ax) = ACCEPTED platform solution
-- for node 0b696241-0045-479d-bdfa-c5aaaec555e0 (sub 73e68a60, fizzyinc3),
-- inlined verbatim as a theorem (only rename: solution -> ext_parent_tree_ax).
-- B2 (dist_avoid_pred_ax) proved for real in the decomp; assembly unchanged.
-- Prior decomp: tree_extension_attach_decomp.lean (round 6 clean, 1 axiom A2).

set_option autoImplicit false

open SimpleGraph

/-- List helper: membership in `dropLast` of a cons-list is membership in
`dropLast` of the tail, or equality with the head. Proved for real. -/
theorem dropLast_head {V : Type*} (a : V) (l : List V) (y : V)
    (hy : y ∈ (a :: l).dropLast) : y ∈ l.dropLast ∨ y = a := by
  cases l with
  | nil => simp at hy
  | cons b l' =>
    have heq : (a :: b :: l').dropLast = a :: (b :: l').dropLast := rfl
    rw [heq] at hy
    rcases List.mem_cons.mp hy with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem h42_acyc {V : Type*} [DecidableEq V] {H H' : SimpleGraph V} (hH' : H'.IsAcyclic)
    (h : V → ℕ) (p : V → V)
    (hadj : ∀ a b, H.Adj a b → H'.Adj a b ∨ (p a = b ∧ 0 < h a ∧ h b + 1 = h a) ∨
      (p b = a ∧ 0 < h b ∧ h a + 1 = h b))
    (h0 : ∀ a b, H'.Adj a b → h a = 0) : H.IsAcyclic := by
  intro x c hc
  by_cases hpos : ∃ y ∈ c.support, 0 < h y
  · obtain ⟨y, hy, hymax⟩ := c.support.toFinset.exists_max_image h ⟨x, by simp⟩
    rw [List.mem_toFinset] at hy
    have hmax : ∀ z ∈ c.support, h z ≤ h y := fun z hz => hymax z (List.mem_toFinset.mpr hz)
    have hypos : 0 < h y := by
      obtain ⟨z, hz, hz'⟩ := hpos; exact lt_of_lt_of_le hz' (hmax z hz)
    have hc' : (c.rotate y hy).IsCycle := hc.rotate hy
    have hnn : ¬ (c.rotate y hy).Nil := hc'.not_nil
    have key : ∀ z, H.Adj y z → z ∈ (c.rotate y hy).support → z = p y := by
      intro z hyz hz
      rw [SimpleGraph.Walk.mem_support_rotate_iff] at hz
      rcases hadj y z hyz with h1 | ⟨h1, _, _⟩ | ⟨h1, _, h3⟩
      · have := h0 y z h1; omega
      · exact h1.symm
      · have := hmax z hz; omega
    have e1 := key _ (SimpleGraph.Walk.adj_snd hnn) (SimpleGraph.Walk.getVert_mem_support _ _)
    have e2 := key _ (SimpleGraph.Walk.adj_penultimate hnn).symm
      (SimpleGraph.Walk.getVert_mem_support _ _)
    exact hc'.snd_ne_penultimate (e1.trans e2.symm)
  · push Not at hpos
    have hE : ∀ e ∈ c.edges, e ∈ H'.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        have ha := hpos a (c.fst_mem_support_of_mem_edges he)
        have hb := hpos b (c.snd_mem_support_of_mem_edges he)
        have hab : H.Adj a b := c.adj_of_mem_edges he
        rcases hadj a b hab with h1 | ⟨_, h2, _⟩ | ⟨_, h2, _⟩
        · exact h1
        · omega
        · omega
    exact hH' (c.transfer H' hE) (hc.transfer hE)

theorem ext_parent_tree_ax {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Set V) (T : G.Subgraph) (v₀ : V)
    (hTverts : T.verts = S) (hv₀ : v₀ ∈ S)
    (hTacyc : T.spanningCoe.IsAcyclic)
    (hTreach : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v)
    (W : Set V) (hSW : S ⊆ W)
    (h : V → ℕ) (hhS : ∀ w ∈ S, h w = 0) (hhW : ∀ w ∈ W, w ∉ S → 0 < h w)
    (hparent : ∀ w ∈ W, w ∉ S → ∃ u ∈ W, G.Adj u w ∧ h u + 1 = h w) :
    ∃ (T₁ : G.Subgraph) (r : V → V),
      T₁.verts = W ∧
      (∀ a b, T.spanningCoe.Adj a b → T₁.spanningCoe.Adj a b) ∧
      T₁.spanningCoe.IsAcyclic ∧
      (∀ w ∈ W, T₁.spanningCoe.Reachable v₀ w) ∧
      (∀ w ∈ W, r w ∈ S) ∧
      (∀ w ∈ S, r w = w) ∧
      (∀ w ∈ W, T₁.spanningCoe.dist v₀ w = T.spanningCoe.dist v₀ (r w) + h w) ∧
      (∀ w ∈ W, w ∉ S → ∃ z, z ∉ S ∧ G.Adj (r w) z) := by
  classical
  have hpex : ∀ w, ∃ u, w ∈ W → w ∉ S → u ∈ W ∧ G.Adj u w ∧ h u + 1 = h w := by
    intro w
    by_cases hw : w ∈ W ∧ w ∉ S
    · obtain ⟨u, hu, hadj, hh⟩ := hparent w hw.1 hw.2
      exact ⟨u, fun _ _ => ⟨hu, hadj, hh⟩⟩
    · exact ⟨w, fun a b => absurd ⟨a, b⟩ hw⟩
  choose p hp using hpex
  have hWS : ∀ x ∈ W, h x = 0 → x ∈ S := by
    intro x hx h0; by_contra hxS; have := hhW x hx hxS; omega
  have hit : ∀ k x, x ∈ W → k ≤ h x → p^[k] x ∈ W ∧ h (p^[k] x) + k = h x := by
    intro k
    induction k with
    | zero => intro x hx _; exact ⟨hx, by simp⟩
    | succ k ih =>
      intro x hx hk
      obtain ⟨h1, h2⟩ := ih x hx (by omega)
      have hyS : p^[k] x ∉ S := by intro hS; have := hhS _ hS; omega
      obtain ⟨h3, _, h5⟩ := hp _ h1 hyS
      rw [Function.iterate_succ_apply']
      exact ⟨h3, by omega⟩
  let r : V → V := fun x => p^[h x] x
  have hrS : ∀ w ∈ W, r w ∈ S := by
    intro w hw
    obtain ⟨h1, h2⟩ := hit (h w) w hw le_rfl
    have h0 : h (p^[h w] w) = 0 := by omega
    exact hWS _ h1 h0
  have hrid : ∀ w ∈ S, r w = w := by
    intro w hw; show p^[h w] w = w; rw [hhS w hw]; rfl
  have hrp : ∀ x ∈ W, x ∉ S → r (p x) = r x := by
    intro x hx hxS
    have hh := (hp x hx hxS).2.2
    show p^[h (p x)] (p x) = p^[h x] x
    rw [← hh, Function.iterate_succ_apply]
  let T₁ : G.Subgraph :=
    { verts := W
      Adj := fun a b => T.Adj a b ∨ (a ∈ W ∧ a ∉ S ∧ p a = b) ∨ (b ∈ W ∧ b ∉ S ∧ p b = a)
      adj_sub := by
        rintro a b (h1 | ⟨ha, haS, rfl⟩ | ⟨hb, hbS, rfl⟩)
        · exact T.adj_sub h1
        · exact (hp a ha haS).2.1.symm
        · exact (hp b hb hbS).2.1
      edge_vert := by
        rintro a b (h1 | ⟨ha, _, _⟩ | ⟨hb, hbS, rfl⟩)
        · exact hSW (hTverts ▸ T.edge_vert h1)
        · exact ha
        · exact (hp b hb hbS).1
      symm := ⟨fun a b hab => by
        rcases hab with h1 | h2 | h3
        · exact Or.inl (T.adj_symm h1)
        · exact Or.inr (Or.inr h2)
        · exact Or.inr (Or.inl h3)⟩ }
  have hT1adj : ∀ a b, T₁.spanningCoe.Adj a b ↔
      (T.Adj a b ∨ (a ∈ W ∧ a ∉ S ∧ p a = b) ∨ (b ∈ W ∧ b ∉ S ∧ p b = a)) := fun a b => Iff.rfl
  have hTS : ∀ a b, T.Adj a b → a ∈ S := fun a b hab => hTverts ▸ T.edge_vert hab
  have hle : T.spanningCoe ≤ T₁.spanningCoe := fun a b hab => Or.inl hab
  -- upper bound walks
  have hup : ∀ k, ∀ x ∈ W, h x = k →
      ∃ q : T₁.spanningCoe.Walk v₀ x, q.length = T.spanningCoe.dist v₀ (r x) + h x := by
    intro k
    induction k with
    | zero =>
      intro x hx hx0
      have hxS := hWS x hx hx0
      obtain ⟨q, hq⟩ := (hTreach x hxS).exists_walk_length_eq_dist
      refine ⟨q.mapLe hle, ?_⟩
      rw [SimpleGraph.Walk.length_mapLe, hq, hrid x hxS, hx0]; rfl
    | succ k ih =>
      intro x hx hxk
      have hxS : x ∉ S := by intro hS; have := hhS x hS; omega
      obtain ⟨h1, _, h3⟩ := hp x hx hxS
      obtain ⟨q, hq⟩ := ih (p x) h1 (by omega)
      have hadj : T₁.spanningCoe.Adj (p x) x := Or.inr (Or.inr ⟨hx, hxS, rfl⟩)
      refine ⟨q.concat hadj, ?_⟩
      rw [SimpleGraph.Walk.length_concat, hq, hrp x hx hxS]; omega
  -- lower bound
  have hlow : ∀ a b (q : T₁.spanningCoe.Walk a b), a ∈ W →
      T.spanningCoe.dist v₀ (r a) + h a ≤ T.spanningCoe.dist v₀ (r b) + h b + q.length := by
    intro a b q
    induction q with
    | nil => intro _; simp
    | @cons a a' b hadj q ih =>
      intro ha
      have ha' : a' ∈ W := T₁.edge_vert hadj.symm
      have := ih ha'
      rw [SimpleGraph.Walk.length_cons]
      rcases hadj with h1 | ⟨_, haS, rfl⟩ | ⟨_, haS', rfl⟩
      · have haS := hTS a a' h1
        have haS' := hTS a' a (T.adj_symm h1)
        rw [hrid a haS, hrid a' haS', hhS a haS, hhS a' haS'] at *
        have hr : T.spanningCoe.Reachable a' a := (SimpleGraph.Adj.reachable (G := T.spanningCoe) (T.adj_symm h1))
        have h2 := hr.dist_triangle_right v₀
        have h3 : T.spanningCoe.dist a' a = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr (show T.spanningCoe.Adj a' a from T.adj_symm h1)
        omega
      · have := (hp a ha haS).2.2
        rw [← hrp a ha haS]; omega
      · have := (hp a' ha' haS').2.2
        rw [hrp a' ha' haS'] at *; omega
  have hreach : ∀ w ∈ W, T₁.spanningCoe.Reachable v₀ w := by
    intro w hw; obtain ⟨q, _⟩ := hup (h w) w hw rfl; exact ⟨q⟩
  have hfront : ∀ k, ∀ w ∈ W, w ∉ S → h w = k + 1 → ∃ z, z ∉ S ∧ G.Adj (r w) z := by
    intro k
    induction k with
    | zero =>
      intro w hw hwS hk
      obtain ⟨h1, h2, h3⟩ := hp w hw hwS
      have hpS := hWS _ h1 (by omega)
      refine ⟨w, hwS, ?_⟩
      rw [← hrp w hw hwS, hrid _ hpS]; exact h2
    | succ k ih =>
      intro w hw hwS hk
      obtain ⟨h1, _, h3⟩ := hp w hw hwS
      have hpS : p w ∉ S := by intro hS; have := hhS _ hS; omega
      rw [← hrp w hw hwS]; exact ih (p w) h1 hpS (by omega)
  refine ⟨T₁, r, rfl, fun a b hab => Or.inl hab, ?_, hreach, hrS, hrid, ?_, ?_⟩
  · refine h42_acyc hTacyc h p ?_ ?_
    · intro a b hab
      rcases hab with h1 | ⟨ha, haS, rfl⟩ | ⟨hb, hbS, rfl⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨rfl, hhW a ha haS, (hp a ha haS).2.2⟩)
      · exact Or.inr (Or.inr ⟨rfl, hhW b hb hbS, (hp b hb hbS).2.2⟩)
    · intro a b hab; exact hhS a (hTS a b hab)
  · intro w hw
    obtain ⟨q, hq⟩ := hup (h w) w hw rfl
    obtain ⟨q', hq'⟩ := (hreach w hw).exists_walk_length_eq_dist
    have h1 := hlow w v₀ q'.reverse hw
    rw [hrid v₀ hv₀, hhS v₀ hv₀, SimpleGraph.Walk.length_reverse, hq'] at h1
    simp only [SimpleGraph.dist_self] at h1
    have h2 := SimpleGraph.dist_le q
    omega
  · intro w hw hwS
    have := hhW w hw hwS
    exact hfront (h w - 1) w hw hwS (by omega)

/-
DEEP INPUT B2 — PROVED (2026-10-17). Distance to `S` avoiding `P` + predecessor.
Pure graph theory (no expansion): `W` is the set of vertices reachable
from `S` by a walk whose support avoids `P`, and `h w` is the shortest
such walk length. The parent property is the predecessor on a shortest
walk; minimality says `h w` is at most any avoiding-walk length.
Proof: `h w = sInf` of avoiding-walk lengths; `sInf_mem` gives a shortest
walk; its penultimate vertex (via `Walk.dropLast` / `Walk.adj_penultimate`)
has `h` one less, and concatenating the last edge gives `h w ≤ h z + 1`.
Standalone proof file: `tree_extension_attach_b2.lean` (theorem `dist_avoid_pred`).
-/
/-- List helper: membership in `dropLast` implies membership. Proved for real. -/
theorem mem_of_mem_dropLast {V : Type*} (l : List V) (y : V)
    (hy : y ∈ l.dropLast) : y ∈ l := by
  induction l with
  | nil => simp at hy
  | cons a l' ih =>
    cases l' with
    | nil => simp at hy
    | cons b l'' =>
      have heq : (a :: b :: l'').dropLast = a :: (b :: l'').dropLast := rfl
      rw [heq] at hy
      rcases List.mem_cons.mp hy with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem dist_avoid_pred_ax (n : ℕ) (G : SimpleGraph (Fin n))
    (S : Set (Fin n)) (P : Set (Fin n)) (hdisj : ∀ w ∈ P, w ∉ S) :
    ∃ (W : Set (Fin n)) (h : Fin n → ℕ),
      S ⊆ W ∧ (∀ w ∈ W, w ∉ P) ∧
      (∀ w ∈ S, h w = 0) ∧ (∀ w ∈ W, w ∉ S → 0 < h w) ∧
      (∀ w ∈ W, w ∉ S → ∃ u ∈ W, G.Adj u w ∧ h u + 1 = h w) ∧
      (∀ w, w ∈ W ↔ w ∉ P ∧ ∃ s ∈ S, ∃ q : G.Walk s w, ∀ y ∈ q.support, y ∉ P) ∧
      (∀ w ∈ W, ∀ s ∈ S, ∀ q : G.Walk s w,
        (∀ y ∈ q.support, y ∉ P) → h w ≤ q.length) := by
  classical
  -- Avoiding-walk lengths to `w`.
  set D : Fin n → Set ℕ := fun w =>
    {ℓ | ∃ s ∈ S, ∃ q : G.Walk s w, q.length = ℓ ∧ ∀ y ∈ q.support, y ∉ P}
    with hDdef
  set W : Set (Fin n) := {w | (D w).Nonempty} with hWdef
  set h : Fin n → ℕ := fun w => sInf (D w) with hhdef
  -- Endpoints lie in the support.
  have end_mem : ∀ {u v : Fin n} (q : G.Walk u v), v ∈ q.support := by
    intro u v q
    induction q with
    | nil => simp [Walk.support_nil]
    | cons hq q' ih =>
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem _ ih
  -- Vertices of `S` avoid `P`.
  have hSP : ∀ w ∈ S, w ∉ P := by
    intro w hw hmem
    exact hdisj w hmem hw
  -- `h = 0` on `S` (the nil walk has length 0).
  have h0_all : ∀ w ∈ S, h w = 0 := by
    intro w hw
    have h0 : (0 : ℕ) ∈ D w := by
      simp only [hDdef, Set.mem_ofPred_eq]
      refine ⟨w, hw, Walk.nil, rfl, ?_⟩
      rw [Walk.support_nil]
      intro y hy
      have hyw : y = w := List.mem_singleton.mp hy
      rw [hyw]
      exact hSP w hw
    have hle : sInf (D w) ≤ 0 := Nat.sInf_le h0
    simp only [hhdef]
    exact Nat.le_zero.mp hle
  -- `h > 0` off `S` (a length-0 walk from `S` to `w` forces `w ∈ S`).
  have hpos_all : ∀ w ∈ W, w ∉ S → 0 < h w := by
    intro w hw hwS
    rcases Nat.eq_zero_or_pos (h w) with h0 | hpos
    · exfalso
      simp only [hWdef, Set.mem_ofPred_eq] at hw
      obtain ⟨ℓ, hℓ⟩ := hw
      simp only [hhdef] at h0
      have hmem : sInf (D w) ∈ D w := Nat.sInf_mem ⟨ℓ, hℓ⟩
      rw [h0] at hmem
      simp only [hDdef, Set.mem_ofPred_eq] at hmem
      obtain ⟨s, hsS, q, hqlen, _hqavoid⟩ := hmem
      have hseq : s = w := Walk.eq_of_length_eq_zero hqlen
      rw [hseq] at hsS
      exact hwS hsS
    · exact hpos
  refine ⟨W, h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `S ⊆ W`
    intro w hw
    simp only [hWdef, Set.mem_ofPred_eq]
    refine ⟨0, ?_⟩
    simp only [hDdef, Set.mem_ofPred_eq]
    refine ⟨w, hw, Walk.nil, rfl, ?_⟩
    rw [Walk.support_nil]
    intro y hy
    have hyw : y = w := List.mem_singleton.mp hy
    rw [hyw]
    exact hSP w hw
  · -- `W` avoids `P`
    intro w hw
    simp only [hWdef, Set.mem_ofPred_eq] at hw
    obtain ⟨ℓ, hℓ⟩ := hw
    simp only [hDdef, Set.mem_ofPred_eq] at hℓ
    obtain ⟨s, _hsS, q, _hqlen, hqavoid⟩ := hℓ
    exact hqavoid w (end_mem q)
  · -- `h = 0` on `S`
    exact h0_all
  · -- `h > 0` off `S`
    exact hpos_all
  · -- Parent property: predecessor on a shortest walk.
    intro w hw hwS
    have hw' : (D w).Nonempty := by
      simp only [hWdef, Set.mem_ofPred_eq] at hw
      exact hw
    have hmem : sInf (D w) ∈ D w := Nat.sInf_mem hw'
    simp only [hDdef, Set.mem_ofPred_eq] at hmem
    obtain ⟨s, hsS, q, hqlen, hqavoid⟩ := hmem
    have hpos : 0 < h w := hpos_all w (by simp only [hWdef, Set.mem_ofPred_eq]; exact hw') hwS
    have hqpos : 0 < q.length := by
      have hqw : q.length = h w := by
        simp only [hhdef]
        exact hqlen
      omega
    have hqnil : ¬ q.Nil := Walk.not_nil_iff_lt_length.mpr hqpos
    have hadj : G.Adj q.penultimate w := Walk.adj_penultimate hqnil
    -- `q.length - 1 ∈ D (penultimate)`, via `q.dropLast`.
    have hzmem : q.length - 1 ∈ D q.penultimate := by
      simp only [hDdef, Set.mem_ofPred_eq]
      refine ⟨s, hsS, q.dropLast, Walk.length_dropLast q, ?_⟩
      intro y hy
      rw [Walk.support_dropLast hqnil] at hy
      exact hqavoid y (mem_of_mem_dropLast _ _ hy)
    have hzW : q.penultimate ∈ W := by
      simp only [hWdef, Set.mem_ofPred_eq]
      exact ⟨q.length - 1, hzmem⟩
    -- Goal in `sInf` form.
    simp only [hhdef]
    refine ⟨q.penultimate, hzW, hadj, ?_⟩
    have hzle : sInf (D q.penultimate) ≤ q.length - 1 := Nat.sInf_le hzmem
    -- `h w ≤ h z + 1`: concat a shortest walk to `z` with the last edge.
    have hwle : sInf (D w) ≤ sInf (D q.penultimate) + 1 := by
      have hzmem' : sInf (D q.penultimate) ∈ D q.penultimate := Nat.sInf_mem ⟨_, hzmem⟩
      simp only [hDdef, Set.mem_ofPred_eq] at hzmem'
      obtain ⟨s₂, hs₂S, q₂, hq₂len, hq₂avoid⟩ := hzmem'
      have hconcat_avoid : ∀ y ∈ (q₂.concat hadj).support, y ∉ P := by
        intro y hy
        rw [Walk.support_concat] at hy
        rcases List.mem_append.mp hy with hleft | hright
        · exact hq₂avoid y hleft
        · have hyw : y = w := List.mem_singleton.mp hright
          rw [hyw]
          have hwP : w ∉ P := by
            have : w ∈ W := by
              simp only [hWdef, Set.mem_ofPred_eq]
              exact hw'
            have h1 : ∀ v ∈ W, v ∉ P := by
              intro v hv
              simp only [hWdef, Set.mem_ofPred_eq] at hv
              obtain ⟨ℓ, hℓ⟩ := hv
              simp only [hDdef, Set.mem_ofPred_eq] at hℓ
              obtain ⟨sv, _hsv, qv, _hqv, hqvavoid⟩ := hℓ
              exact hqvavoid v (end_mem qv)
            exact h1 w this
          exact hwP
      have h1 : sInf (D w) ≤ (q₂.concat hadj).length :=
        Nat.sInf_le ⟨s₂, hs₂S, q₂.concat hadj, rfl, hconcat_avoid⟩
      have h2 : (q₂.concat hadj).length = q₂.length + 1 :=
        Walk.length_concat q₂ hadj
      calc sInf (D w) ≤ (q₂.concat hadj).length := h1
        _ = q₂.length + 1 := h2
        _ = sInf (D q.penultimate) + 1 := by rw [hq₂len]
    have hge : sInf (D q.penultimate) + 1 ≤ sInf (D w) := by
      rw [← hqlen]
      omega
    exact le_antisymm hge hwle
  · -- `W` characterization.
    intro w
    constructor
    · intro hw
      simp only [hWdef, Set.mem_ofPred_eq] at hw
      obtain ⟨ℓ, hℓ⟩ := hw
      simp only [hDdef, Set.mem_ofPred_eq] at hℓ
      obtain ⟨s, hsS, q, _hqlen, hqavoid⟩ := hℓ
      refine ⟨hqavoid w (end_mem q), s, hsS, q, hqavoid⟩
    · rintro ⟨hwP, s, hsS, q, hqavoid⟩
      simp only [hWdef, Set.mem_ofPred_eq]
      refine ⟨q.length, ?_⟩
      simp only [hDdef, Set.mem_ofPred_eq]
      exact ⟨s, hsS, q, rfl, hqavoid⟩
  · -- Minimality.
    intro w _hw s hsS q hqavoid
    simp only [hhdef]
    exact Nat.sInf_le ⟨s, hsS, q, rfl, hqavoid⟩


/-
ASSEMBLY — proved for real from A2 (+ proved B2).
Target type copied verbatim from the platform record for
`CycleLengthsExp.ManyLengths.tree_extension_attach`.

Attachment argument (no induction on the walk): for `x ∈ X₀`, let `q` be
its connecting path from `s ∈ S` (length `≤ k`, internals avoiding
`S ∪ P.support`). The penultimate vertex `z` of `q` is adjacent to `x`
(`Walk.adj_penultimate`); `z` lies in `W` (the `q.dropLast` path avoids
`P`, by the `X₀` dropLast-condition plus `dropLast_head`), with
`h z ≤ q.length - 1 ≤ k - 1` (B2 minimality). If `z ∈ S`, its `T₁`-level
equals its `T`-level, which is in `[m-1, m]` by `hTfront`/`hTlev`. If
`z ∉ S`, its `T₁`-level is `level_T (r z) + h z` with
`level_T (r z) ∈ [m-1, m]` (A2 frontier-neighbour + `hTfront`/`hTlev`)
and `1 ≤ h z ≤ k - 1`, so the level is in `[m, m+k-1]`. Either way the
level lies in the `k+1` values `[m-1, m+k-1]`; pigeonhole over those
levels gives `j` and `X₁` with `|X₁| ≥ |X₀|/(k+1)` attached to level `j`.
`M₁` is the max `T₁`-level over the finite set `W`.
-/
theorem solution (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G)
    (S : Set (Fin n)) (T : G.Subgraph) (v₀ : Fin n) (m : ℕ)
    (hScard : S.ncard = Nat.floor (α * (n : ℝ) / 4))
    (hTverts : T.verts = S)
    (hv₀ : v₀ ∈ S)
    (hTacyc : T.spanningCoe.IsAcyclic)
    (hTreach : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v)
    (hTlev : ∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v ≤ m)
    (hTmax : ∃ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = m)
    (hTfront : ∀ t ∈ S, ∀ q : Fin n, q ∉ S → G.Adj t q →
      m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀ t)
    (u v : Fin n) (P : G.Walk u v) (hPpath : P.IsPath)
    (hPlen : P.length = Nat.ceil (α * (n : ℝ) / 4) - 1)
    (hPdisj : ∀ w ∈ P.support, w ∉ S) :
    ∃ (T₁ : G.Subgraph) (M₁ : ℕ) (X₁ : Set (Fin n)) (j : ℕ),
      (T.verts ⊆ T₁.verts ∧
        (∀ a b : Fin n, T.spanningCoe.Adj a b → T₁.spanningCoe.Adj a b)) ∧
      T₁.spanningCoe.IsAcyclic ∧
      (∀ w ∈ T₁.verts, T₁.spanningCoe.Reachable v₀ w) ∧
      (∀ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w ≤ M₁) ∧
      (∃ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w = M₁) ∧
      (∀ w ∈ T₁.verts, w ∉ P.support) ∧
      X₁ ⊆ CycleLengthsExp.ManyLengths.X0 α G S P ∧
      ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
          ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) ≤ (X₁.ncard : ℝ) ∧
      (∀ x ∈ X₁, ∃ y ∈ T₁.verts,
        CycleLengthsExp.WellSpread.level T₁ v₀ y = j ∧ G.Adj x y) := by
  classical
  set k := CycleLengthsExp.ManyLengths.kNum α with hkdef
  -- `k ≥ 2` from `kNum α = 2 * ⌈R⌉₊ + 1` with `R > 0`.
  have hk2 : 2 ≤ k := by
    have hR : (0 : ℝ) < Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2) := by
      apply div_pos
      · exact Real.logb_pos (by norm_num) (by
          have h3 : (1 : ℝ) * α < 3 := by linarith [hα1]
          rwa [lt_div_iff₀ hα0])
      · exact Real.logb_pos (by norm_num) (by linarith [hα0])
    have hceil : 1 ≤ Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) :=
      Nat.ceil_pos.mpr hR
    have hkexp : CycleLengthsExp.ManyLengths.kNum α =
        2 * Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 1 := rfl
    rw [hkdef, hkexp]
    omega
  -- `m ≥ 1` from `hTmax` (levels are `dist + 1 ≥ 1`).
  obtain ⟨vm, hvmS, hvmlev⟩ := hTmax
  have hm1 : 1 ≤ m := by
    have h1 : 1 ≤ CycleLengthsExp.WellSpread.level T v₀ vm := by
      show 1 ≤ T.spanningCoe.dist v₀ vm + 1
      omega
    omega
  -- Deep input B2: distance to `S` avoiding `P.support`.
  obtain ⟨W, h, hSW, hWP, hhS, hhW, hparent, hWiff, hmin⟩ :=
    dist_avoid_pred_ax n G S {w | w ∈ P.support} (by
      intro w hw
      exact hPdisj w hw)
  -- Deep input A2: extension parent tree.
  obtain ⟨T₁, r, hT₁verts, hText, hT₁acyc, hT₁reach, hrW, hrS, hdist, hrfront⟩ :=
    ext_parent_tree_ax G S T v₀ hTverts hv₀ hTacyc hTreach W hSW h hhS hhW hparent
  -- Level formula in `T₁`.
  have hlevel : ∀ w ∈ W,
      CycleLengthsExp.WellSpread.level T₁ v₀ w =
        CycleLengthsExp.WellSpread.level T v₀ (r w) + h w := by
    intro w hw
    show T₁.spanningCoe.dist v₀ w + 1 = T.spanningCoe.dist v₀ (r w) + 1 + h w
    rw [hdist w hw]
    omega
  -- Attachment: every `x ∈ X₀` has a neighbour in `T₁` at a level in
  -- `[m-1, m+k-1]`, namely the penultimate vertex of its connecting path.
  have hattach_all : ∀ x ∈ CycleLengthsExp.ManyLengths.X0 α G S P,
      ∃ y ∈ T₁.verts,
        CycleLengthsExp.WellSpread.level T₁ v₀ y ∈ Finset.Icc (m - 1) (m + k - 1) ∧
        G.Adj x y := by
    intro x hx
    simp only [CycleLengthsExp.ManyLengths.X0, Set.mem_ofPred_eq] at hx
    obtain ⟨hxP, s, hsS, q, _hqpath, hqlen, hqavoid⟩ := hx
    rw [← hkdef] at hqlen
    cases q with
    | nil => exact absurd hsS (hPdisj x hxP)
    | cons hq q' =>
      have hqnil : ¬ (Walk.cons hq q').Nil :=
        Walk.not_nil_iff_lt_length.mpr (by rw [Walk.length_cons]; omega)
      have hadj : G.Adj (Walk.cons hq q').penultimate x :=
        Walk.adj_penultimate hqnil
      have hsupp : (Walk.cons hq q').support = s :: q'.support :=
        Walk.support_cons hq q'
      have hzP : (Walk.cons hq q').penultimate ∉ P.support := by
        have hmem : (Walk.cons hq q').penultimate ∈
            (Walk.cons hq q').support.dropLast :=
          Walk.penultimate_mem_dropLast_support hqnil
        rw [hsupp] at hmem
        rcases dropLast_head s q'.support (Walk.cons hq q').penultimate hmem with
          hleft | hright
        · have hzcond := hqavoid (Walk.cons hq q').penultimate
            (by rw [hsupp]; exact hleft)
          exact hzcond.2
        · rw [hright]
          exact fun hmem2 => hPdisj s hmem2 hsS
      have hdrop_avoid :
          ∀ y ∈ (Walk.cons hq q').dropLast.support,
            y ∉ {w | w ∈ P.support} := by
        intro y hy
        rw [Walk.support_dropLast hqnil, hsupp] at hy
        rcases dropLast_head s q'.support y hy with hleft | hright
        · have hycond := hqavoid y (by rw [hsupp]; exact hleft)
          exact fun hmem2 => hycond.2 hmem2
        · rw [hright]
          exact fun hmem2 => hPdisj s hmem2 hsS
      have hzW : (Walk.cons hq q').penultimate ∈ W := by
        apply (hWiff _).mpr
        refine ⟨?_, s, hsS, (Walk.cons hq q').dropLast, hdrop_avoid⟩
        exact fun hmem2 => hzP hmem2
      have hzle : h (Walk.cons hq q').penultimate ≤ (Walk.cons hq q').length - 1 := by
        have hmin' := hmin _ hzW s hsS (Walk.cons hq q').dropLast hdrop_avoid
        rwa [Walk.length_dropLast] at hmin'
      by_cases hzS : (Walk.cons hq q').penultimate ∈ S
      · refine ⟨(Walk.cons hq q').penultimate, ?_, ?_, hadj.symm⟩
        · rw [hT₁verts]; exact hSW hzS
        · rw [Finset.mem_Icc]
          have hlev : CycleLengthsExp.WellSpread.level T₁ v₀
              (Walk.cons hq q').penultimate =
              CycleLengthsExp.WellSpread.level T v₀
                (Walk.cons hq q').penultimate := by
            rw [hlevel _ (hSW hzS), hrS _ hzS, hhS _ hzS, add_zero]
          rw [hlev]
          constructor
          · exact hTfront _ hzS x (fun hmem => hPdisj x hxP hmem) hadj
          · exact le_trans (hTlev _ hzS) (by omega)
      · have hzpos : 0 < h (Walk.cons hq q').penultimate := hhW _ hzW hzS
        refine ⟨(Walk.cons hq q').penultimate, ?_, ?_, hadj.symm⟩
        · rw [hT₁verts]; exact hzW
        · rw [Finset.mem_Icc]
          have hlev : CycleLengthsExp.WellSpread.level T₁ v₀
              (Walk.cons hq q').penultimate =
              CycleLengthsExp.WellSpread.level T v₀
                (r (Walk.cons hq q').penultimate) +
                h (Walk.cons hq q').penultimate := hlevel _ hzW
          rw [hlev]
          have hrS' : r (Walk.cons hq q').penultimate ∈ S := hrW _ hzW
          have hlow : m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀
              (r (Walk.cons hq q').penultimate) := by
            obtain ⟨w, hwS, hwAdj⟩ := hrfront _ hzW hzS
            exact hTfront _ hrS' w hwS hwAdj
          have hhigh : CycleLengthsExp.WellSpread.level T v₀
              (r (Walk.cons hq q').penultimate) ≤ m := hTlev _ hrS'
          omega
  -- `M₁`: the max `T₁`-level over the finite set `W`.
  have hWne : W.toFinset.Nonempty := ⟨v₀, by simpa using hSW hv₀⟩
  obtain ⟨wstar, hwstar_mem, hwstar_max⟩ :=
    Finset.exists_max_image W.toFinset
      (fun w => CycleLengthsExp.WellSpread.level T₁ v₀ w) hWne
  -- Choice of attachment vertex for each `x ∈ X₀` (total function).
  set y : Fin n → Fin n := fun x =>
    if hx : x ∈ CycleLengthsExp.ManyLengths.X0 α G S P then
      Classical.choose (hattach_all x hx) else v₀ with hydef
  have hy : ∀ x, x ∈ CycleLengthsExp.ManyLengths.X0 α G S P →
      y x ∈ T₁.verts ∧
        CycleLengthsExp.WellSpread.level T₁ v₀ (y x) ∈ Finset.Icc (m - 1) (m + k - 1) ∧
        G.Adj x (y x) := by
    intro x hx
    have h1 : y x = Classical.choose (hattach_all x hx) := by
      simp only [hydef, dif_pos hx]
    rw [h1]
    exact Classical.choose_spec (hattach_all x hx)
  set a : Fin n → ℕ := fun x => CycleLengthsExp.WellSpread.level T₁ v₀ (y x) with hadef
  have ha_eq : ∀ x, a x = CycleLengthsExp.WellSpread.level T₁ v₀ (y x) := by
    intro x
    rw [hadef]
  have ha_mem : ∀ x ∈ (CycleLengthsExp.ManyLengths.X0 α G S P).toFinset,
      a x ∈ Finset.Icc (m - 1) (m + k - 1) := by
    intro x hx
    have hx0 : x ∈ CycleLengthsExp.ManyLengths.X0 α G S P :=
      Set.mem_toFinset.mp hx
    rw [ha_eq]
    exact (hy x hx0).2.1
  -- Pigeonhole: some level `j` carries `≥ |X₀|/(k+1)` of `X₀`.
  have hIcc_card : (Finset.Icc (m - 1) (m + k - 1)).card = k + 1 := by
    rw [Nat.card_Icc]
    omega
  have hsum : (CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.card =
      ∑ j ∈ Finset.Icc (m - 1) (m + k - 1),
        (((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.filter
          (fun x => a x = j)).card) :=
    Finset.card_eq_sum_card_fiberwise ha_mem
  obtain ⟨j, hj⟩ : ∃ j,
      ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) / ((k : ℝ) + 1) ≤
        ((((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.filter
          (fun x => a x = j)).card : ℕ) : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hFcard : (((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.card : ℕ) : ℝ) =
        ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) := by
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hsumR : (∑ j ∈ Finset.Icc (m - 1) (m + k - 1),
        ((((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.filter
          (fun x => a x = j)).card : ℕ) : ℝ)) =
        (((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.card : ℕ) : ℝ) := by
      simp only [← Nat.cast_sum, hsum]
    have hlt : (∑ j ∈ Finset.Icc (m - 1) (m + k - 1),
        ((((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset.filter
          (fun x => a x = j)).card : ℕ) : ℝ)) <
        ∑ j ∈ Finset.Icc (m - 1) (m + k - 1),
          ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) / ((k : ℝ) + 1) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.nonempty_Icc.mpr (by omega)
      · intro j _
        exact hcon j
    rw [Finset.sum_const, hIcc_card, nsmul_eq_mul] at hlt
    push_cast at hlt
    rw [hsumR, hFcard] at hlt
    have hk1ne : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hmul : ((k : ℝ) + 1) *
        (((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) / ((k : ℝ) + 1)) =
        ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) := by
      field_simp
    rw [hmul] at hlt
    exact lt_irrefl _ hlt
  -- Assemble the existential.
  refine ⟨T₁, CycleLengthsExp.WellSpread.level T₁ v₀ wstar,
    ↑(((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset).filter
      (fun x => a x = j)), j,
    ⟨?_, ?_⟩, hT₁acyc, (by rw [hT₁verts]; exact hT₁reach), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTverts, hT₁verts]; exact hSW
  · exact hText
  · intro w hw
    rw [hT₁verts] at hw
    apply hwstar_max
    simpa using hw
  · exact ⟨wstar, by rw [hT₁verts]; simpa using hwstar_mem, rfl⟩
  · intro w hw
    rw [hT₁verts] at hw
    have hnot : w ∉ {w | w ∈ P.support} := hWP w hw
    intro hmem
    exact hnot hmem
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    exact Set.mem_toFinset.mp hx.1
  · have hconv : (↑(((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset).filter
        (fun x => a x = j)) : Set (Fin n)).ncard =
        (((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset).filter
          (fun x => a x = j)).card := by
      have h1 : (↑(((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset).filter
          (fun x => a x = j)) : Set (Fin n)).ncard =
          (Finset.finite_toSet (((CycleLengthsExp.ManyLengths.X0 α G S P).toFinset).filter
            (fun x => a x = j))).toFinset.card :=
        Set.ncard_eq_toFinset_card _ (Finset.finite_toSet _)
      rw [h1, Finset.finite_toSet_toFinset]
    rw [hconv]
    exact hj
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    obtain ⟨hxF, hxj⟩ := hx
    have hx0 : x ∈ CycleLengthsExp.ManyLengths.X0 α G S P :=
      Set.mem_toFinset.mp hxF
    obtain ⟨hy1, _hIcc, hy3⟩ := hy x hx0
    refine ⟨y x, hy1, ?_, hy3⟩
    rw [← ha_eq]
    exact hxj
