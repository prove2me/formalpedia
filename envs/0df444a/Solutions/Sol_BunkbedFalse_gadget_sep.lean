-- Prove2me | solution 1 for BunkbedFalse.gadget_sep
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T18:30:32.729288+00:00
-- url     : https://prove2.me/submissions/a471eeab-e066-432a-9a36-f42f57977871

import Definitions.Def_BunkbedPercolation

open Bunkbed Finset

namespace TryL53

open SimpleGraph

/-! ## Generic reachability tools -/

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A predicate preserved by every edge is preserved along reachability. -/
private lemma reach_invariant {G : SimpleGraph V} (p : V → Prop)
    (h : ∀ u v : V, G.Adj u v → p u → p v) {u v : V} (hr : G.Reachable u v) : p u → p v := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact id
  | cons hadj _ ih => exact fun hu => ih (h _ _ hadj hu)

private lemma adj_of_mem {S : Finset (Sym2 V)} {u v : V} (h : s(u, v) ∈ S) (hne : u ≠ v) :
    (ofEdges S).Adj u v :=
  (SimpleGraph.fromEdgeSet_adj _).2 ⟨Finset.mem_coe.2 h, hne⟩

private lemma mem_of_adj {S : Finset (Sym2 V)} {u v : V} (h : (ofEdges S).Adj u v) :
    s(u, v) ∈ S :=
  Finset.mem_coe.1 ((SimpleGraph.fromEdgeSet_adj _).1 h).1

/-- If `z` is not reachable from `u`, then any walk out of `u` avoids all edges through `z`. -/
private lemma walk_avoid (S : Finset (Sym2 V)) (z : V) {u w : V}
    (p : (ofEdges S).Walk u w) :
    ¬ (ofEdges S).Reachable z u →
      (ofEdges (S.filter (fun e => z ∉ e))).Reachable u w := by
  induction p with
  | nil => intro _; exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj q ih =>
      intro hu
      have hSab : s(a, b) ∈ S := mem_of_adj hadj
      have hab : a ≠ b := hadj.ne
      have hza : z ≠ a := by
        intro hz; subst hz; exact hu (SimpleGraph.Reachable.refl _)
      have hzb : ¬ (ofEdges S).Reachable z b := by
        intro hr
        exact hu (hr.trans hadj.symm.reachable)
      have hzb' : z ≠ b := by
        intro hz; subst hz; exact hzb (SimpleGraph.Reachable.refl _)
      have hmem : s(a, b) ∈ S.filter (fun e => z ∉ e) := by
        refine Finset.mem_filter.2 ⟨hSab, ?_⟩
        simp only [Sym2.mem_iff]
        exact fun h => h.elim (fun h => hza h) (fun h => hzb' h)
      exact (adj_of_mem hmem hab).reachable.trans (ih hzb)

end Generic

/-! ## The gadget -/

/-- The path edges of the gadget: those avoiding the hub `0`. -/
private def pathSet (n : ℕ) : Finset (Sym2 (Fin (n + 1))) :=
  (gadgetE n).filter (fun e => (0 : Fin (n + 1)) ∉ e)

private lemma mem_gadgetE {n : ℕ} {e : Sym2 (Fin (n + 1))} :
    e ∈ gadgetE n ↔ ∃ x y : Fin (n + 1),
      ((x = 0 ∧ y ≠ 0) ∨ (1 ≤ x.val ∧ y.val = x.val + 1)) ∧ s(x, y) = e := by
  simp [gadgetE, Finset.mem_image, Finset.mem_filter, Prod.exists]

private lemma one_val {n : ℕ} (hn : 1 ≤ n) : ((1 : Fin (n + 1)) : ℕ) = 1 := by
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)

private lemma pathSet_subset (n : ℕ) : pathSet n ⊆ gadgetE n := Finset.filter_subset _ _

/-- Description of the members of `pathSet`. -/
private lemma mem_pathSet {n : ℕ} {e : Sym2 (Fin (n + 1))} (he : e ∈ pathSet n) :
    ∃ x y : Fin (n + 1), 1 ≤ x.val ∧ y.val = x.val + 1 ∧ s(x, y) = e := by
  have h0 : (0 : Fin (n + 1)) ∉ e := (Finset.mem_filter.1 he).2
  have hg : e ∈ gadgetE n := (Finset.mem_filter.1 he).1
  rw [mem_gadgetE] at hg
  obtain ⟨x, y, hxy, hex⟩ := hg
  rcases hxy with ⟨hx0, hy0⟩ | ⟨hx1, hy1⟩
  · exfalso
    rw [hx0] at hex
    rw [← hex] at h0
    exact h0 (Sym2.mem_mk_left _ _)
  · exact ⟨x, y, hx1, hy1, hex⟩

/-- Every path edge lies in `pathSet`. -/
private lemma pathEdge_mem {n : ℕ} {x y : Fin (n + 1)} (h1 : 1 ≤ x.val)
    (h2 : y.val = x.val + 1) : s(x, y) ∈ pathSet n := by
  refine Finset.mem_filter.2 ⟨mem_gadgetE.2 ⟨x, y, Or.inr ⟨h1, h2⟩, rfl⟩, ?_⟩
  simp only [Sym2.mem_iff]
  rintro (h | h)
  · have hv : (0 : Fin (n + 1)).val = x.val := by rw [h]
    rw [Fin.val_zero] at hv; omega
  · have hv : (0 : Fin (n + 1)).val = y.val := by rw [h]
    rw [Fin.val_zero] at hv; omega

/-- The hub `0` is in no path edge. -/
private lemma zero_not_mem_pathSet {n : ℕ} {e : Sym2 (Fin (n + 1))} (he : e ∈ pathSet n) :
    (0 : Fin (n + 1)) ∉ e := (Finset.mem_filter.1 he).2

/-- Walking along the path connects `1` to every `vₘ`. -/
private lemma reach_path (n : ℕ) (hn : 1 ≤ n) :
    ∀ m : ℕ, ∀ h : m < n + 1, 1 ≤ m →
      (ofEdges (pathSet n)).Reachable 1 ⟨m, h⟩ := by
  intro m
  induction m with
  | zero => intro _ h1; exact absurd h1 (by omega)
  | succ k ih =>
      intro h h1
      rcases Nat.lt_or_ge 0 k with hk | hk
      · have hkn : k < n + 1 := by omega
        have hrec := ih hkn (by omega)
        have hmem : s((⟨k, hkn⟩ : Fin (n + 1)), (⟨k + 1, h⟩ : Fin (n + 1))) ∈ pathSet n :=
          pathEdge_mem (show 1 ≤ k by omega) (show k + 1 = k + 1 from rfl)
        have hne : (⟨k, hkn⟩ : Fin (n + 1)) ≠ ⟨k + 1, h⟩ := by
          simp [Fin.ext_iff]
        exact hrec.trans (adj_of_mem hmem hne).reachable
      · have hk0 : k = 0 := by omega
        subst hk0
        have hEq : (⟨0 + 1, h⟩ : Fin (n + 1)) = 1 := by
          rw [Fin.ext_iff, one_val hn]
        rw [hEq]

private lemma reach_one (n : ℕ) (hn : 1 ≤ n) {x : Fin (n + 1)} (hx : x ≠ 0) :
    (ofEdges (pathSet n)).Reachable 1 x := by
  have hval : 1 ≤ x.val := by
    rcases Nat.eq_zero_or_pos x.val with h | h
    · exact absurd (Fin.ext h : x = 0) hx
    · exact h
  have h := reach_path n hn x.val x.isLt hval
  simpa using h

/-! ## The event holds at exactly one configuration -/

private lemma event_iff (n : ℕ) (hn : 3 ≤ n) {S : Finset (Sym2 (Fin (n + 1)))}
    (hS : S ⊆ gadgetE n) :
    ((ofEdges S).Reachable 1 (Fin.last n) ∧ ¬ (ofEdges S).Reachable 0 1) ↔ S = pathSet n := by
  constructor
  · rintro ⟨hreach, hsep⟩
    set S' : Finset (Sym2 (Fin (n + 1))) := S.filter (fun e => (0 : Fin (n + 1)) ∉ e) with hS'def
    have hS'sub : S' ⊆ S := Finset.filter_subset _ _
    -- reachability survives in the 0-avoiding subgraph
    have hreach' : (ofEdges S').Reachable 1 (Fin.last n) := by
      obtain ⟨p⟩ := hreach
      exact walk_avoid S 0 p hsep
    -- every path edge is present in `S'`
    have hall : ∀ x y : Fin (n + 1), 1 ≤ x.val → y.val = x.val + 1 → s(x, y) ∈ S' := by
      intro x y hx1 hy1
      by_contra hnot
      have hinv : ∀ u v : Fin (n + 1), (ofEdges S').Adj u v → u.val ≤ x.val → v.val ≤ x.val := by
        intro u v hadj hu
        have hmem : s(u, v) ∈ S' := mem_of_adj hadj
        have h0 : (0 : Fin (n + 1)) ∉ s(u, v) := (Finset.mem_filter.1 hmem).2
        have hgmem : s(u, v) ∈ pathSet n :=
          Finset.mem_filter.2 ⟨hS (Finset.mem_filter.1 hmem).1, h0⟩
        obtain ⟨a, b, ha1, hb1, hab⟩ := mem_pathSet hgmem
        rcases Sym2.eq_iff.1 hab with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
        · subst hau; subst hbv
          rcases Nat.lt_or_ge a.val x.val with hlt | hge
          · omega
          · exfalso
            have hax : a = x := Fin.ext (by omega)
            have hbx : b = y := Fin.ext (by omega)
            rw [hax, hbx] at hmem
            exact hnot hmem
        · subst hav; subst hbu
          omega
      have h1k : ((1 : Fin (n + 1)) : ℕ) ≤ x.val := by rw [one_val (by omega)]; exact hx1
      have hend := reach_invariant (fun z : Fin (n + 1) => z.val ≤ x.val) hinv hreach' h1k
      rw [Fin.val_last] at hend
      have := y.isLt
      omega
    -- hence all path edges lie in `S`
    have hpath_sub : pathSet n ⊆ S := by
      intro e he
      obtain ⟨x, y, hx1, hy1, hxy⟩ := mem_pathSet he
      rw [← hxy]
      exact hS'sub (hall x y hx1 hy1)
    -- no spoke is open
    have hno_spoke : ∀ e ∈ S, (0 : Fin (n + 1)) ∉ e := by
      intro e he h0
      obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.1 h0
      have hg : e ∈ gadgetE n := hS he
      have hx0 : x ≠ 0 := by
        intro hx00
        subst hx00
        rw [mem_gadgetE] at hg
        obtain ⟨u, v, huv, hev⟩ := hg
        rw [hx] at hev
        rcases huv with ⟨hu0, hv0⟩ | ⟨hu1, hv1⟩
        · rcases Sym2.eq_iff.1 hev with ⟨_, h2'⟩ | ⟨_, h2'⟩ <;> exact hv0 h2'
        · rcases Sym2.eq_iff.1 hev with ⟨h1', _⟩ | ⟨h1', _⟩ <;>
            (rw [h1'] at hu1; simp at hu1)
      have hmemS : s((0 : Fin (n + 1)), x) ∈ S := by rw [← hx]; exact he
      have hadj : (ofEdges S).Adj 0 x := adj_of_mem hmemS (fun h => hx0 h.symm)
      have hr1 : (ofEdges S).Reachable 1 x :=
        (reach_one n (by omega) hx0).mono
          (SimpleGraph.fromEdgeSet_mono (by exact_mod_cast hpath_sub))
      exact hsep (hadj.reachable.trans hr1.symm)
    refine Finset.Subset.antisymm ?_ hpath_sub
    intro e he
    exact Finset.mem_filter.2 ⟨hS he, hno_spoke e he⟩
  · rintro rfl
    refine ⟨?_, ?_⟩
    · have hlast : (Fin.last n) ≠ 0 := by
        rw [Ne, Fin.ext_iff, Fin.val_last, Fin.val_zero]
        omega
      exact reach_one n (by omega) hlast
    · intro hr
      have hinv : ∀ u v : Fin (n + 1), (ofEdges (pathSet n)).Adj u v → u = 0 → v = 0 := by
        intro u v hadj hu
        exfalso
        have hmem : s(u, v) ∈ pathSet n := mem_of_adj hadj
        have h0 : (0 : Fin (n + 1)) ∉ s(u, v) := zero_not_mem_pathSet hmem
        exact h0 (by rw [← hu]; exact Sym2.mem_mk_left _ _)
      have hzero := reach_invariant (fun z : Fin (n + 1) => z = 0) hinv hr rfl
      rw [Fin.ext_iff, one_val (by omega), Fin.val_zero] at hzero
      omega

/-! ## Counting -/

private lemma card_pathSet (n : ℕ) (hn : 1 ≤ n) : (pathSet n).card = n - 1 := by
  have hb : (pathSet n).card = (Finset.Ioo (0 : Fin (n + 1)) (Fin.last n)).card := by
    refine (Finset.card_bij
      (fun (a : Fin (n + 1)) (ha : a ∈ Finset.Ioo (0 : Fin (n + 1)) (Fin.last n)) =>
        s(a, (⟨a.val + 1, by
            have h2 := (Finset.mem_Ioo.1 ha).2
            rw [Fin.lt_def, Fin.val_last] at h2
            omega⟩ : Fin (n + 1)))) ?_ ?_ ?_).symm
    · intro a ha
      have h1 := (Finset.mem_Ioo.1 ha).1
      rw [Fin.lt_def, Fin.val_zero] at h1
      exact pathEdge_mem (show 1 ≤ a.val by omega) (show a.val + 1 = a.val + 1 from rfl)
    · intro a₁ ha₁ a₂ ha₂ heq
      rcases Sym2.eq_iff.1 heq with ⟨h1', _⟩ | ⟨h1', h2'⟩
      · exact h1'
      · exfalso
        rw [Fin.ext_iff] at h1' h2'
        simp only at h1' h2'
        omega
    · intro e he
      obtain ⟨x, y, hx1, hy1, hxy⟩ := mem_pathSet he
      have hyn : x.val + 1 < n + 1 := by have := y.isLt; omega
      refine ⟨x, Finset.mem_Ioo.2 ⟨?_, ?_⟩, ?_⟩
      · rw [Fin.lt_def, Fin.val_zero]; omega
      · rw [Fin.lt_def, Fin.val_last]; omega
      · rw [← hxy]
        congr 1
        exact (Fin.ext (by omega) : y = _).symm
  rw [hb, Fin.card_Ioo, Fin.val_last, Fin.val_zero]
  omega

private lemma card_spokes (n : ℕ) (hn : 1 ≤ n) :
    ((gadgetE n) \ (pathSet n)).card = n := by
  have hb : ((gadgetE n) \ (pathSet n)).card
      = ((Finset.univ : Finset (Fin (n + 1))).erase 0).card := by
    refine (Finset.card_bij
      (fun (a : Fin (n + 1)) (_ : a ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0) =>
        s((0 : Fin (n + 1)), a)) ?_ ?_ ?_).symm
    · intro a ha
      have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
      refine Finset.mem_sdiff.2 ⟨mem_gadgetE.2 ⟨0, a, Or.inl ⟨rfl, ha0⟩, rfl⟩, ?_⟩
      intro hmem
      exact (Finset.mem_filter.1 hmem).2 (Sym2.mem_mk_left _ _)
    · intro a₁ ha₁ a₂ ha₂ heq
      have ha₁0 : a₁ ≠ 0 := Finset.ne_of_mem_erase ha₁
      rcases Sym2.eq_iff.1 heq with ⟨_, h2'⟩ | ⟨h1', h2'⟩
      · exact h2'
      · exact absurd h2' ha₁0
    · intro e he
      have hg : e ∈ gadgetE n := (Finset.mem_sdiff.1 he).1
      have hnp : e ∉ pathSet n := (Finset.mem_sdiff.1 he).2
      have h0 : (0 : Fin (n + 1)) ∈ e := by
        by_contra h
        exact hnp (Finset.mem_filter.2 ⟨hg, h⟩)
      obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.1 h0
      have hx0 : x ≠ 0 := by
        intro hx00
        subst hx00
        rw [mem_gadgetE] at hg
        obtain ⟨u, v, huv, hev⟩ := hg
        rw [hx] at hev
        rcases huv with ⟨hu0, hv0⟩ | ⟨hu1, hv1⟩
        · rcases Sym2.eq_iff.1 hev with ⟨_, h2'⟩ | ⟨_, h2'⟩ <;> exact hv0 h2'
        · rcases Sym2.eq_iff.1 hev with ⟨h1', _⟩ | ⟨h1', _⟩ <;>
            (rw [h1'] at hu1; simp at hu1)
      exact ⟨x, Finset.mem_erase.2 ⟨hx0, Finset.mem_univ _⟩, hx.symm⟩
  rw [hb, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-! ## The weight of the single surviving configuration -/

private lemma weight_pathSet (n : ℕ) (P : ℚ) (hn : 1 ≤ n) :
    weight (gadgetE n) (gadgetW n P) (pathSet n) = P ^ (2 * n - 1) := by
  rw [weight]
  have h1 : (∏ e ∈ pathSet n, gadgetW n P e) = P ^ (pathSet n).card := by
    rw [Finset.prod_congr rfl (fun e he => ?_), Finset.prod_const]
    have h0 : (0 : Fin (n + 1)) ∉ e := zero_not_mem_pathSet he
    rw [gadgetW, if_neg h0]
  have h2 : (∏ e ∈ gadgetE n \ pathSet n, (1 - gadgetW n P e))
      = P ^ ((gadgetE n) \ (pathSet n)).card := by
    rw [Finset.prod_congr rfl (fun e he => ?_), Finset.prod_const]
    have hg : e ∈ gadgetE n := (Finset.mem_sdiff.1 he).1
    have hnp : e ∉ pathSet n := (Finset.mem_sdiff.1 he).2
    have h0 : (0 : Fin (n + 1)) ∈ e := by
      by_contra h
      exact hnp (Finset.mem_filter.2 ⟨hg, h⟩)
    rw [gadgetW, if_pos h0]
    ring
  rw [h1, h2, ← pow_add, card_pathSet n hn, card_spokes n hn]
  congr 1
  omega

end TryL53

theorem solution (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    Pa_bc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) = P ^ (2 * n - 1) := by
  rw [Pa_bc, probOf]
  rw [Finset.sum_eq_single_of_mem (TryL53.pathSet n)
      (Finset.mem_powerset.2 (TryL53.pathSet_subset n)) ?_]
  · rw [if_pos ((TryL53.event_iff n hn (TryL53.pathSet_subset n)).2 rfl)]
    exact TryL53.weight_pathSet n P (by omega)
  · intro b hb hne
    refine if_neg ?_
    intro hev
    exact hne ((TryL53.event_iff n hn (Finset.mem_powerset.1 hb)).1 hev)
