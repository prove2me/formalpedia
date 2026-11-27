-- Prove2me | solution 1 for EvenCycleListing723.Main.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:51:47.463322+00:00
-- url     : https://prove2.me/submissions/42b9c55e-36b0-4b8d-a327-15a927dbd9cc

import Mathlib
import Definitions.Def_EvenCycleListing723_Main_GraphModel
import Theorems.Thm_EvenCycleListing723_Main_lemma_3_3

set_option autoImplicit false

open EvenCycleListing723.Main
open scoped BigOperators

namespace L32Aux

section Ball

variable {m : ℕ} (H : SimpleGraph (Fin m)) (A : Finset (Fin m)) (u : Fin m)

lemma mem_neighbors {B : Finset (Fin m)} {z x : Fin m} :
    x ∈ neighbors H B z ↔ x ∈ B ∧ H.Adj z x := by
  unfold neighbors; simp [Finset.mem_filter]

lemma mem_ball_zero {x : Fin m} : x ∈ ball H A u 0 ↔ x = u ∧ u ∈ A := by
  simp only [ball]
  split_ifs with h <;> simp [h]

lemma mem_ball_succ {x : Fin m} {r : ℕ} :
    x ∈ ball H A u (r + 1) ↔ x ∈ ball H A u r ∨ ∃ z ∈ ball H A u r, x ∈ A ∧ H.Adj z x := by
  simp only [ball, Finset.mem_union, Finset.mem_biUnion, mem_neighbors]

lemma ball_mono {r s : ℕ} (hrs : r ≤ s) : ball H A u r ⊆ ball H A u s := by
  induction hrs with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (fun x hx => (mem_ball_succ H A u).2 (Or.inl hx))

lemma ball_subset_A (r : ℕ) : ball H A u r ⊆ A := by
  induction r with
  | zero => intro x hx; rw [mem_ball_zero] at hx; rw [hx.1]; exact hx.2
  | succ r ih =>
    intro x hx
    rcases (mem_ball_succ H A u).1 hx with h | ⟨z, _, hxA, _⟩
    · exact ih h
    · exact hxA

lemma ball_mono_A {A' : Finset (Fin m)} (hA : A ⊆ A') (r : ℕ) :
    ball H A u r ⊆ ball H A' u r := by
  induction r with
  | zero => intro x hx; rw [mem_ball_zero] at hx ⊢; exact ⟨hx.1, hA hx.2⟩
  | succ r ih =>
    intro x hx
    rw [mem_ball_succ] at hx ⊢
    rcases hx with h | ⟨z, hz, hxA, hadj⟩
    · exact Or.inl (ih h)
    · exact Or.inr ⟨z, ih hz, hA hxA, hadj⟩

lemma root_mem_of_mem_ball {x : Fin m} {r : ℕ} (hx : x ∈ ball H A u r) : u ∈ A := by
  induction r generalizing x with
  | zero => rw [mem_ball_zero] at hx; exact hx.2
  | succ r ih =>
    rcases (mem_ball_succ H A u).1 hx with h | ⟨z, hz, _, _⟩
    · exact ih h
    · exact ih hz

/-- reachable from `u` inside `A` -/
def rc (x : Fin m) : Prop := ∃ r, x ∈ ball H A u r

/-- BFS level of `x` from `u` inside `A` -/
noncomputable def lev (x : Fin m) : ℕ := by
  classical
  exact if h : ∃ r, x ∈ ball H A u r then Nat.find h else 0

lemma mem_ball_lev {x : Fin m} (hx : rc H A u x) : x ∈ ball H A u (lev H A u x) := by
  classical
  unfold lev; rw [dif_pos (show ∃ r, x ∈ ball H A u r from hx)]; exact Nat.find_spec hx

lemma lev_le {x : Fin m} {r : ℕ} (hx : x ∈ ball H A u r) : lev H A u x ≤ r := by
  classical
  have hrc : rc H A u x := ⟨r, hx⟩
  unfold lev; rw [dif_pos (show ∃ r, x ∈ ball H A u r from hrc)]; exact Nat.find_min' hrc hx

lemma mem_ball_iff {x : Fin m} {r : ℕ} (hx : rc H A u x) :
    x ∈ ball H A u r ↔ lev H A u x ≤ r :=
  ⟨lev_le H A u, fun h => ball_mono H A u h (mem_ball_lev H A u hx)⟩

lemma rc_mem_A {x : Fin m} (hx : rc H A u x) : x ∈ A :=
  ball_subset_A H A u _ (mem_ball_lev H A u hx)

lemma eq_of_lev_zero {x : Fin m} (hx : rc H A u x) (h0 : lev H A u x = 0) : x = u := by
  have := mem_ball_lev H A u hx
  rw [h0, mem_ball_zero] at this
  exact this.1

lemma rc_root {x : Fin m} (hx : rc H A u x) : rc H A u u ∧ lev H A u u = 0 := by
  have huA : u ∈ A := root_mem_of_mem_ball H A u (mem_ball_lev H A u hx)
  have h0 : u ∈ ball H A u 0 := (mem_ball_zero H A u).2 ⟨rfl, huA⟩
  exact ⟨⟨0, h0⟩, Nat.le_zero.1 (lev_le H A u h0)⟩

lemma lev_pos_of_ne {x : Fin m} (hx : rc H A u x) (hne : x ≠ u) : 0 < lev H A u x := by
  rcases Nat.eq_zero_or_pos (lev H A u x) with h | h
  · exact absurd (eq_of_lev_zero H A u hx h) hne
  · exact h

lemma rc_adj {z x : Fin m} (hz : rc H A u z) (hxA : x ∈ A) (hadj : H.Adj z x) :
    rc H A u x ∧ lev H A u x ≤ lev H A u z + 1 := by
  have : x ∈ ball H A u (lev H A u z + 1) :=
    (mem_ball_succ H A u).2 (Or.inr ⟨z, mem_ball_lev H A u hz, hxA, hadj⟩)
  exact ⟨⟨_, this⟩, lev_le H A u this⟩

lemma exists_par {x : Fin m} (hx : rc H A u x) (hpos : 0 < lev H A u x) :
    ∃ z, rc H A u z ∧ lev H A u z + 1 = lev H A u x ∧ H.Adj z x := by
  obtain ⟨r, hr⟩ : ∃ r, lev H A u x = r + 1 := ⟨lev H A u x - 1, by omega⟩
  have h1 := mem_ball_lev H A u hx
  rw [hr, mem_ball_succ] at h1
  rcases h1 with h | ⟨z, hz, hxA, hadj⟩
  · have := lev_le H A u h; omega
  · refine ⟨z, ⟨r, hz⟩, ?_, hadj⟩
    have hzr := lev_le H A u hz
    by_contra hne
    have hlt : lev H A u z < r := by omega
    have := (rc_adj H A u ⟨r, hz⟩ hxA hadj).2
    omega

/-- BFS parent -/
noncomputable def par (x : Fin m) : Fin m := by
  classical
  exact if h : rc H A u x ∧ 0 < lev H A u x then Classical.choose (exists_par H A u h.1 h.2) else x

lemma par_spec {x : Fin m} (hx : rc H A u x) (hpos : 0 < lev H A u x) :
    rc H A u (par H A u x) ∧ lev H A u (par H A u x) + 1 = lev H A u x ∧
      H.Adj (par H A u x) x := by
  have h : rc H A u x ∧ 0 < lev H A u x := ⟨hx, hpos⟩
  unfold par; rw [dif_pos h]; exact Classical.choose_spec (exists_par H A u h.1 h.2)

lemma par_of_lev_zero {x : Fin m} (h0 : lev H A u x = 0) : par H A u x = x := by
  unfold par; rw [dif_neg (fun h => absurd h.2 (by omega))]

lemma par_rc {x : Fin m} (hx : rc H A u x) :
    rc H A u (par H A u x) ∧ lev H A u (par H A u x) = lev H A u x - 1 := by
  rcases Nat.eq_zero_or_pos (lev H A u x) with h | h
  · rw [par_of_lev_zero H A u h]; exact ⟨hx, by omega⟩
  · have := par_spec H A u hx h; exact ⟨this.1, by omega⟩

lemma iter_rc {x : Fin m} (hx : rc H A u x) (i : ℕ) :
    rc H A u ((par H A u)^[i] x) ∧ lev H A u ((par H A u)^[i] x) = lev H A u x - i := by
  induction i with
  | zero => exact ⟨hx, by simp⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := par_rc H A u ih.1
    exact ⟨this.1, by rw [this.2, ih.2]; omega⟩

lemma iter_lev_eq_root {x : Fin m} (hx : rc H A u x) :
    (par H A u)^[lev H A u x] x = u := by
  have := iter_rc H A u hx (lev H A u x)
  exact eq_of_lev_zero H A u this.1 (by rw [this.2]; omega)

/-- chain in `A'` gives membership in the `A'`-ball -/
lemma mem_ball_of_chain (A' : Finset (Fin m)) :
    ∀ d : ℕ, ∀ x : Fin m, rc H A u x → lev H A u x = d →
      (∀ i ≤ d, (par H A u)^[i] x ∈ A') → x ∈ ball H A' u d := by
  intro d
  induction d with
  | zero =>
    intro x hx h0 hch
    have hxu := eq_of_lev_zero H A u hx h0
    have := hch 0 le_rfl
    simp only [Function.iterate_zero, id] at this
    rw [mem_ball_zero]; exact ⟨hxu, hxu ▸ this⟩
  | succ d ih =>
    intro x hx hd hch
    have hs := par_spec H A u hx (by omega)
    have hp : par H A u x ∈ ball H A' u d := by
      apply ih _ hs.1 (by omega)
      intro i hi
      have := hch (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hxA : x ∈ A' := by
      have := hch 0 (by omega); simpa using this
    exact (mem_ball_succ H A' u).2 (Or.inr ⟨_, hp, hxA, hs.2.2⟩)

end Ball

/-- vertices reachable by walks of length exactly `j` -/
noncomputable def W {m : ℕ} (H : SimpleGraph (Fin m)) : ℕ → Fin m → Finset (Fin m)
  | 0, y => {y}
  | j + 1, y => (neighbors H Finset.univ y).biUnion (W H j)

lemma mem_W_lev {m : ℕ} (H : SimpleGraph (Fin m)) (A : Finset (Fin m)) (u : Fin m) :
    ∀ d : ℕ, ∀ x : Fin m, rc H A u x → lev H A u x = d → u ∈ W H d x := by
  intro d
  induction d with
  | zero => intro x hx h0; rw [eq_of_lev_zero H A u hx h0]; simp [W]
  | succ d ih =>
    intro x hx hd
    have hs := par_spec H A u hx (by omega)
    simp only [W, Finset.mem_biUnion]
    exact ⟨par H A u x, (mem_neighbors H).2 ⟨Finset.mem_univ _, hs.2.2.symm⟩,
      ih _ hs.1 (by omega)⟩

lemma W_card {m : ℕ} (H : SimpleGraph (Fin m)) (D : ℝ) (hD : 0 ≤ D)
    (hmax : ∀ v, (degree H v : ℝ) ≤ 2 * D) (j : ℕ) (y : Fin m) :
    ((W H j y).card : ℝ) ≤ (2 * D) ^ j := by
  induction j generalizing y with
  | zero => simp [W]
  | succ j ih =>
    calc ((W H (j + 1) y).card : ℝ)
        ≤ ∑ z ∈ neighbors H Finset.univ y, ((W H j z).card : ℝ) := by
          simp only [W]; exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ z ∈ neighbors H Finset.univ y, (2 * D) ^ j :=
          Finset.sum_le_sum (fun z _ => ih z)
      _ = (degree H y : ℝ) * (2 * D) ^ j := by
          rw [Finset.sum_const, nsmul_eq_mul]; rfl
      _ ≤ (2 * D) * (2 * D) ^ j := by
          gcongr; exact hmax y
      _ = (2 * D) ^ (j + 1) := by ring

section Tree

variable {m : ℕ} (H : SimpleGraph (Fin m)) (A : Finset (Fin m)) (u : Fin m)
  (L : Finset (Fin m)) (h : ℕ)

noncomputable def tV : Finset (Fin m) := by
  classical
  exact (L ×ˢ Finset.range (h + 1)).image (fun q => (par H A u)^[q.2] q.1)

lemma mem_tV {x : Fin m} :
    x ∈ tV H A u L h ↔ ∃ v ∈ L, ∃ i ≤ h, (par H A u)^[i] v = x := by
  classical
  unfold tV
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨v, i, ⟨hv, hi⟩, rfl⟩; exact ⟨v, hv, i, by omega, rfl⟩
  · rintro ⟨v, hv, i, hi, rfl⟩; exact ⟨v, i, ⟨hv, by omega⟩, rfl⟩

noncomputable def tG : SimpleGraph {x // x ∈ tV H A u L h} :=
  SimpleGraph.fromRel (fun a b => a.1 ≠ u ∧ b.1 = par H A u a.1)

/-- descendant relation: `a` is an ancestor of `y` -/
def Desc (a y : Fin m) : Prop := ∃ i, (par H A u)^[i] y = a

variable {H A u L h}

lemma tV_rc (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h) {x : Fin m}
    (hx : x ∈ tV H A u L h) : rc H A u x ∧ lev H A u x ≤ h := by
  obtain ⟨v, hv, i, hi, rfl⟩ := (mem_tV H A u L h).1 hx
  have := iter_rc H A u (hL v hv).1 i
  exact ⟨this.1, by rw [this.2, (hL v hv).2]; omega⟩

lemma tV_lev_eq (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h) {x : Fin m}
    (hx : x ∈ tV H A u L h) (hxh : lev H A u x = h) : x ∈ L := by
  obtain ⟨v, hv, i, hi, rfl⟩ := (mem_tV H A u L h).1 hx
  have := iter_rc H A u (hL v hv).1 i
  rw [this.2, (hL v hv).2] at hxh
  have hi0 : i = 0 := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact h0
    · exfalso
      have hpos : 0 < h := by
        by_contra hc; omega
      omega
  subst hi0; simpa using hv

lemma par_mem_tV (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h) {x : Fin m}
    (hx : x ∈ tV H A u L h) : par H A u x ∈ tV H A u L h := by
  obtain ⟨v, hv, i, hi, rfl⟩ := (mem_tV H A u L h).1 hx
  rcases Nat.lt_or_ge i h with hlt | hge
  · refine (mem_tV H A u L h).2 ⟨v, hv, i + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply']
  · have := iter_rc H A u (hL v hv).1 i
    have h0 : lev H A u ((par H A u)^[i] v) = 0 := by rw [this.2, (hL v hv).2]; omega
    rw [par_of_lev_zero H A u h0]; exact hx

lemma root_mem_tV (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h) (hne : L.Nonempty) :
    u ∈ tV H A u L h := by
  obtain ⟨v, hv⟩ := hne
  refine (mem_tV H A u L h).2 ⟨v, hv, h, le_rfl, ?_⟩
  have := iter_lev_eq_root H A u (hL v hv).1
  rwa [(hL v hv).2] at this

lemma tG_adj_iff (a b : {x // x ∈ tV H A u L h}) :
    (tG H A u L h).Adj a b ↔ a ≠ b ∧ ((a.1 ≠ u ∧ b.1 = par H A u a.1) ∨
      (b.1 ≠ u ∧ a.1 = par H A u b.1)) := by
  unfold tG; rw [SimpleGraph.fromRel_adj]

lemma tG_adj_lev (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h)
    {a b : {x // x ∈ tV H A u L h}} (hab : (tG H A u L h).Adj a b) :
    lev H A u b.1 ≤ lev H A u a.1 + 1 ∧ lev H A u a.1 ≤ lev H A u b.1 + 1 := by
  rw [tG_adj_iff] at hab
  rcases hab.2 with ⟨hau, hb⟩ | ⟨hbu, ha⟩
  · have hrc := (tV_rc hL a.2).1
    have := par_spec H A u hrc (lev_pos_of_ne H A u hrc hau)
    rw [hb]; omega
  · have hrc := (tV_rc hL b.2).1
    have := par_spec H A u hrc (lev_pos_of_ne H A u hrc hbu)
    rw [ha]; omega

lemma tG_sub (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h)
    (a b : {x // x ∈ tV H A u L h}) (hab : (tG H A u L h).Adj a b) : H.Adj a.1 b.1 := by
  rw [tG_adj_iff] at hab
  rcases hab.2 with ⟨hau, hb⟩ | ⟨hbu, ha⟩
  · have hrc := (tV_rc hL a.2).1
    have := par_spec H A u hrc (lev_pos_of_ne H A u hrc hau)
    rw [hb]; exact this.2.2.symm
  · have hrc := (tV_rc hL b.2).1
    have := par_spec H A u hrc (lev_pos_of_ne H A u hrc hbu)
    rw [ha]; exact this.2.2

lemma walk_from_root (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h) (hne : L.Nonempty) :
    ∀ d : ℕ, ∀ x (hx : x ∈ tV H A u L h), lev H A u x = d →
      ∃ p : (tG H A u L h).Walk ⟨u, root_mem_tV hL hne⟩ ⟨x, hx⟩, p.length = d := by
  intro d
  induction d with
  | zero =>
    intro x hx h0
    have hxu := eq_of_lev_zero H A u (tV_rc hL hx).1 h0
    subst hxu
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ d ih =>
    intro x hx hd
    have hrc := (tV_rc hL hx).1
    have hs := par_spec H A u hrc (by omega)
    have hpx := par_mem_tV hL hx
    obtain ⟨p, hp⟩ := ih (par H A u x) hpx (by omega)
    have hadj : (tG H A u L h).Adj ⟨par H A u x, hpx⟩ ⟨x, hx⟩ := by
      rw [tG_adj_iff]
      refine ⟨fun heq => ?_, Or.inr ⟨fun hxu => ?_, rfl⟩⟩
      · have := congrArg Subtype.val heq
        simp only at this
        rw [this] at hs; omega
      · simp only at hxu; rw [hxu] at hd; have := (rc_root H A u hrc).2; omega
    exact ⟨p.concat hadj, by rw [SimpleGraph.Walk.length_concat, hp]⟩

lemma lev_walk (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h)
    {a b : {x // x ∈ tV H A u L h}} (p : (tG H A u L h).Walk a b) :
    lev H A u b.1 ≤ lev H A u a.1 + p.length := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
    have := tG_adj_lev hL hadj
    rw [SimpleGraph.Walk.length_cons]; omega

lemma tG_dist (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h) (hne : L.Nonempty)
    (x : {x // x ∈ tV H A u L h}) :
    (tG H A u L h).dist ⟨u, root_mem_tV hL hne⟩ x = lev H A u x.1 := by
  obtain ⟨p, hp⟩ := walk_from_root hL hne _ x.1 x.2 rfl
  apply le_antisymm
  · rw [← hp]; exact SimpleGraph.dist_le p
  · have hr : (tG H A u L h).Reachable ⟨u, root_mem_tV hL hne⟩ x := ⟨p⟩
    obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
    have := lev_walk hL q
    have h0 := (rc_root H A u (tV_rc hL x.2).1).2
    simp only at this
    omega

lemma bridge_aux
    (a : {x // x ∈ tV H A u L h}) {y z : {x // x ∈ tV H A u L h}}
    (p : (tG H A u L h).Walk y z) (hy : Desc H A u a.1 y.1)
    (hz : ¬ Desc H A u a.1 z.1) :
    ∃ w : {x // x ∈ tV H A u L h}, w.1 = par H A u a.1 ∧ s(a, w) ∈ p.edges := by
  induction p with
  | nil => exact absurd hy hz
  | @cons y y' z hadj p ih =>
    by_cases hy' : Desc H A u a.1 y'.1
    · obtain ⟨w, hw, hmem⟩ := ih hy' hz
      exact ⟨w, hw, by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ hmem⟩
    · rw [tG_adj_iff] at hadj
      obtain ⟨i, hi⟩ := hy
      rcases hadj.2 with ⟨hyu, hy'p⟩ | ⟨hy'u, hyp⟩
      · rcases i with _ | i
        · simp only [Function.iterate_zero, id] at hi
          have hya : y = a := Subtype.ext hi
          subst hya
          exact ⟨y', hy'p, by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons.2 (Or.inl rfl)⟩
        · exfalso; apply hy'; refine ⟨i, ?_⟩
          rw [hy'p, ← Function.iterate_succ_apply]; exact hi
      · exfalso; apply hy'; refine ⟨i + 1, ?_⟩
        rw [Function.iterate_succ_apply, ← hyp]; exact hi

lemma not_desc_par (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h) {a : Fin m}
    (ha : a ∈ tV H A u L h) (hau : a ≠ u) : ¬ Desc H A u a (par H A u a) := by
  rintro ⟨i, hi⟩
  have hrc := (tV_rc hL ha).1
  have hpos := lev_pos_of_ne H A u hrc hau
  have h1 := iter_rc H A u (par_rc H A u hrc).1 i
  rw [hi, (par_rc H A u hrc).2] at h1
  omega

lemma tG_acyclic (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h) :
    (tG H A u L h).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  intro p
  have hvw' := hvw
  rw [tG_adj_iff] at hvw'
  rcases hvw'.2 with ⟨hvu, hw⟩ | ⟨hwu, hv⟩
  · obtain ⟨w', hw', hmem⟩ := bridge_aux v p ⟨0, rfl⟩
      (by rw [hw]; exact not_desc_par hL v.2 hvu)
    have : w' = w := Subtype.ext (hw'.trans hw.symm)
    rwa [this] at hmem
  · obtain ⟨v', hv', hmem⟩ := bridge_aux w p.reverse ⟨0, rfl⟩
      (by rw [hv]; exact not_desc_par hL w.2 hwu)
    have : v' = v := Subtype.ext (hv'.trans hv.symm)
    subst this
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hmem
    rw [Sym2.eq_swap]; exact hmem

lemma tG_connected (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h) (hne : L.Nonempty) :
    (tG H A u L h).Connected := by
  have : Nonempty {x // x ∈ tV H A u L h} := ⟨⟨u, root_mem_tV hL hne⟩⟩
  have hr : ∀ x : {x // x ∈ tV H A u L h},
      (tG H A u L h).Reachable ⟨u, root_mem_tV hL hne⟩ x := by
    intro x
    obtain ⟨p, _⟩ := walk_from_root hL hne _ x.1 x.2 rfl
    exact ⟨p⟩
  exact ⟨fun a b => (hr a).symm.trans (hr b)⟩

lemma mem_tV_of_L {v : Fin m} (hv : v ∈ L) : v ∈ tV H A u L h :=
  (mem_tV H A u L h).2 ⟨v, hv, 0, Nat.zero_le _, rfl⟩

lemma tree_exists (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h) (hne : L.Nonempty) :
    ∃ T : RootedTreeIn H, treeDepth T h ∧ treeLayer T h = L ∧ T.vertices ⊆ A ∧
      ∀ j, ∀ y ∈ treeLayer T j, rc H A u y ∧ lev H A u y = j := by
  classical
  let T : RootedTreeIn H :=
    { vertices := tV H A u L h
      tree := tG H A u L h
      root := ⟨u, root_mem_tV hL hne⟩
      isTree := ⟨tG_connected hL hne, tG_acyclic hL⟩
      subgraph := tG_sub hL }
  have hd : ∀ x, T.tree.dist T.root x = lev H A u x.1 := tG_dist hL hne
  have hlayer : ∀ j y, y ∈ treeLayer T j ↔ y ∈ tV H A u L h ∧ lev H A u y = j := by
    intro j y
    unfold treeLayer
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, by rw [← hx, hd]⟩
    · rintro ⟨hy, hj⟩; exact ⟨⟨y, hy⟩, by rw [hd]; exact hj, rfl⟩
  obtain ⟨v0, hv0⟩ := hne
  refine ⟨T, ⟨fun v => ?_, ⟨⟨v0, mem_tV_of_L hv0⟩, ?_⟩⟩, ?_, ?_, ?_⟩
  · rw [hd]; exact (tV_rc hL v.2).2
  · rw [hd]; exact (hL v0 hv0).2
  · ext y; rw [hlayer]
    exact ⟨fun ⟨hy, hl⟩ => tV_lev_eq hL hy hl, fun hy => ⟨mem_tV_of_L hy, (hL y hy).2⟩⟩
  · intro x hx; exact rc_mem_A H A u (tV_rc hL hx).1
  · intro j y hy
    rw [hlayer] at hy
    exact ⟨(tV_rc hL hy.1).1, hy.2⟩

end Tree

section Counting

variable {m : ℕ} (H : SimpleGraph (Fin m))

lemma card_mem_sym2_le (e : Sym2 (Fin m)) :
    (Finset.univ.filter (fun y => y ∈ e)).card ≤ 2 := by
  classical
  induction e using Sym2.ind with
  | h a b =>
    calc (Finset.univ.filter (fun y => y ∈ s(a, b))).card ≤ ({a, b} : Finset (Fin m)).card := by
          apply Finset.card_le_card
          intro y hy
          rw [Finset.mem_filter, Sym2.mem_iff] at hy
          rcases hy.2 with rfl | rfl <;> simp
      _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)

lemma charge (k j : ℕ) (D : ℝ) (hD : 0 ≤ D) (hmax : ∀ v, (degree H v : ℝ) ≤ 2 * D)
    (U : Finset (Fin m)) (S : Fin m → Finset (Fin m))
    (hS : ∀ u ∈ U, ∀ y ∈ S u, u ∈ W H j y) :
    (∑ u ∈ U, (copiesMeeting H k (S u) : ℝ)) ≤ 4 * k * (2 * D) ^ j * cycleCount H k := by
  classical
  have key : ∀ E ∈ cycleCopies H k,
      ((U.filter (fun u => ∃ v ∈ S u, ∃ e ∈ E, v ∈ e)).card : ℝ) ≤ 4 * k * (2 * D) ^ j := by
    intro E hE
    have hEc : E.card = 2 * k := by
      unfold cycleCopies at hE; exact (Finset.mem_filter.1 hE).2.1
    set VE := Finset.univ.filter (fun y => ∃ e ∈ E, y ∈ e) with hVE
    have h1 : U.filter (fun u => ∃ v ∈ S u, ∃ e ∈ E, v ∈ e) ⊆ VE.biUnion (W H j) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨v, hv, e, he, hve⟩ := hu.2
      rw [Finset.mem_biUnion]
      exact ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, e, he, hve⟩, hS u hu.1 v hv⟩
    have h2 : VE.card ≤ 2 * E.card := by
      calc VE.card ≤ (E.biUnion (fun e => Finset.univ.filter (fun y => y ∈ e))).card := by
            apply Finset.card_le_card
            intro y hy
            rw [Finset.mem_filter] at hy
            obtain ⟨e, he, hye⟩ := hy.2
            exact Finset.mem_biUnion.2 ⟨e, he, Finset.mem_filter.2 ⟨Finset.mem_univ _, hye⟩⟩
        _ ≤ ∑ e ∈ E, (Finset.univ.filter (fun y => y ∈ e)).card := Finset.card_biUnion_le
        _ ≤ ∑ e ∈ E, 2 := Finset.sum_le_sum (fun e _ => card_mem_sym2_le e)
        _ = 2 * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have h2' : (VE.card : ℝ) ≤ 4 * k := by
      have : VE.card ≤ 4 * k := by omega
      exact_mod_cast this
    calc ((U.filter (fun u => ∃ v ∈ S u, ∃ e ∈ E, v ∈ e)).card : ℝ)
        ≤ ((VE.biUnion (W H j)).card : ℝ) := by exact_mod_cast Finset.card_le_card h1
      _ ≤ ∑ y ∈ VE, ((W H j y).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ y ∈ VE, (2 * D) ^ j := Finset.sum_le_sum (fun y _ => W_card H D hD hmax j y)
      _ = (VE.card : ℝ) * (2 * D) ^ j := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * k * (2 * D) ^ j := by gcongr
  have hswap : ∑ u ∈ U, copiesMeeting H k (S u) =
      ∑ E ∈ cycleCopies H k, (U.filter (fun u => ∃ v ∈ S u, ∃ e ∈ E, v ∈ e)).card := by
    unfold copiesMeeting
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hswapR : (∑ u ∈ U, (copiesMeeting H k (S u) : ℝ)) =
      ∑ E ∈ cycleCopies H k, ((U.filter (fun u => ∃ v ∈ S u, ∃ e ∈ E, v ∈ e)).card : ℝ) := by
    exact_mod_cast hswap
  rw [hswapR]
  calc ∑ E ∈ cycleCopies H k, ((U.filter (fun u => ∃ v ∈ S u, ∃ e ∈ E, v ∈ e)).card : ℝ)
      ≤ ∑ E ∈ cycleCopies H k, 4 * k * (2 * D) ^ j := Finset.sum_le_sum key
    _ = 4 * k * (2 * D) ^ j * cycleCount H k := by
      rw [Finset.sum_const, nsmul_eq_mul]; unfold cycleCount; ring

lemma cross_ge (L R A : Finset (Fin m))
    (hR : ∀ v ∈ L, neighbors H Finset.univ v \ A ⊆ R) :
    ∑ v ∈ L, (neighbors H Finset.univ v \ A).card ≤ crossEdges H L R := by
  classical
  unfold crossEdges
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_le_sum
  intro v hv
  rw [← Finset.card_filter]
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_filter]
  refine ⟨hR v hv hr, ?_⟩
  have := (Finset.mem_sdiff.1 hr).1
  rw [mem_neighbors] at this
  exact this.2

lemma cross_le (D : ℝ) (hmax : ∀ v, (degree H v : ℝ) ≤ 2 * D) (L R : Finset (Fin m)) :
    (crossEdges H L R : ℝ) ≤ 2 * D * R.card := by
  classical
  have : crossEdges H L R ≤ ∑ r ∈ R, degree H r := by
    unfold crossEdges
    rw [Finset.card_filter, Finset.sum_product_right]
    apply Finset.sum_le_sum
    intro r _
    rw [← Finset.card_filter]
    unfold degree
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [mem_neighbors]
    exact ⟨Finset.mem_univ _, hv.2.symm⟩
  calc (crossEdges H L R : ℝ) ≤ ∑ r ∈ R, (degree H r : ℝ) := by exact_mod_cast this
    _ ≤ ∑ r ∈ R, 2 * D := Finset.sum_le_sum (fun r _ => hmax r)
    _ = 2 * D * R.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end Counting

section Averaging

variable {m : ℕ}

lemma count_good (π F : Finset (Fin m)) (hd : Disjoint π F) :
    2 ^ m ≤ 2 ^ (π.card + 1) * ((Finset.univ : Finset (Finset (Fin m))).filter
      (fun A => π ⊆ A ∧ F.card ≤ 2 * (F \ A).card)).card := by
  classical
  set G := (Finset.univ : Finset (Finset (Fin m))).filter
      (fun A => π ⊆ A ∧ F.card ≤ 2 * (F \ A).card) with hG
  set X := (Finset.univ : Finset (Finset (Fin m))).filter (fun B => B ∪ π ∈ G) with hX
  have hcov : ∀ B : Finset (Fin m), B ∈ X ∨ symmDiff B F ∈ X := by
    intro B
    have e1 : F \ (B ∪ π) = F \ B := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hx, hn⟩; exact ⟨hx, fun h => hn (Or.inl h)⟩
      · rintro ⟨hx, hn⟩
        refine ⟨hx, fun h => ?_⟩
        rcases h with h | h
        · exact hn h
        · exact Finset.disjoint_left.1 hd h hx
    have e2 : F \ (symmDiff B F ∪ π) = F ∩ B := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]
      constructor
      · rintro ⟨hx, hn⟩
        refine ⟨hx, ?_⟩
        by_contra hb; exact hn (Or.inl (Or.inr ⟨hx, hb⟩))
      · rintro ⟨hx, hb⟩
        refine ⟨hx, fun h => ?_⟩
        rcases h with (⟨_, h⟩ | ⟨_, h⟩) | h
        · exact h hx
        · exact h hb
        · exact Finset.disjoint_left.1 hd h hx
    have hsum := Finset.card_sdiff_add_card_inter F B
    by_cases hc : F.card ≤ 2 * (F \ B).card
    · left
      simp only [hX, hG, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Finset.subset_union_right, by rw [e1]; exact hc⟩
    · right
      simp only [hX, hG, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Finset.subset_union_right, by rw [e2]; omega⟩
  have h1 : 2 ^ m ≤ 2 * X.card := by
    have hsub : (Finset.univ : Finset (Finset (Fin m))) ⊆
        X ∪ X.image (fun B => symmDiff B F) := by
      intro B _
      rcases hcov B with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _
          (Finset.mem_image.2 ⟨symmDiff B F, h, symmDiff_symmDiff_cancel_right F B⟩)
    calc 2 ^ m = (Finset.univ : Finset (Finset (Fin m))).card := by
          simp [Finset.card_univ, Fintype.card_finset]
      _ ≤ (X ∪ X.image (fun B => symmDiff B F)).card := Finset.card_le_card hsub
      _ ≤ X.card + (X.image (fun B => symmDiff B F)).card := Finset.card_union_le _ _
      _ ≤ X.card + X.card := Nat.add_le_add_left Finset.card_image_le _
      _ = 2 * X.card := by ring
  have h2 : X.card ≤ 2 ^ π.card * G.card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := fun B => B ∪ π)
    · intro B hB; exact (Finset.mem_filter.1 hB).2
    · intro A _
      have hsub : X.filter (fun B => B ∪ π = A) ⊆
          π.powerset.image (fun C => (A \ π) ∪ C) := by
        intro B hB
        rw [Finset.mem_filter] at hB
        rw [Finset.mem_image]
        refine ⟨B ∩ π, Finset.mem_powerset.2 Finset.inter_subset_right, ?_⟩
        rw [← hB.2]
        ext x
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
        tauto
      calc (X.filter (fun B => B ∪ π = A)).card
          ≤ (π.powerset.image (fun C => (A \ π) ∪ C)).card := Finset.card_le_card hsub
        _ ≤ π.powerset.card := Finset.card_image_le
        _ = 2 ^ π.card := Finset.card_powerset π
  calc 2 ^ m ≤ 2 * X.card := h1
    _ ≤ 2 * (2 ^ π.card * G.card) := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (π.card + 1) * G.card := by ring

lemma exists_good_A {α : Type*} (Q : Finset α) (π F : α → Finset (Fin m)) (s : ℕ)
    (hd : ∀ q ∈ Q, Disjoint (π q) (F q)) (hs : ∀ q ∈ Q, (π q).card ≤ s) :
    ∃ A : Finset (Fin m), Q.card ≤ 2 ^ (s + 1) *
      (Q.filter (fun q => π q ⊆ A ∧ (F q).card ≤ 2 * (F q \ A).card)).card := by
  classical
  by_contra hcon
  push Not at hcon
  have hlt : ∑ A : Finset (Fin m), 2 ^ (s + 1) *
      (Q.filter (fun q => π q ⊆ A ∧ (F q).card ≤ 2 * (F q \ A).card)).card <
      ∑ _A : Finset (Fin m), Q.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun A _ => hcon A)
  have hswap : ∑ A : Finset (Fin m),
      (Q.filter (fun q => π q ⊆ A ∧ (F q).card ≤ 2 * (F q \ A).card)).card =
      ∑ q ∈ Q, ((Finset.univ : Finset (Finset (Fin m))).filter
        (fun A => π q ⊆ A ∧ (F q).card ≤ 2 * (F q \ A).card)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hge : 2 ^ m * Q.card ≤ ∑ A : Finset (Fin m), 2 ^ (s + 1) *
      (Q.filter (fun q => π q ⊆ A ∧ (F q).card ≤ 2 * (F q \ A).card)).card := by
    rw [← Finset.mul_sum, hswap, Finset.mul_sum]
    calc 2 ^ m * Q.card = ∑ q ∈ Q, 2 ^ m := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro q hq
        refine (count_good (π q) (F q) (hd q hq)).trans (Nat.mul_le_mul_right _ ?_)
        exact Nat.pow_le_pow_right (by norm_num) (by linarith [hs q hq])
  have hconst : ∑ _A : Finset (Fin m), Q.card = 2 ^ m * Q.card := by
    simp [Finset.card_univ, Fintype.card_finset]
  omega

end Averaging

section Numeric

lemma alpha_pos (k : ℕ) (hk : 1 ≤ k) : 0 < alpha k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold alpha
  apply mul_pos
  · positivity
  · apply pow_pos; apply div_pos one_pos; linarith

lemma crunch1 (k D Lc Rc c n : ℝ) (hk : 2 ≤ k) (hD : 2 ≤ D) (hL : 1 ≤ Lc) (hR : 0 < Rc)
    (hRn : Rc ≤ n) (hc1 : Lc * ((D - 1) / 2) ≤ c) (hc2 : c ≤ 2 * D * Rc)
    (hheavy : 512 * k ^ 2 * n < D * Lc) :
    16 * k ^ 2 ≤ c / Lc ∧ 16 * k ^ 2 ≤ c / Rc ∧ 3 * D / 8 ≤ c / Lc ∧
      128 * D ≤ c / Lc * (c / Rc) := by
  have hLpos : 0 < Lc := by linarith
  have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
  have hk4 : 4 ≤ k ^ 2 := by nlinarith
  have hdL : (D - 1) / 2 ≤ c / Lc := by rw [le_div_iff₀ hLpos]; linarith
  have hdR : 128 * k ^ 2 ≤ c / Rc := by
    rw [le_div_iff₀ hR]
    by_contra hcon
    push Not at hcon
    have h1 : 128 * k ^ 2 * Rc ≤ 128 * k ^ 2 * n := by
      apply mul_le_mul_of_nonneg_left hRn; linarith
    have h2 : Lc * (D / 4) ≤ Lc * ((D - 1) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    nlinarith
  have hdR2 : c / Rc ≤ 2 * D := by rw [div_le_iff₀ hR]; linarith
  have hD64 : 64 * k ^ 2 ≤ D := by linarith
  have h38 : 3 * D / 8 ≤ c / Lc := by linarith
  refine ⟨by nlinarith, by nlinarith, h38, ?_⟩
  calc 128 * D ≤ (3 * D / 8) * (128 * k ^ 2) := by nlinarith
    _ ≤ c / Lc * (c / Rc) := mul_le_mul h38 hdR (by positivity) (by linarith)

lemma crunch2 (α Lc dL dR Q D : ℝ) (e j : ℕ) (hej : j ≤ e) (hα : 0 < α) (hL : 0 ≤ Lc)
    (hD : 2 ≤ D) (hdL : 3 * D / 8 ≤ dL) (hprod : 128 * D ≤ dL * dR)
    (hQ : α * Lc * dL * (dL * dR) ^ e ≤ Q) :
    α * Lc * (3 * D / 8) * (2 * D) ^ j * (if j = 0 then 1 else 64) ≤ Q := by
  have hx1 : 1 ≤ dL * dR := by linarith
  have hc0 : 0 ≤ (2 * D) ^ j * (if j = 0 then (1 : ℝ) else 64) := by
    split_ifs <;> positivity
  have hpow : (2 * D) ^ j * (if j = 0 then (1 : ℝ) else 64) ≤ (dL * dR) ^ e := by
    have h1 : (dL * dR) ^ j ≤ (dL * dR) ^ e := pow_le_pow_right₀ hx1 hej
    have h2 : (128 * D) ^ j ≤ (dL * dR) ^ j := pow_le_pow_left₀ (by positivity) hprod j
    have h3 : (2 * D) ^ j * (if j = 0 then (1 : ℝ) else 64) ≤ (128 * D) ^ j := by
      have he : (128 * D) ^ j = 64 ^ j * (2 * D) ^ j := by rw [← mul_pow]; ring
      rw [he]
      split_ifs with hj
      · subst hj; simp
      · have h64 : (64 : ℝ) ≤ 64 ^ j := le_self_pow₀ (by norm_num) hj
        have hp : 0 ≤ (2 * D) ^ j := by positivity
        nlinarith
    linarith
  have hc : 0 ≤ α * Lc := by positivity
  calc α * Lc * (3 * D / 8) * (2 * D) ^ j * (if j = 0 then 1 else 64)
      = α * Lc * ((3 * D / 8) * ((2 * D) ^ j * (if j = 0 then 1 else 64))) := by ring
    _ ≤ α * Lc * (dL * (dL * dR) ^ e) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact mul_le_mul hdL hpow hc0 (by linarith)
    _ = α * Lc * dL * (dL * dR) ^ e := by ring
    _ ≤ Q := hQ

end Numeric

section Heavy

variable {m : ℕ}

lemma heavy (k h : ℕ) (hk : 2 ≤ k) (hh : 1 ≤ h) (hhk : h ≤ k - 1) (n : ℕ) (hmn : m ≤ n)
    (H : SimpleGraph (Fin m)) (D : ℝ) (hD : 2 ≤ D) (hmax : ∀ v, (degree H v : ℝ) ≤ 2 * D)
    (A : Finset (Fin m)) (u : Fin m) (L : Finset (Fin m)) (hne : L.Nonempty)
    (hL : ∀ v ∈ L, rc H A u v ∧ lev H A u v = h)
    (hfree : ∀ v ∈ L, D - 1 ≤ 2 * ((neighbors H Finset.univ v \ A).card : ℝ))
    (hheavy : 512 * (k : ℝ) ^ 2 * n < D * L.card) :
    ∃ j ≤ h, ∃ S : Finset (Fin m), (∀ y ∈ S, u ∈ W H j y) ∧
      alpha k * L.card * (3 * D / 8) * (2 * D) ^ j * (if j = 0 then 1 else 64) ≤
        (copiesMeeting H k S : ℝ) := by
  classical
  obtain ⟨T, hdepth, hlayer, hsubA, hlev⟩ := tree_exists hL hne
  set R : Finset (Fin m) := (L.biUnion (fun v => neighbors H Finset.univ v)) \ A with hRdef
  have hRdisj : Disjoint R T.vertices := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    exact (Finset.mem_sdiff.1 hx).2 (hsubA hxT)
  have hRsub : ∀ v ∈ L, neighbors H Finset.univ v \ A ⊆ R := by
    intro v hv x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨Finset.mem_biUnion.2 ⟨v, hv, hx.1⟩, hx.2⟩
  have hcge : (L.card : ℝ) * ((D - 1) / 2) ≤ crossEdges H L R := by
    have h1 : (∑ v ∈ L, ((neighbors H Finset.univ v \ A).card : ℝ)) ≤ crossEdges H L R := by
      exact_mod_cast cross_ge H L R A hRsub
    calc (L.card : ℝ) * ((D - 1) / 2) = ∑ v ∈ L, (D - 1) / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ L, ((neighbors H Finset.univ v \ A).card : ℝ) :=
          Finset.sum_le_sum (fun v hv => by linarith [hfree v hv])
      _ ≤ _ := h1
  have hcle := cross_le H D hmax L R
  have hRn : (R.card : ℝ) ≤ n := by
    have : R.card ≤ n := (Finset.card_le_univ R).trans (by simp [hmn])
    exact_mod_cast this
  have hLc : (1 : ℝ) ≤ L.card := by
    have : 1 ≤ L.card := Finset.card_pos.2 hne
    exact_mod_cast this
  have hRpos : (0 : ℝ) < R.card := by
    by_contra hc
    push Not at hc
    have : (crossEdges H L R : ℝ) ≤ 0 := by nlinarith
    nlinarith
  obtain ⟨hdL16, hdR16, hdL38, hprod⟩ := crunch1 k D L.card R.card (crossEdges H L R) n
    (by exact_mod_cast hk) hD hLc hRpos hRn hcge hcle hheavy
  have hdL' : 16 * (k : ℝ) ^ 2 ≤ averageLeft H (treeLayer T h) R := by
    rw [hlayer]; unfold averageLeft; exact hdL16
  have hdR' : 16 * (k : ℝ) ^ 2 ≤ averageRight H (treeLayer T h) R := by
    rw [hlayer]; unfold averageRight; exact hdR16
  obtain ⟨j, hjh, hj⟩ := lemma_3_3 m h k (by omega) (by omega) hhk H T hdepth R hRdisj hdL' hdR'
  rw [hlayer] at hj
  unfold averageLeft averageRight at hj
  refine ⟨j, hjh, treeLayer T j, fun y hy => ?_, ?_⟩
  · have := hlev j y hy; exact mem_W_lev H A u j y this.1 this.2
  · exact crunch2 (alpha k) L.card _ _ _ D (k - h + j - 1) j (by omega)
      (alpha_pos k (by omega)) (by positivity) hD hdL38 hprod hj

end Heavy

section PerA

variable {m : ℕ}

lemma perA (k h : ℕ) (hk : 2 ≤ k) (hh : 1 ≤ h) (hhk : h ≤ k - 1) (n : ℕ) (hmn : m ≤ n)
    (H : SimpleGraph (Fin m)) (D : ℝ) (hD : 2 ≤ D) (hmax : ∀ v, (degree H v : ℝ) ≤ 2 * D)
    (A : Finset (Fin m)) (P' : Finset (Fin m × Fin m))
    (hP' : ∀ p ∈ P', rc H A p.1 p.2 ∧ lev H A p.1 p.2 = h ∧
      D - 1 ≤ 2 * ((neighbors H Finset.univ p.2 \ A).card : ℝ)) :
    D * P'.card ≤ 512 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 +
      8 * (k : ℝ) ^ 2 * cycleCount H k / alpha k := by
  classical
  set U := P'.image Prod.fst with hU
  set Lof : Fin m → Finset (Fin m) :=
    fun u => (P'.filter (fun p => p.1 = u)).image Prod.snd with hLof
  have hcard : P'.card = ∑ u ∈ U, (Lof u).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := U)
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    apply Finset.sum_congr rfl
    intro u _
    rw [hLof]
    rw [Finset.card_image_of_injOn]
    intro p hp q hq hpq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) hpq
  have hLprop : ∀ u ∈ U, (Lof u).Nonempty ∧ (∀ v ∈ Lof u, rc H A u v ∧ lev H A u v = h) ∧
      ∀ v ∈ Lof u, D - 1 ≤ 2 * ((neighbors H Finset.univ v \ A).card : ℝ) := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
    refine ⟨⟨p.2, Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨hp, rfl⟩, rfl⟩⟩, ?_, ?_⟩
    · intro v hv
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
      rw [Finset.mem_filter] at hq
      rw [← hq.2]; exact ⟨(hP' q hq.1).1, (hP' q hq.1).2.1⟩
    · intro v hv
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
      exact (hP' q (Finset.mem_filter.1 hq).1).2.2
  have hex : ∀ u, ∃ j : ℕ, ∃ S : Finset (Fin m),
      (u ∈ U → 512 * (k : ℝ) ^ 2 * n < D * (Lof u).card →
        j ≤ h ∧ (∀ y ∈ S, u ∈ W H j y) ∧
        alpha k * (Lof u).card * (3 * D / 8) * (2 * D) ^ j * (if j = 0 then 1 else 64) ≤
          (copiesMeeting H k S : ℝ)) := by
    intro u
    by_cases hu : u ∈ U ∧ 512 * (k : ℝ) ^ 2 * n < D * (Lof u).card
    · obtain ⟨hne, hL, hfree⟩ := hLprop u hu.1
      obtain ⟨j, hj, S, hS, hineq⟩ :=
        heavy k h hk hh hhk n hmn H D hD hmax A u (Lof u) hne hL hfree hu.2
      exact ⟨j, S, fun _ _ => ⟨hj, hS, hineq⟩⟩
    · exact ⟨0, ∅, fun h1 h2 => absurd ⟨h1, h2⟩ hu⟩
  choose jf Sf hjS using hex
  have hα := alpha_pos k (by omega)
  have ht : (0 : ℝ) ≤ cycleCount H k := Nat.cast_nonneg _
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set Uh := U.filter (fun u => 512 * (k : ℝ) ^ 2 * n < D * (Lof u).card) with hUh
  set Ul := U.filter (fun u => ¬ (512 * (k : ℝ) ^ 2 * n < D * (Lof u).card)) with hUl
  have hsplit : D * P'.card = ∑ u ∈ Uh, D * (Lof u).card + ∑ u ∈ Ul, D * (Lof u).card := by
    rw [Finset.sum_filter_add_sum_filter_not, hcard]; push_cast; rw [Finset.mul_sum]
  have hlight : ∑ u ∈ Ul, D * (Lof u).card ≤ 512 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
    have hUl_card : (Ul.card : ℝ) ≤ n := by
      have : Ul.card ≤ n := (Finset.card_le_univ Ul).trans (by simp [hmn])
      exact_mod_cast this
    calc ∑ u ∈ Ul, D * (Lof u).card ≤ ∑ u ∈ Ul, 512 * (k : ℝ) ^ 2 * n :=
          Finset.sum_le_sum (fun u hu => by
            have := (Finset.mem_filter.1 hu).2
            push Not at this
            exact this)
      _ = Ul.card * (512 * (k : ℝ) ^ 2 * n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * (512 * (k : ℝ) ^ 2 * n) := by
          apply mul_le_mul_of_nonneg_right hUl_card; positivity
      _ = 512 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 := by ring
  have hheavy : (∑ u ∈ Uh, D * (Lof u).card) * alpha k ≤ 8 * k ^ 2 * cycleCount H k := by
    have hmaps : ∀ u ∈ Uh, jf u ∈ Finset.range (h + 1) := by
      intro u hu
      have hu' := Finset.mem_filter.1 hu
      have := (hjS u hu'.1 hu'.2).1
      exact Finset.mem_range.2 (by omega)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_mul]
    have hj : ∀ j ∈ Finset.range (h + 1),
        (∑ u ∈ Uh.filter (fun u => jf u = j), D * (Lof u).card) * alpha k ≤
          (if j = 0 then 32 * (k : ℝ) / 3 else k / 6) * cycleCount H k := by
      intro j _
      set Uj := Uh.filter (fun u => jf u = j) with hUj
      have hmemj : ∀ u ∈ Uj, u ∈ U ∧ 512 * (k : ℝ) ^ 2 * n < D * (Lof u).card ∧ jf u = j := by
        intro u hu
        have hu' := Finset.mem_filter.1 hu
        have hu'' := Finset.mem_filter.1 hu'.1
        exact ⟨hu''.1, hu''.2, hu'.2⟩
      have hch := charge H k j D (by linarith) hmax Uj Sf (fun u hu y hy => by
        obtain ⟨h1, h2, h3⟩ := hmemj u hu
        have := (hjS u h1 h2).2.1 y hy
        rwa [h3] at this)
      have hlow : ∀ u ∈ Uj, (D * (Lof u).card) *
          (alpha k * (3 / 8) * (2 * D) ^ j * (if j = 0 then 1 else 64)) ≤
            (copiesMeeting H k (Sf u) : ℝ) := by
        intro u hu
        obtain ⟨h1, h2, h3⟩ := hmemj u hu
        have := (hjS u h1 h2).2.2
        rw [h3] at this
        calc (D * (Lof u).card) * (alpha k * (3 / 8) * (2 * D) ^ j * (if j = 0 then 1 else 64))
            = alpha k * (Lof u).card * (3 * D / 8) * (2 * D) ^ j *
                (if j = 0 then 1 else 64) := by ring
          _ ≤ _ := this
      have hsum := (Finset.sum_le_sum hlow).trans hch
      rw [← Finset.sum_mul] at hsum
      set X := ∑ u ∈ Uj, D * (Lof u).card
      have hpos : 0 < (2 * D) ^ j := by positivity
      split_ifs at hsum ⊢ with hj0
      · subst hj0
        simp only [pow_zero, mul_one] at hsum
        nlinarith
      · have : (X * alpha k * 24) * (2 * D) ^ j ≤ (4 * k * cycleCount H k) * (2 * D) ^ j := by
          nlinarith
        have := le_of_mul_le_mul_right this hpos
        nlinarith
    calc ∑ j ∈ Finset.range (h + 1),
          (∑ u ∈ Uh.filter (fun u => jf u = j), D * (Lof u).card) * alpha k
        ≤ ∑ j ∈ Finset.range (h + 1),
          (if j = 0 then 32 * (k : ℝ) / 3 else k / 6) * cycleCount H k := Finset.sum_le_sum hj
      _ = (32 * (k : ℝ) / 3 + h * (k / 6)) * cycleCount H k := by
          rw [Finset.sum_range_succ']
          simp only [Nat.add_one_ne_zero, if_false, if_true, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ 8 * k ^ 2 * cycleCount H k := by
          apply mul_le_mul_of_nonneg_right _ ht
          have hhr : (h : ℝ) + 1 ≤ k := by
            have : h + 1 ≤ k := by omega
            exact_mod_cast this
          have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
          nlinarith
  have hheavy' : ∑ u ∈ Uh, D * (Lof u).card ≤ 8 * (k : ℝ) ^ 2 * cycleCount H k / alpha k := by
    rw [le_div_iff₀ hα]; exact hheavy
  rw [hsplit]
  linarith

end PerA

section PerH

variable {m : ℕ}

/-- the vertex set of a shortest path from `p.1` to `p.2` (BFS parents in `H`) -/
noncomputable def piPath (H : SimpleGraph (Fin m)) (h : ℕ) (p : Fin m × Fin m) : Finset (Fin m) :=
  (Finset.range (h + 1)).image (fun i => (par H Finset.univ p.1)^[i] p.2)

/-- the neighbours of `p.2` off the path -/
noncomputable def freeN (H : SimpleGraph (Fin m)) (h : ℕ) (p : Fin m × Fin m) : Finset (Fin m) :=
  neighbors H Finset.univ p.2 \ piPath H h p

lemma perH (k h : ℕ) (hk : 2 ≤ k) (hh : 1 ≤ h) (hhk : h ≤ k - 1) (n : ℕ) (hmn : m ≤ n)
    (H : SimpleGraph (Fin m)) (D : ℝ) (hD : 2 ≤ D) (hmax : ∀ v, (degree H v : ℝ) ≤ 2 * D)
    (Ph : Finset (Fin m × Fin m))
    (hPh : ∀ p ∈ Ph, rc H Finset.univ p.1 p.2 ∧ lev H Finset.univ p.1 p.2 = h ∧
      D ≤ degree H p.2) :
    D * Ph.card ≤ 2 ^ (h + 2) * (512 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 +
      8 * (k : ℝ) ^ 2 * cycleCount H k / alpha k) := by
  classical
  have hd : ∀ p ∈ Ph, Disjoint (piPath H h p) (freeN H h p) := fun p _ => by
    unfold freeN; exact Finset.disjoint_sdiff
  have hs : ∀ p ∈ Ph, (piPath H h p).card ≤ h + 1 := fun p _ => by
    unfold piPath; exact Finset.card_image_le.trans (by simp)
  obtain ⟨A, hA⟩ := exists_good_A Ph (piPath H h) (freeN H h) (h + 1) hd hs
  set P' := Ph.filter (fun q => piPath H h q ⊆ A ∧
    (freeN H h q).card ≤ 2 * (freeN H h q \ A).card) with hP'def
  have hP' : ∀ p ∈ P', rc H A p.1 p.2 ∧ lev H A p.1 p.2 = h ∧
      D - 1 ≤ 2 * ((neighbors H Finset.univ p.2 \ A).card : ℝ) := by
    intro p hp
    rw [hP'def, Finset.mem_filter] at hp
    obtain ⟨hpP, hπA, hFA⟩ := hp
    obtain ⟨hrc, hlev, hdeg⟩ := hPh p hpP
    have hball : p.2 ∈ ball H A p.1 h :=
      mem_ball_of_chain H Finset.univ p.1 A h p.2 hrc hlev (fun i hi => hπA (by
        unfold piPath
        exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩))
    have hrcA : rc H A p.1 p.2 := ⟨h, hball⟩
    have hlevA : lev H A p.1 p.2 = h := by
      apply le_antisymm (lev_le H A p.1 hball)
      by_contra hlt
      push Not at hlt
      have h1 := mem_ball_lev H A p.1 hrcA
      have h2 := ball_mono_A H A p.1 (Finset.subset_univ A) _ h1
      have := lev_le H Finset.univ p.1 h2
      omega
    have hNπ : neighbors H Finset.univ p.2 ∩ piPath H h p ⊆
        {par H Finset.univ p.1 p.2} := by
      intro x hx
      rw [Finset.mem_inter, mem_neighbors] at hx
      obtain ⟨⟨_, hadj⟩, hxπ⟩ := hx
      unfold piPath at hxπ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hxπ
      rw [Finset.mem_range] at hi
      rw [Finset.mem_singleton]
      have hit := iter_rc H Finset.univ p.1 hrc i
      rcases i with _ | _ | i
      · simp at hadj
      · rfl
      · exfalso
        have := (rc_adj H Finset.univ p.1 hit.1 (Finset.mem_univ _) hadj.symm).2
        rw [hit.2, hlev] at this
        omega
    have hFcard : degree H p.2 ≤ (freeN H h p).card + 1 := by
      have h1 := Finset.card_sdiff_add_card_inter (neighbors H Finset.univ p.2) (piPath H h p)
      have h2 : (neighbors H Finset.univ p.2 ∩ piPath H h p).card ≤ 1 :=
        (Finset.card_le_card hNπ).trans (by simp)
      unfold degree freeN
      omega
    have hFA' : (freeN H h p \ A).card ≤ (neighbors H Finset.univ p.2 \ A).card := by
      apply Finset.card_le_card
      intro x hx
      unfold freeN at hx
      rw [Finset.mem_sdiff, Finset.mem_sdiff] at hx
      exact Finset.mem_sdiff.2 ⟨hx.1.1, hx.2⟩
    refine ⟨hrcA, hlevA, ?_⟩
    have h3 : degree H p.2 ≤ 2 * (neighbors H Finset.univ p.2 \ A).card + 1 := by omega
    have h4 : (degree H p.2 : ℝ) ≤ 2 * ((neighbors H Finset.univ p.2 \ A).card : ℝ) + 1 := by
      exact_mod_cast h3
    linarith
  have hmain := perA k h hk hh hhk n hmn H D hD hmax A P' hP'
  have hA' : (Ph.card : ℝ) ≤ 2 ^ (h + 2) * P'.card := by exact_mod_cast hA
  calc D * Ph.card ≤ D * (2 ^ (h + 2) * P'.card) := by
        apply mul_le_mul_of_nonneg_left hA'; linarith
    _ = 2 ^ (h + 2) * (D * P'.card) := by ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hmain; positivity

end PerH

end L32Aux

open L32Aux in
theorem solution (k : ℕ) (hk : 2 ≤ k) (n m : ℕ) (hmn : m ≤ n)
    (H : SimpleGraph (Fin m)) (D : ℝ) (hD : 2 ≤ D)
    (hmax : ∀ v, (degree H v : ℝ) ≤ 2 * D)
    (P : Finset (Fin m × Fin m))
    (hP : ∀ p ∈ P, D ≤ (degree H p.2 : ℝ) ∧
      p.2 ∈ ball H Finset.univ p.1 (k - 1)) :
    (∑ p ∈ P, (degree H p.1 : ℝ)) ≤
      pairQuadraticCoefficient k * (n : ℝ) ^ 2 +
        pairCycleCoefficient k * (cycleCount H k : ℝ) := by
  classical
  set X : ℝ := 512 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 + 8 * (k : ℝ) ^ 2 * cycleCount H k / alpha k
    with hX
  have hmaps : ∀ p ∈ P, lev H Finset.univ p.1 p.2 ∈ Finset.range k := by
    intro p hp
    have := lev_le H Finset.univ p.1 (hP p hp).2
    exact Finset.mem_range.2 (by omega)
  have hcardN := Finset.card_eq_sum_card_fiberwise
    (f := fun p : Fin m × Fin m => lev H Finset.univ p.1 p.2) (t := Finset.range k) hmaps
  have hcard : (P.card : ℝ) = ∑ h ∈ Finset.range k,
      ((P.filter (fun p => lev H Finset.univ p.1 p.2 = h)).card : ℝ) := by
    exact_mod_cast hcardN
  have hrange : Finset.range k = insert 0 (Finset.Icc 1 (k - 1)) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hDm : ∀ v, (degree H v : ℝ) ≤ m := by
    intro v
    have : degree H v ≤ m := by
      unfold degree; exact (Finset.card_le_univ _).trans (by simp)
    exact_mod_cast this
  have h0 : D * (P.filter (fun p => lev H Finset.univ p.1 p.2 = 0)).card ≤ (n : ℝ) ^ 2 := by
    set P0 := P.filter (fun p => lev H Finset.univ p.1 p.2 = 0) with hP0
    rcases P0.eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    · have hcm : P0.card ≤ m := by
        have := Finset.card_le_card_of_injOn (s := P0) (t := (Finset.univ : Finset (Fin m))) Prod.fst
          (fun p _ => Finset.mem_coe.2 (Finset.mem_univ _)) (by
            intro p hp q hq hpq
            rw [Finset.mem_coe, hP0, Finset.mem_filter] at hp hq
            have e1 := eq_of_lev_zero H Finset.univ p.1 ⟨_, (hP p hp.1).2⟩ hp.2
            have e2 := eq_of_lev_zero H Finset.univ q.1 ⟨_, (hP q hq.1).2⟩ hq.2
            exact Prod.ext hpq (by rw [e1, e2]; exact hpq))
        simpa using this
      obtain ⟨p, hp⟩ := hne
      have hDle : D ≤ m := ((hP p (Finset.mem_filter.1 hp).1).1).trans (hDm _)
      have hcm' : (P0.card : ℝ) ≤ m := by exact_mod_cast hcm
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      calc D * P0.card ≤ (m : ℝ) * m := mul_le_mul hDle hcm' (Nat.cast_nonneg _) hm0
        _ ≤ (n : ℝ) ^ 2 := by nlinarith
  have hh : ∀ h ∈ Finset.Icc 1 (k - 1),
      D * (P.filter (fun p => lev H Finset.univ p.1 p.2 = h)).card ≤ 2 ^ (h + 2) * X := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    apply perH k h hk hh.1 hh.2 n hmn H D hD hmax
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨⟨_, (hP p hp.1).2⟩, hp.2, (hP p hp.1).1⟩
  have hDP : D * P.card ≤ (n : ℝ) ^ 2 + (bucketSum k : ℝ) * X := by
    rw [hcard, Finset.mul_sum, hrange, Finset.sum_insert (by simp)]
    have hb : (bucketSum k : ℝ) * X = ∑ h ∈ Finset.Icc 1 (k - 1), 2 ^ (h + 2) * X := by
      unfold bucketSum; push_cast; rw [Finset.sum_mul]
    rw [hb]
    exact add_le_add h0 (Finset.sum_le_sum hh)
  have hdeg : (∑ p ∈ P, (degree H p.1 : ℝ)) ≤ 2 * D * P.card := by
    calc (∑ p ∈ P, (degree H p.1 : ℝ)) ≤ ∑ p ∈ P, 2 * D := Finset.sum_le_sum (fun p _ => hmax _)
      _ = 2 * D * P.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have heq : pairQuadraticCoefficient k * (n : ℝ) ^ 2 +
      pairCycleCoefficient k * (cycleCount H k : ℝ) = 2 * ((n : ℝ) ^ 2 + (bucketSum k : ℝ) * X) := by
    unfold pairQuadraticCoefficient pairCycleCoefficient
    rw [hX]; ring
  rw [heq]
  linarith
