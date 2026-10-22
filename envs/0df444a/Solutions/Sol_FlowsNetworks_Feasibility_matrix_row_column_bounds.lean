-- Prove2me | solution 1 for FlowsNetworks.Feasibility.matrix_row_column_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:24:50.839295+00:00
-- url     : https://prove2.me/submissions/d72ff914-8381-4191-8a83-148ed3dbc052

import Mathlib

section g70fn1
variable {N : Type} [Fintype N] [DecidableEq N]
set_option linter.unusedSectionVars false

structure g70fn1_Net (N : Type) [Fintype N] [DecidableEq N] where
  arcs : Finset (N × N)
  low : N → N → ℝ
  cap : N → N → ℝ

def g70fn1_nfo (G : g70fn1_Net N) (f : N → N → ℝ) (x : N) : ℝ :=
  (∑ p ∈ G.arcs.filter (fun p => p.1 = x), f p.1 p.2) -
    ∑ p ∈ G.arcs.filter (fun p => p.2 = x), f p.1 p.2


def g70fn1_Res (G : g70fn1_Net N) (f : N → N → ℝ) (ε : ℝ) (u w : N) : Prop :=
  ((u, w) ∈ G.arcs ∧ f u w + ε ≤ G.cap u w) ∨ ((w, u) ∈ G.arcs ∧ G.low w u + ε ≤ f w u)

def g70fn1_Step (R : N → N → Prop) (a b : N × List N) : Prop :=
  R a.1 b.1 ∧ b.1 ∉ a.2 ∧ b.2 = b.1 :: a.2

def g70fn1_e (a b : N) : N → N → ℝ := fun u w => if u = a ∧ w = b then 1 else 0

theorem g70fn1_nfo_add (G : g70fn1_Net N) (f g : N → N → ℝ) (z : N) :
    g70fn1_nfo G (f + g) z = g70fn1_nfo G f z + g70fn1_nfo G g z := by
  unfold g70fn1_nfo; simp only [Pi.add_apply, Finset.sum_add_distrib]; ring

theorem g70fn1_nfo_smul (G : g70fn1_Net N) (f : N → N → ℝ) (c : ℝ) (z : N) :
    g70fn1_nfo G (c • f) z = c * g70fn1_nfo G f z := by
  unfold g70fn1_nfo; simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring

theorem g70fn1_nfo_e (G : g70fn1_Net N) (a b : N) (hab : (a, b) ∈ G.arcs) (z : N) :
    g70fn1_nfo G (g70fn1_e a b) z = (if z = a then 1 else 0) - (if z = b then 1 else 0) := by
  unfold g70fn1_nfo g70fn1_e
  have key : ∀ (q : N × N → N), (∑ p ∈ G.arcs.filter (fun p => q p = z),
      (if p.1 = a ∧ p.2 = b then (1:ℝ) else 0)) = if z = q (a, b) then 1 else 0 := by
    intro q
    rw [Finset.sum_filter]
    have : ∀ p ∈ G.arcs, (if q p = z then (if p.1 = a ∧ p.2 = b then (1:ℝ) else 0) else 0)
        = if p = (a, b) then (if z = q (a, b) then 1 else 0) else 0 := by
      intro p _
      by_cases h : p = (a, b)
      · subst h; simp [eq_comm]
      · have : ¬ (p.1 = a ∧ p.2 = b) := fun ⟨h1, h2⟩ => h (Prod.ext h1 h2)
        simp [h, this]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' G.arcs (a, b), if_pos hab]
  rw [key (fun p => p.1), key (fun p => p.2)]

theorem g70fn1_step_mem {R : N → N → Prop} {s : N} {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn1_Step R) (s, [s]) (x, l)) : x ∈ l ∧ s ∈ l := by
  generalize hb : (x, l) = b at h
  induction h generalizing x l with
  | refl => cases hb; simp
  | tail _ hst ih =>
    rename_i b c
    obtain ⟨b1, b2⟩ := b
    obtain ⟨_, _, h3⟩ := hst
    cases hb
    simp only at h3
    subst h3
    exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (ih rfl).2⟩

theorem g70fn1_step_prefix {R : N → N → Prop} {s : N} {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn1_Step R) (s, [s]) (x, l)) :
    ∀ z ∈ l, ∃ l', Relation.ReflTransGen (g70fn1_Step R) (s, [s]) (z, l') := by
  generalize hb : (x, l) = b at h
  induction h generalizing x l with
  | refl => cases hb; intro z hz; simp at hz; subst hz; exact ⟨_, Relation.ReflTransGen.refl⟩
  | tail h1 hst ih =>
    rename_i b c
    obtain ⟨b1, b2⟩ := b
    obtain ⟨_, _, h3⟩ := hst
    cases hb
    simp only at h3
    subst h3
    intro z hz
    rcases List.mem_cons.1 hz with hz | hz
    · subst hz; exact ⟨_, h1.tail ⟨by assumption, by assumption, rfl⟩⟩
    · exact ih rfl z hz

theorem g70fn1_simple {R : N → N → Prop} {s x : N} (h : Relation.ReflTransGen R s x) :
    ∃ l, Relation.ReflTransGen (g70fn1_Step R) (s, [s]) (x, l) := by
  induction h with
  | refl => exact ⟨_, Relation.ReflTransGen.refl⟩
  | @tail y x _ hyx ih =>
    obtain ⟨l, hl⟩ := ih
    by_cases hx : x ∈ l
    · exact g70fn1_step_prefix hl x hx
    · exact ⟨x :: l, hl.tail ⟨hyx, hx, rfl⟩⟩

/-- augmentation along a simple residual path -/
theorem g70fn1_augment (G : g70fn1_Net N) (f : N → N → ℝ) (s : N)
    (hnn : ∀ p ∈ G.arcs, G.low p.1 p.2 ≤ f p.1 p.2) (hcap : ∀ p ∈ G.arcs, f p.1 p.2 ≤ G.cap p.1 p.2)
    (ε : ℝ) (hε : 0 < ε) {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn1_Step (g70fn1_Res G f ε)) (s, [s]) (x, l)) :
    ∃ g : N → N → ℝ, (∀ a b, g a b ≠ 0 → a ∈ l ∧ b ∈ l) ∧
      (∀ a b, (a, b) ∉ G.arcs → g a b = 0) ∧
      (∀ p ∈ G.arcs, G.low p.1 p.2 ≤ f p.1 p.2 + g p.1 p.2 ∧ f p.1 p.2 + g p.1 p.2 ≤ G.cap p.1 p.2) ∧
      (∀ z, g70fn1_nfo G g z = (if z = s then ε else 0) - (if z = x then ε else 0)) ∧
      (∀ a b, ∃ k : ℤ, g a b = k * ε) := by
  generalize hb : (x, l) = b at h
  induction h generalizing x l with
  | refl =>
    cases hb
    refine ⟨0, by simp, by simp, fun p hp => by simpa using ⟨hnn p hp, hcap p hp⟩, ?_, ?_⟩
    · intro z; unfold g70fn1_nfo; simp
    · intro a b; exact ⟨0, by simp⟩
  | tail h1 hst ih =>
    rename_i b c
    obtain ⟨y, l0⟩ := b
    obtain ⟨hR, hx, h3⟩ := hst
    cases hb
    simp only at h3 hR hx
    subst h3
    obtain ⟨g, hgl, hgs, hgf, hgn, hgk⟩ := ih rfl
    have hyl : y ∈ l0 := (g70fn1_step_mem h1).1
    have hxy : x ≠ y := fun e => hx (e ▸ hyl)
    rcases hR with ⟨harc, hres⟩ | ⟨harc, hres⟩
    · refine ⟨g + ε • g70fn1_e y x, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab
        by_cases he : a = y ∧ b = x
        · obtain ⟨rfl, rfl⟩ := he; simp [hyl]
        · have : g a b ≠ 0 := by simpa [g70fn1_e, he] using hab
          have := hgl a b this
          exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩
      · intro a b hab
        have : ¬ (a = y ∧ b = x) := by rintro ⟨rfl, rfl⟩; exact hab harc
        simp [g70fn1_e, this, hgs a b hab]
      · intro p hp
        obtain ⟨p1, p2⟩ := p
        by_cases he : p1 = y ∧ p2 = x
        · obtain ⟨rfl, rfl⟩ := he
          have hg0 : g p1 p2 = 0 := by
            by_contra hne; exact hx (hgl _ _ hne).2
          have hfp := hnn _ hp
          simp only [Pi.add_apply, Pi.smul_apply, g70fn1_e, and_self, if_true, smul_eq_mul,
            mul_one, hg0] at hfp ⊢
          constructor <;> linarith
        · simpa [g70fn1_e, he] using hgf _ hp
      · intro z
        rw [g70fn1_nfo_add, g70fn1_nfo_smul, g70fn1_nfo_e G y x harc, hgn]
        clear ih h1 hgf hgk hgl hgs hgn
        by_cases hzs : z = s <;> by_cases hzy : z = y <;> by_cases hzx : z = x <;>
          simp_all
      · intro a b
        obtain ⟨k, hk⟩ := hgk a b
        by_cases he : a = y ∧ b = x
        · refine ⟨k + 1, ?_⟩
          have hk' := hk
          rw [he.1, he.2] at hk' ⊢
          simp only [Pi.add_apply, Pi.smul_apply, g70fn1_e, and_self, if_true,
            smul_eq_mul, mul_one, hk']
          push_cast; ring
        · exact ⟨k, by simp [g70fn1_e, he, hk]⟩
    · refine ⟨g - ε • g70fn1_e x y, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab
        by_cases he : a = x ∧ b = y
        · obtain ⟨rfl, rfl⟩ := he; simp [hyl]
        · have : g a b ≠ 0 := by simpa [g70fn1_e, he] using hab
          have := hgl a b this
          exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩
      · intro a b hab
        have : ¬ (a = x ∧ b = y) := by rintro ⟨rfl, rfl⟩; exact hab harc
        simp [g70fn1_e, this, hgs a b hab]
      · intro p hp
        obtain ⟨p1, p2⟩ := p
        by_cases he : p1 = x ∧ p2 = y
        · obtain ⟨rfl, rfl⟩ := he
          have hg0 : g p1 p2 = 0 := by
            by_contra hne; exact hx (hgl _ _ hne).1
          have hfp := hcap _ hp
          simp only [Pi.sub_apply, Pi.smul_apply, g70fn1_e, and_self, if_true, smul_eq_mul,
            mul_one, hg0] at hfp ⊢
          constructor <;> linarith
        · simpa [g70fn1_e, he] using hgf _ hp
      · intro z
        rw [sub_eq_add_neg, g70fn1_nfo_add, ← neg_smul, g70fn1_nfo_smul,
          g70fn1_nfo_e G x y harc, hgn]
        clear ih h1 hgf hgk hgl hgs hgn
        by_cases hzs : z = s <;> by_cases hzy : z = y <;> by_cases hzx : z = x <;>
          simp_all
      · intro a b
        obtain ⟨k, hk⟩ := hgk a b
        by_cases he : a = x ∧ b = y
        · refine ⟨k - 1, ?_⟩
          have hk' := hk
          rw [he.1, he.2] at hk' ⊢
          simp only [Pi.sub_apply, Pi.smul_apply, g70fn1_e, and_self, if_true,
            smul_eq_mul, mul_one, hk']
          push_cast; ring
        · exact ⟨k, by simp [g70fn1_e, he, hk]⟩


def g70fn1_AS (G : g70fn1_Net N) (f : N → N → ℝ) (u w : N) : Prop :=
  ((u, w) ∈ G.arcs ∧ f u w < G.cap u w) ∨ ((w, u) ∈ G.arcs ∧ G.low w u < f w u)

def g70fn1_fsum (G : g70fn1_Net N) (g : N → N → ℝ) (X Y : Finset N) : ℝ :=
  ∑ p ∈ G.arcs.filter (fun p => p.1 ∈ X ∧ p.2 ∈ Y), g p.1 p.2

def g70fn1_IsInt (r : ℝ) : Prop := ∃ k : ℤ, r = k

theorem g70fn1_int_lt {a b : ℝ} (ha : g70fn1_IsInt a) (hb : g70fn1_IsInt b) (h : a < b) :
    a + 1 ≤ b := by
  obtain ⟨m, rfl⟩ := ha; obtain ⟨n, rfl⟩ := hb
  have : m < n := by exact_mod_cast h
  have : m + 1 ≤ n := this
  exact_mod_cast this

theorem g70fn1_res_mono (G : g70fn1_Net N) (f : N → N → ℝ) {ε ε' : ℝ} (h : ε' ≤ ε) {u w : N}
    (hr : g70fn1_Res G f ε u w) : g70fn1_Res G f ε' u w := by
  rcases hr with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨a, by linarith⟩
  · exact Or.inr ⟨a, by linarith⟩

theorem g70fn1_res_exists (G : g70fn1_Net N) (f : N → N → ℝ) (s : N) {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn1_Step (g70fn1_AS G f)) (s, [s]) (x, l)) :
    ∃ ε > 0, Relation.ReflTransGen (g70fn1_Step (g70fn1_Res G f ε)) (s, [s]) (x, l) := by
  generalize hb : (x, l) = b at h
  induction h generalizing x l with
  | refl => cases hb; exact ⟨1, one_pos, Relation.ReflTransGen.refl⟩
  | tail h1 hst ih =>
    rename_i b c
    obtain ⟨y, l0⟩ := b
    obtain ⟨hR, hx, h3⟩ := hst
    cases hb
    simp only at h3 hR hx
    obtain ⟨ε, hε, hrt⟩ := ih rfl
    have : ∃ δ > 0, g70fn1_Res G f δ y x := by
      rcases hR with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨G.cap y x - f y x, by linarith, Or.inl ⟨a, by linarith⟩⟩
      · exact ⟨f x y - G.low x y, by linarith, Or.inr ⟨a, by linarith⟩⟩
    obtain ⟨δ, hδ, hr⟩ := this
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩
    refine Relation.ReflTransGen.tail (Relation.ReflTransGen.mono (fun a b (hab : g70fn1_Step (g70fn1_Res G f ε) a b) => (⟨g70fn1_res_mono G f (min_le_left _ _) hab.1, hab.2⟩ : g70fn1_Step (g70fn1_Res G f (min ε δ)) a b)) _ _ hrt) ?_
    refine ⟨g70fn1_res_mono G f (min_le_right _ _) hr, hx, ?_⟩
    simpa using h3

theorem g70fn1_res_one_path (G : g70fn1_Net N) (f : N → N → ℝ)
    (hI : ∀ p ∈ G.arcs, g70fn1_IsInt (f p.1 p.2) ∧ g70fn1_IsInt (G.low p.1 p.2) ∧
      g70fn1_IsInt (G.cap p.1 p.2)) (s : N) {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn1_Step (g70fn1_AS G f)) (s, [s]) (x, l)) :
    Relation.ReflTransGen (g70fn1_Step (g70fn1_Res G f 1)) (s, [s]) (x, l) := by
  refine Relation.ReflTransGen.mono (fun a b hab => ⟨?_, hab.2⟩) _ _ h
  rcases hab.1 with ⟨a, b⟩ | ⟨a, b⟩
  · have := hI _ a
    exact Or.inl ⟨a, g70fn1_int_lt this.1 this.2.2 b⟩
  · have := hI _ a
    exact Or.inr ⟨a, g70fn1_int_lt this.2.1 this.1 b⟩

theorem g70fn1_sum_nfo (G : g70fn1_Net N) (f : N → N → ℝ) (X : Finset N) :
    ∑ x ∈ X, g70fn1_nfo G f x = g70fn1_fsum G f X Xᶜ - g70fn1_fsum G f Xᶜ X := by
  have key : ∀ (q : N × N → N), ∑ x ∈ X, ∑ p ∈ G.arcs.filter (fun p => q p = x), f p.1 p.2
      = ∑ p ∈ G.arcs, if q p ∈ X then f p.1 p.2 else 0 := by
    intro q
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_ite_eq]
  unfold g70fn1_nfo g70fn1_fsum
  rw [Finset.sum_sub_distrib, key (fun p => p.1), key (fun p => p.2), Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Finset.mem_compl]
  by_cases a : p.1 ∈ X <;> by_cases b : p.2 ∈ X <;> simp [a, b]

theorem g70fn1_nfo_neg (G : g70fn1_Net N) (f : N → N → ℝ) (z : N) :
    g70fn1_nfo G (-f) z = - g70fn1_nfo G f z := by
  unfold g70fn1_nfo; simp only [Pi.neg_apply, Finset.sum_neg_distrib]; ring

/-- reachability: if node x has too much net inflow, some node with slack is reachable -/
theorem g70fn1_reach (G : g70fn1_Net N) (f : N → N → ℝ)
    (hlow : ∀ p ∈ G.arcs, G.low p.1 p.2 ≤ f p.1 p.2) (hcap : ∀ p ∈ G.arcs, f p.1 p.2 ≤ G.cap p.1 p.2)
    (hi : N → ℝ)
    (C1 : ∀ X : Finset N, g70fn1_fsum G G.low Xᶜ X - ∑ x ∈ X, hi x ≤ g70fn1_fsum G G.cap X Xᶜ)
    (x : N) (hx : hi x < - g70fn1_nfo G f x) :
    ∃ y, y ≠ x ∧ - g70fn1_nfo G f y < hi y ∧
      ∃ l, Relation.ReflTransGen (g70fn1_Step (g70fn1_AS G f)) (x, [x]) (y, l) := by
  classical
  by_contra hne
  push_neg at hne
  set Y := Finset.univ.filter (fun y => Relation.ReflTransGen (g70fn1_AS G f) x y) with hY
  have hxY : x ∈ Y := by simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and]; exact Relation.ReflTransGen.refl
  have hYle : ∀ y ∈ Y, y ≠ x → hi y ≤ - g70fn1_nfo G f y := by
    intro y hy hyx
    by_contra hlt; push_neg at hlt
    simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨l, hl⟩ := g70fn1_simple hy
    exact hne y hyx hlt l hl
  have hsum : ∑ y ∈ Y, hi y < ∑ y ∈ Y, - g70fn1_nfo G f y := by
    rw [← Finset.add_sum_erase Y _ hxY, ← Finset.add_sum_erase Y _ hxY]
    have := Finset.sum_le_sum (fun y hy => hYle y (Finset.mem_of_mem_erase hy)
      (Finset.ne_of_mem_erase hy))
    linarith
  rw [Finset.sum_neg_distrib, g70fn1_sum_nfo] at hsum
  have a1 : g70fn1_fsum G f Y Yᶜ = g70fn1_fsum G G.cap Y Yᶜ := by
    unfold g70fn1_fsum
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_compl] at hp
    by_contra hne2
    have hlt : f p.1 p.2 < G.cap p.1 p.2 := lt_of_le_of_ne (hcap p hp.1) hne2
    apply hp.2.2
    have h1 := hp.2.1
    simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
    exact h1.tail (Or.inl ⟨hp.1, hlt⟩)
  have a2 : g70fn1_fsum G f Yᶜ Y = g70fn1_fsum G G.low Yᶜ Y := by
    unfold g70fn1_fsum
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_compl] at hp
    by_contra hne2
    have hlt : G.low p.1 p.2 < f p.1 p.2 := lt_of_le_of_ne (hlow p hp.1) (Ne.symm hne2)
    apply hp.2.1
    have h1 := hp.2.2
    simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
    exact h1.tail (Or.inr ⟨hp.1, hlt⟩)
  have := C1 Y
  rw [a1, a2] at hsum
  linarith


theorem g70fn1_isInt_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ) (h : ∀ i ∈ s, g70fn1_IsInt (g i)) :
    g70fn1_IsInt (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨m, hm⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨n, hn⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨m + n, by rw [hm, hn]; push_cast; ring⟩

theorem g70fn1_isInt_nfo (G : g70fn1_Net N) (f : N → N → ℝ)
    (h : ∀ p ∈ G.arcs, g70fn1_IsInt (f p.1 p.2)) (z : N) : g70fn1_IsInt (g70fn1_nfo G f z) := by
  unfold g70fn1_nfo
  obtain ⟨m, hm⟩ := g70fn1_isInt_sum _ _ (fun p hp => h p (Finset.mem_filter.1 hp).1 :
    ∀ p ∈ G.arcs.filter (fun p => p.1 = z), g70fn1_IsInt (f p.1 p.2))
  obtain ⟨n, hn⟩ := g70fn1_isInt_sum _ _ (fun p hp => h p (Finset.mem_filter.1 hp).1 :
    ∀ p ∈ G.arcs.filter (fun p => p.2 = z), g70fn1_IsInt (f p.1 p.2))
  exact ⟨m - n, by rw [hm, hn]; push_cast; ring⟩

def g70fn1_V (G : g70fn1_Net N) (lo hi : N → ℝ) (f : N → N → ℝ) : ℝ :=
  ∑ z, (max 0 (- g70fn1_nfo G f z - hi z) + max 0 (lo z + g70fn1_nfo G f z))

def g70fn1_K (G : g70fn1_Net N) (f : N → N → ℝ) : Prop :=
  (∀ a b, (a, b) ∉ G.arcs → f a b = 0) ∧
    ∀ p ∈ G.arcs, G.low p.1 p.2 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2

theorem g70fn1_V_nonneg (G : g70fn1_Net N) (lo hi : N → ℝ) (f : N → N → ℝ) :
    0 ≤ g70fn1_V G lo hi f :=
  Finset.sum_nonneg fun z _ => add_nonneg (le_max_left _ _) (le_max_left _ _)

theorem g70fn1_improve (G : g70fn1_Net N) (f : N → N → ℝ) (hf : g70fn1_K G f)
    (lo hi : N → ℝ) (hlh : ∀ z, lo z ≤ hi z) (x y : N) (hyx : y ≠ x) (ε : ℝ) (hε : 0 < ε)
    (hεx : ε ≤ - g70fn1_nfo G f x - hi x) (hεy : ε ≤ hi y + g70fn1_nfo G f y) {l : List N}
    (hl : Relation.ReflTransGen (g70fn1_Step (g70fn1_Res G f ε)) (x, [x]) (y, l)) :
    ∃ g : N → N → ℝ, g70fn1_K G (f + g) ∧ g70fn1_V G lo hi (f + g) ≤ g70fn1_V G lo hi f - ε ∧
      ∀ a b, ∃ k : ℤ, g a b = k * ε := by
  obtain ⟨hsupp, hb⟩ := hf
  obtain ⟨g, -, hgs, hgf, hgn, hgk⟩ := g70fn1_augment G f x (fun p hp => (hb p hp).1)
    (fun p hp => (hb p hp).2) ε hε hl
  refine ⟨g, ⟨fun a b hab => by simp [hsupp a b hab, hgs a b hab], hgf⟩, ?_, hgk⟩
  have key : ∀ z, max 0 (- g70fn1_nfo G (f + g) z - hi z) + max 0 (lo z + g70fn1_nfo G (f + g) z)
      ≤ max 0 (- g70fn1_nfo G f z - hi z) + max 0 (lo z + g70fn1_nfo G f z) -
        (if z = x then ε else 0) := by
    intro z
    rw [g70fn1_nfo_add, hgn]
    have := hlh z
    by_cases hzx : z = x
    · subst hzx
      simp only [if_true, if_neg (Ne.symm hyx)]
      have h1 : max 0 (-(g70fn1_nfo G f z + (ε - 0)) - hi z) = -(g70fn1_nfo G f z + (ε - 0)) - hi z :=
        max_eq_right (by linarith)
      have h2 : max 0 (lo z + (g70fn1_nfo G f z + (ε - 0))) = 0 := max_eq_left (by linarith)
      have h3 : max 0 (- g70fn1_nfo G f z - hi z) = - g70fn1_nfo G f z - hi z :=
        max_eq_right (by linarith)
      have h4 := le_max_left 0 (lo z + g70fn1_nfo G f z)
      rw [h1, h2, h3]; linarith
    · simp only [if_neg hzx]
      by_cases hzy : z = y
      · subst hzy
        simp only [if_true]
        have h1 : max 0 (-(g70fn1_nfo G f z + (0 - ε)) - hi z) = 0 := max_eq_left (by linarith)
        have h2 : max 0 (lo z + (g70fn1_nfo G f z + (0 - ε))) ≤ max 0 (lo z + g70fn1_nfo G f z) :=
          max_le_max le_rfl (by linarith)
        have h3 := le_max_left 0 (- g70fn1_nfo G f z - hi z)
        rw [h1]; linarith
      · simp [hzy]
  unfold g70fn1_V
  have := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => key z)
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq'] at this
  simpa using this

/-- one improvement step for an excess violation -/
theorem g70fn1_step (G : g70fn1_Net N) (f : N → N → ℝ) (hf : g70fn1_K G f)
    (lo hi : N → ℝ) (hlh : ∀ z, lo z ≤ hi z)
    (C1 : ∀ X : Finset N, g70fn1_fsum G G.low Xᶜ X - ∑ x ∈ X, hi x ≤ g70fn1_fsum G G.cap X Xᶜ)
    (x : N) (hx : hi x < - g70fn1_nfo G f x) (I : Prop)
    (hI1 : I → ∀ p ∈ G.arcs, g70fn1_IsInt (f p.1 p.2) ∧ g70fn1_IsInt (G.low p.1 p.2) ∧
      g70fn1_IsInt (G.cap p.1 p.2))
    (hI2 : I → ∀ z, g70fn1_IsInt (hi z)) :
    ∃ ε > 0, ∃ g : N → N → ℝ, g70fn1_K G (f + g) ∧
      g70fn1_V G lo hi (f + g) ≤ g70fn1_V G lo hi f - ε ∧ (I → ε = 1 ∧ ∀ a b, g70fn1_IsInt (g a b)) := by
  obtain ⟨y, hyx, hy, l, hl⟩ := g70fn1_reach G f (fun p hp => (hf.2 p hp).1)
    (fun p hp => (hf.2 p hp).2) hi C1 x hx
  by_cases hI : I
  · have hp1 := g70fn1_res_one_path G f (hI1 hI) x hl
    have hfi : ∀ p ∈ G.arcs, g70fn1_IsInt (f p.1 p.2) := fun p hp => (hI1 hI p hp).1
    have e1 : g70fn1_IsInt (- g70fn1_nfo G f x) := by
      obtain ⟨k, hk⟩ := g70fn1_isInt_nfo G f hfi x; exact ⟨-k, by rw [hk]; push_cast; ring⟩
    have e2 := g70fn1_int_lt (hI2 hI x) e1 hx
    have e1y : g70fn1_IsInt (- g70fn1_nfo G f y) := by
      obtain ⟨k, hk⟩ := g70fn1_isInt_nfo G f hfi y; exact ⟨-k, by rw [hk]; push_cast; ring⟩
    have e3 := g70fn1_int_lt e1y (hI2 hI y) hy
    obtain ⟨g, hg1, hg2, hg3⟩ := g70fn1_improve G f hf lo hi hlh x y hyx 1 one_pos
      (by linarith) (by linarith) hp1
    refine ⟨1, one_pos, g, hg1, hg2, fun _ => ⟨rfl, fun a b => ?_⟩⟩
    obtain ⟨k, hk⟩ := hg3 a b; exact ⟨k, by rw [hk]; ring⟩
  · obtain ⟨ε1, hε1, hp⟩ := g70fn1_res_exists G f x hl
    set ε := min ε1 (min (- g70fn1_nfo G f x - hi x) (hi y + g70fn1_nfo G f y)) with hε
    have hεpos : 0 < ε := lt_min hε1 (lt_min (by linarith) (by linarith))
    have hp' : Relation.ReflTransGen (g70fn1_Step (g70fn1_Res G f ε)) (x, [x]) (y, l) :=
      Relation.ReflTransGen.mono (fun a b hab => ⟨g70fn1_res_mono G f (min_le_left _ _) hab.1,
        hab.2⟩) _ _ hp
    obtain ⟨g, hg1, hg2, -⟩ := g70fn1_improve G f hf lo hi hlh x y hyx ε hεpos
      ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _)) hp'
    exact ⟨ε, hεpos, g, hg1, hg2, fun h => absurd h hI⟩

theorem g70fn1_nfo_congr (G G' : g70fn1_Net N) (h : G'.arcs = G.arcs) (f : N → N → ℝ) (z : N) :
    g70fn1_nfo G' f z = g70fn1_nfo G f z := by
  unfold g70fn1_nfo; rw [h]

theorem g70fn1_V_neg (G G' : g70fn1_Net N) (h : G'.arcs = G.arcs) (lo hi : N → ℝ)
    (f : N → N → ℝ) : g70fn1_V G' (-hi) (-lo) f = g70fn1_V G lo hi (-f) := by
  unfold g70fn1_V
  apply Finset.sum_congr rfl
  intro z _
  rw [g70fn1_nfo_congr G G' h, g70fn1_nfo_neg, add_comm]
  simp only [Pi.neg_apply]
  congr 2 <;> ring

theorem g70fn1_fsum_neg (G : g70fn1_Net N) (g : N → N → ℝ) (X Y : Finset N) :
    g70fn1_fsum G (fun a b => - g a b) X Y = - g70fn1_fsum G g X Y := by
  unfold g70fn1_fsum; rw [Finset.sum_neg_distrib]

theorem g70fn1_improve_any (G : g70fn1_Net N) (f : N → N → ℝ) (hf : g70fn1_K G f)
    (lo hi : N → ℝ) (hlh : ∀ z, lo z ≤ hi z)
    (C1 : ∀ X : Finset N, g70fn1_fsum G G.low Xᶜ X - ∑ x ∈ X, hi x ≤ g70fn1_fsum G G.cap X Xᶜ)
    (C2 : ∀ X : Finset N, g70fn1_fsum G G.low Xᶜ X + ∑ x ∈ Xᶜ, lo x ≤ g70fn1_fsum G G.cap X Xᶜ)
    (hnot : ¬ ∀ z, lo z ≤ - g70fn1_nfo G f z ∧ - g70fn1_nfo G f z ≤ hi z) (I : Prop)
    (hI1 : I → ∀ p ∈ G.arcs, g70fn1_IsInt (f p.1 p.2) ∧ g70fn1_IsInt (G.low p.1 p.2) ∧
      g70fn1_IsInt (G.cap p.1 p.2))
    (hI2 : I → ∀ z, g70fn1_IsInt (lo z) ∧ g70fn1_IsInt (hi z)) :
    ∃ ε > 0, ∃ f' : N → N → ℝ, g70fn1_K G f' ∧
      g70fn1_V G lo hi f' ≤ g70fn1_V G lo hi f - ε ∧
      (I → ε = 1 ∧ ∀ p ∈ G.arcs, g70fn1_IsInt (f' p.1 p.2)) := by
  by_cases h1 : ∃ x, hi x < - g70fn1_nfo G f x
  · obtain ⟨x, hx⟩ := h1
    obtain ⟨ε, hε, g, hg1, hg2, hg3⟩ := g70fn1_step G f hf lo hi hlh C1 x hx I hI1
      (fun h z => (hI2 h z).2)
    refine ⟨ε, hε, f + g, hg1, hg2, fun h => ⟨(hg3 h).1, fun p hp => ?_⟩⟩
    obtain ⟨m, hm⟩ := (hI1 h p hp).1; obtain ⟨n, hn⟩ := (hg3 h).2 p.1 p.2
    exact ⟨m + n, by simp only [Pi.add_apply]; rw [hm, hn]; push_cast; ring⟩
  · push_neg at h1
    have h2 : ∃ x, - g70fn1_nfo G f x < lo x := by
      by_contra h3; push_neg at h3; exact hnot fun z => ⟨h3 z, h1 z⟩
    obtain ⟨x, hx⟩ := h2
    set G' : g70fn1_Net N := ⟨G.arcs, fun a b => - G.cap a b, fun a b => - G.low a b⟩ with hG'
    have harcs : G'.arcs = G.arcs := rfl
    have hK' : g70fn1_K G' (-f) := ⟨fun a b hab => by simp [hf.1 a b hab], fun p hp => by
      have := hf.2 p hp; simp only [hG', Pi.neg_apply]; constructor <;> linarith⟩
    have C1' : ∀ X : Finset N, g70fn1_fsum G' G'.low Xᶜ X - ∑ x ∈ X, (-lo) x ≤
        g70fn1_fsum G' G'.cap X Xᶜ := by
      intro X
      have := C2 Xᶜ
      rw [compl_compl] at this
      have e1 : g70fn1_fsum G' G'.low Xᶜ X = - g70fn1_fsum G G.cap Xᶜ X :=
        g70fn1_fsum_neg G G.cap Xᶜ X
      have e2 : g70fn1_fsum G' G'.cap X Xᶜ = - g70fn1_fsum G G.low X Xᶜ :=
        g70fn1_fsum_neg G G.low X Xᶜ
      rw [e1, e2]; simp only [Pi.neg_apply, Finset.sum_neg_distrib]; linarith
    have hx' : (-lo) x < - g70fn1_nfo G' (-f) x := by
      rw [g70fn1_nfo_congr G G' harcs, g70fn1_nfo_neg]; simp only [Pi.neg_apply]; linarith
    obtain ⟨ε, hε, g, hg1, hg2, hg3⟩ := g70fn1_step G' (-f) hK' (-hi) (-lo)
      (fun z => by simp only [Pi.neg_apply]; linarith [hlh z]) C1' x hx' I
      (fun h p hp => by
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := hI1 h p hp
        exact ⟨⟨-a, by simp [ha]⟩, ⟨-c, by simp [hG', hc]⟩, ⟨-b, by simp [hG', hb]⟩⟩)
      (fun h z => by obtain ⟨a, ha⟩ := (hI2 h z).1; exact ⟨-a, by simp [ha]⟩)
    refine ⟨ε, hε, -(-f + g), ⟨fun a b hab => by
      have := hg1.1 a b hab; simp only [Pi.add_apply, Pi.neg_apply] at this ⊢; linarith, fun p hp => by
      have := hg1.2 p hp; simp only [hG', Pi.neg_apply] at this ⊢; constructor <;> linarith⟩,
      ?_, fun h => ⟨(hg3 h).1, fun p hp => ?_⟩⟩
    · have q1 := g70fn1_V_neg G G' harcs lo hi (-f + g)
      have q2 := g70fn1_V_neg G G' harcs lo hi (-f)
      rw [neg_neg] at q2
      rw [← q1, ← q2]; exact hg2
    · obtain ⟨m, hm⟩ := (hI1 h p hp).1; obtain ⟨n, hn⟩ := (hg3 h).2 p.1 p.2
      exact ⟨m - n, by simp only [Pi.add_apply, Pi.neg_apply]; rw [hm, hn]; push_cast; ring⟩

theorem g70fn1_main (G : g70fn1_Net N) (hlc : ∀ p ∈ G.arcs, G.low p.1 p.2 ≤ G.cap p.1 p.2)
    (lo hi : N → ℝ) (hlh : ∀ z, lo z ≤ hi z)
    (C1 : ∀ X : Finset N, g70fn1_fsum G G.low Xᶜ X - ∑ x ∈ X, hi x ≤ g70fn1_fsum G G.cap X Xᶜ)
    (C2 : ∀ X : Finset N, g70fn1_fsum G G.low Xᶜ X + ∑ x ∈ Xᶜ, lo x ≤ g70fn1_fsum G G.cap X Xᶜ) :
    ∃ f, g70fn1_K G f ∧ ∀ z, lo z ≤ - g70fn1_nfo G f z ∧ - g70fn1_nfo G f z ≤ hi z := by
  set F : Set (N → N → ℝ) := {f | g70fn1_K G f} with hF
  have hcont : ∀ x, Continuous (fun f : N → N → ℝ => g70fn1_nfo G f x) := by
    intro x; unfold g70fn1_nfo; fun_prop
  have hev : ∀ x y, Continuous (fun f : N → N → ℝ => f x y) := by
    intro x y; fun_prop
  have hVc : Continuous (fun f => g70fn1_V G lo hi f) := by
    unfold g70fn1_V
    refine continuous_finset_sum _ fun z _ => ?_
    exact ((continuous_const.max ((hcont z).neg.sub continuous_const))).add
      (continuous_const.max (continuous_const.add (hcont z)))
  have hclosed : IsClosed F := by
    simp only [hF, g70fn1_K, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_eq (hev x y) continuous_const) (isClosed_iInter fun p => isClosed_iInter fun _ =>
      IsClosed.inter (isClosed_le continuous_const (hev _ _)) (isClosed_le (hev _ _) continuous_const))
  set C := ∑ p ∈ G.arcs, (|G.low p.1 p.2| + |G.cap p.1 p.2|)
  have hC : 0 ≤ C := Finset.sum_nonneg fun p _ => by positivity
  have hbdd : Bornology.IsBounded F := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨C, fun f hf => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hC]
    intro x
    rw [pi_norm_le_iff_of_nonneg hC]
    intro y
    rw [Real.norm_eq_abs]
    by_cases hxy : (x, y) ∈ G.arcs
    · have a := (hf.2 _ hxy).1
      have b := (hf.2 _ hxy).2
      have c : |G.low x y| + |G.cap x y| ≤ C := Finset.single_le_sum
        (f := fun p => |G.low p.1 p.2| + |G.cap p.1 p.2|) (fun p _ => by positivity) hxy
      simp only at a b
      have := abs_le.1 (le_refl |G.low x y|)
      have := abs_le.1 (le_refl |G.cap x y|)
      rw [abs_le]; constructor <;> linarith
    · rw [hf.1 x y hxy]; simpa using hC
  have hcpt : IsCompact F := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : F.Nonempty := ⟨fun a b => if (a, b) ∈ G.arcs then G.low a b else 0,
    fun a b hab => by simp [hab], fun p hp => by simp [hp, hlc p hp]⟩
  obtain ⟨f0, hf0, hmin⟩ := hcpt.exists_isMinOn hne hVc.continuousOn
  refine ⟨f0, hf0, ?_⟩
  by_contra hnot
  obtain ⟨ε, hε, f', hf', hV, -⟩ := g70fn1_improve_any G f0 hf0 lo hi hlh C1 C2 hnot False
    (fun h => h.elim) (fun h => h.elim)
  have := hmin hf'
  simp only [Set.mem_setOf_eq] at this
  linarith

theorem g70fn1_main_int (G : g70fn1_Net N) (hlc : ∀ p ∈ G.arcs, G.low p.1 p.2 ≤ G.cap p.1 p.2)
    (lo hi : N → ℝ) (hlh : ∀ z, lo z ≤ hi z)
    (C1 : ∀ X : Finset N, g70fn1_fsum G G.low Xᶜ X - ∑ x ∈ X, hi x ≤ g70fn1_fsum G G.cap X Xᶜ)
    (C2 : ∀ X : Finset N, g70fn1_fsum G G.low Xᶜ X + ∑ x ∈ Xᶜ, lo x ≤ g70fn1_fsum G G.cap X Xᶜ)
    (hI1 : ∀ p ∈ G.arcs, g70fn1_IsInt (G.low p.1 p.2) ∧ g70fn1_IsInt (G.cap p.1 p.2))
    (hI2 : ∀ z, g70fn1_IsInt (lo z) ∧ g70fn1_IsInt (hi z)) :
    ∃ f, g70fn1_K G f ∧ (∀ p ∈ G.arcs, g70fn1_IsInt (f p.1 p.2)) ∧
      ∀ z, lo z ≤ - g70fn1_nfo G f z ∧ - g70fn1_nfo G f z ≤ hi z := by
  have key : ∀ n : ℕ, ∀ f, g70fn1_K G f → (∀ p ∈ G.arcs, g70fn1_IsInt (f p.1 p.2)) →
      g70fn1_V G lo hi f ≤ n → ∃ f, g70fn1_K G f ∧ (∀ p ∈ G.arcs, g70fn1_IsInt (f p.1 p.2)) ∧
      ∀ z, lo z ≤ - g70fn1_nfo G f z ∧ - g70fn1_nfo G f z ≤ hi z := by
    intro n
    induction n with
    | zero =>
      intro f hf hfi hV
      by_contra hno
      have hnot : ¬ ∀ z, lo z ≤ - g70fn1_nfo G f z ∧ - g70fn1_nfo G f z ≤ hi z :=
        fun h => hno ⟨f, hf, hfi, h⟩
      obtain ⟨ε, hε, f', hf', hV', h3⟩ := g70fn1_improve_any G f hf lo hi hlh C1 C2 hnot True
        (fun _ p hp => ⟨hfi p hp, hI1 p hp⟩) (fun _ => hI2)
      have := g70fn1_V_nonneg G lo hi f'
      push_cast at hV
      linarith
    | succ n ih =>
      intro f hf hfi hV
      by_cases hfeas : ∀ z, lo z ≤ - g70fn1_nfo G f z ∧ - g70fn1_nfo G f z ≤ hi z
      · exact ⟨f, hf, hfi, hfeas⟩
      obtain ⟨ε, hε, f', hf', hV', h3⟩ := g70fn1_improve_any G f hf lo hi hlh C1 C2 hfeas True
        (fun _ p hp => ⟨hfi p hp, hI1 p hp⟩) (fun _ => hI2)
      obtain ⟨rfl, hf'i⟩ := h3 trivial
      exact ih f' hf' hf'i (by push_cast at hV; linarith)
  set f0 : N → N → ℝ := fun a b => if (a, b) ∈ G.arcs then G.low a b else 0
  exact key _ f0 ⟨fun a b hab => by simp [f0, hab], fun p hp => by simp [f0, hp, hlc p hp]⟩
    (fun p hp => by simpa [f0, hp] using (hI1 p hp).1) (Nat.le_ceil _)
end g70fn1

section g70fn1N
variable {N : Type} [Fintype N] [DecidableEq N]
set_option linter.unusedSectionVars false

theorem g70fn1_necC1 (G : g70fn1_Net N) (f : N → N → ℝ) (hf : g70fn1_K G f) (hi : N → ℝ)
    (h : ∀ z, - g70fn1_nfo G f z ≤ hi z) (X : Finset N) :
    g70fn1_fsum G G.low Xᶜ X - ∑ x ∈ X, hi x ≤ g70fn1_fsum G G.cap X Xᶜ := by
  have e := g70fn1_sum_nfo G f X
  have s : ∑ x ∈ X, - g70fn1_nfo G f x ≤ ∑ x ∈ X, hi x := Finset.sum_le_sum fun x _ => h x
  rw [Finset.sum_neg_distrib, e] at s
  have a1 : g70fn1_fsum G G.low Xᶜ X ≤ g70fn1_fsum G f Xᶜ X :=
    Finset.sum_le_sum fun p hp => (hf.2 p (Finset.mem_filter.1 hp).1).1
  have a2 : g70fn1_fsum G f X Xᶜ ≤ g70fn1_fsum G G.cap X Xᶜ :=
    Finset.sum_le_sum fun p hp => (hf.2 p (Finset.mem_filter.1 hp).1).2
  linarith

theorem g70fn1_necC2 (G : g70fn1_Net N) (f : N → N → ℝ) (hf : g70fn1_K G f) (lo : N → ℝ)
    (h : ∀ z, lo z ≤ - g70fn1_nfo G f z) (X : Finset N) :
    g70fn1_fsum G G.low Xᶜ X + ∑ x ∈ Xᶜ, lo x ≤ g70fn1_fsum G G.cap X Xᶜ := by
  have e := g70fn1_sum_nfo G f Xᶜ
  rw [compl_compl] at e
  have s : ∑ x ∈ Xᶜ, lo x ≤ ∑ x ∈ Xᶜ, - g70fn1_nfo G f x := Finset.sum_le_sum fun x _ => h x
  rw [Finset.sum_neg_distrib, e] at s
  have a1 : g70fn1_fsum G G.low Xᶜ X ≤ g70fn1_fsum G f Xᶜ X :=
    Finset.sum_le_sum fun p hp => (hf.2 p (Finset.mem_filter.1 hp).1).1
  have a2 : g70fn1_fsum G f X Xᶜ ≤ g70fn1_fsum G G.cap X Xᶜ :=
    Finset.sum_le_sum fun p hp => (hf.2 p (Finset.mem_filter.1 hp).1).2
  linarith

theorem g70fn1_nfo_full (G : g70fn1_Net N) (f : N → N → ℝ)
    (hs : ∀ a b, (a, b) ∉ G.arcs → f a b = 0) (x : N) :
    g70fn1_nfo G f x = ∑ y, f x y - ∑ y, f y x := by
  have key : ∀ q : N × N → N, ∑ p ∈ G.arcs.filter (fun p => q p = x), f p.1 p.2 =
      ∑ p : N × N, if q p = x then f p.1 p.2 else 0 := by
    intro q
    rw [← Finset.sum_filter]
    apply Finset.sum_subset (Finset.filter_subset_filter _ (Finset.subset_univ _))
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    exact hs p.1 p.2 (fun h => hp' ⟨h, hp⟩)
  unfold g70fn1_nfo
  rw [key (fun p => p.1), key (fun p => p.2), Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end g70fn1N

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 2.3 (p. 23). Let `0 ≤ a_i ≤ a'_i`
(`i = 1, …, m`), `0 ≤ b_j ≤ b'_j` (`j = 1, …, n`) and `c_ij ≥ 0` be real constants. If there are
real `m × n` matrices `f¹`, `f²` with (2.9) `a_i ≤ ∑_j f¹_ij`, `∑_i f¹_ij ≤ b'_j`, `0 ≤ f¹_ij ≤ c_ij`
and (2.10) `∑_j f²_ij ≤ a'_i`, `b_j ≤ ∑_i f²_ij`, `0 ≤ f²_ij ≤ c_ij`, then there is a real matrix
`f` with (2.11) `a_i ≤ ∑_j f_ij ≤ a'_i`, `b_j ≤ ∑_i f_ij ≤ b'_j`, `0 ≤ f_ij ≤ c_ij`. Indices run
over `Fin m` and `Fin n` (0-based) instead of `1, …, m` and `1, …, n`. -/
theorem solution (m n : ℕ) (a a' : Fin m → ℝ) (b b' : Fin n → ℝ)
    (c : Matrix (Fin m) (Fin n) ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ a' i) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ b' j)
    (hc : ∀ i j, 0 ≤ c i j)
    (h1 : ∃ f₁ : Matrix (Fin m) (Fin n) ℝ,
      (∀ i, a i ≤ ∑ j, f₁ i j) ∧ (∀ j, ∑ i, f₁ i j ≤ b' j) ∧
        ∀ i j, 0 ≤ f₁ i j ∧ f₁ i j ≤ c i j)
    (h2 : ∃ f₂ : Matrix (Fin m) (Fin n) ℝ,
      (∀ i, ∑ j, f₂ i j ≤ a' i) ∧ (∀ j, b j ≤ ∑ i, f₂ i j) ∧
        ∀ i j, 0 ≤ f₂ i j ∧ f₂ i j ≤ c i j) :
    ∃ f : Matrix (Fin m) (Fin n) ℝ,
      (∀ i, a i ≤ ∑ j, f i j ∧ ∑ j, f i j ≤ a' i) ∧
        (∀ j, b j ≤ ∑ i, f i j ∧ ∑ i, f i j ≤ b' j) ∧
        ∀ i j, 0 ≤ f i j ∧ f i j ≤ c i j := by
  classical
  obtain ⟨f₁, h1a, h1b, h1c⟩ := h1
  obtain ⟨f₂, h2a, h2b, h2c⟩ := h2
  let fo : Matrix (Fin m) (Fin n) ℝ → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ := fun F u v =>
    Sum.elim (fun i => Sum.elim (fun _ => (0:ℝ)) (fun j => F i j) v) (fun _ => 0) u
  let G : g70fn1_Net (Fin m ⊕ Fin n) :=
    ⟨Finset.univ.filter (fun p => p.1.isLeft ∧ p.2.isRight), fun _ _ => 0, fo c⟩
  have hmem : ∀ u v, (u, v) ∈ G.arcs ↔ ∃ i j, u = Sum.inl i ∧ v = Sum.inr j := by
    intro u v
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
    cases u <;> cases v <;> simp
  have hfoK : ∀ F : Matrix (Fin m) (Fin n) ℝ, (∀ i j, 0 ≤ F i j ∧ F i j ≤ c i j) → g70fn1_K G (fo F) := by
    intro F hF
    refine ⟨fun u v huv => ?_, fun p hp => ?_⟩
    · rw [hmem] at huv
      cases u <;> cases v <;> simp_all [fo]
    · obtain ⟨u, v⟩ := p
      obtain ⟨i, j, rfl, rfl⟩ := (hmem u v).1 hp
      simpa [fo, G] using hF i j
  have hnet : ∀ (F : Matrix (Fin m) (Fin n) ℝ),
      (∀ i, - g70fn1_nfo G (fo F) (Sum.inl i) = - ∑ j, F i j) ∧
      (∀ j, - g70fn1_nfo G (fo F) (Sum.inr j) = ∑ i, F i j) := by
    intro F
    have hs : ∀ u v, (u, v) ∉ G.arcs → fo F u v = 0 := by
      intro u v huv; rw [hmem] at huv; cases u <;> cases v <;> simp_all [fo]
    refine ⟨fun i => ?_, fun j => ?_⟩ <;>
      rw [g70fn1_nfo_full G _ hs] <;> simp [fo, Fintype.sum_sum_type]
  let lo : Fin m ⊕ Fin n → ℝ := Sum.elim (fun i => - a' i) b
  let hi : Fin m ⊕ Fin n → ℝ := Sum.elim (fun i => - a i) b'
  have hlh : ∀ z, lo z ≤ hi z := by
    intro z; cases z with
    | inl i => simp [lo, hi, (ha i).2]
    | inr j => simp [lo, hi, (hb j).2]
  have C1 := g70fn1_necC1 G (fo f₁) (hfoK f₁ h1c) hi (by
    intro z; cases z with
    | inl i => rw [(hnet f₁).1 i]; simp [hi, h1a i]
    | inr j => rw [(hnet f₁).2 j]; simp [hi, h1b j])
  have C2 := g70fn1_necC2 G (fo f₂) (hfoK f₂ h2c) lo (by
    intro z; cases z with
    | inl i => rw [(hnet f₂).1 i]; simp [lo, h2a i]
    | inr j => rw [(hnet f₂).2 j]; simp [lo, h2b j])
  obtain ⟨f, hK, hb'⟩ := g70fn1_main G (fun p hp => by
      obtain ⟨u, v⟩ := p
      obtain ⟨i, j, rfl, rfl⟩ := (hmem u v).1 hp
      simpa [fo, G] using hc i j) lo hi hlh C1 C2
  have hs := hK.1
  have hrow : ∀ i, - g70fn1_nfo G f (Sum.inl i) = - ∑ j, f (Sum.inl i) (Sum.inr j) := by
    intro i
    rw [g70fn1_nfo_full G f hs, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have z1 : ∀ i', f (Sum.inl i) (Sum.inl i') = 0 := fun i' => hs _ _ (by rw [hmem]; simp)
    have z2 : ∀ i', f (Sum.inl i') (Sum.inl i) = 0 := fun i' => hs _ _ (by rw [hmem]; simp)
    have z3 : ∀ j, f (Sum.inr j) (Sum.inl i) = 0 := fun j => hs _ _ (by rw [hmem]; simp)
    simp [z1, z2, z3]
  have hcol : ∀ j, - g70fn1_nfo G f (Sum.inr j) = ∑ i, f (Sum.inl i) (Sum.inr j) := by
    intro j
    rw [g70fn1_nfo_full G f hs, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have z1 : ∀ j', f (Sum.inr j) (Sum.inr j') = 0 := fun j' => hs _ _ (by rw [hmem]; simp)
    have z2 : ∀ j', f (Sum.inr j') (Sum.inr j) = 0 := fun j' => hs _ _ (by rw [hmem]; simp)
    have z3 : ∀ i, f (Sum.inr j) (Sum.inl i) = 0 := fun i => hs _ _ (by rw [hmem]; simp)
    simp [z1, z2, z3]
  refine ⟨fun i j => f (Sum.inl i) (Sum.inr j), fun i => ?_, fun j => ?_, fun i j => ?_⟩
  · have := hb' (Sum.inl i); rw [hrow] at this; simp only [lo, hi, Sum.elim_inl] at this
    constructor <;> linarith [this.1, this.2]
  · have := hb' (Sum.inr j); rw [hcol] at this; simpa [lo, hi] using this
  · have := hK.2 (Sum.inl i, Sum.inr j) ((hmem _ _).2 ⟨i, j, rfl, rfl⟩)
    simpa [G, fo] using this

