-- Prove2me | solution 1 for FlowsNetworks.Graphs.menger_node_disjoint_chains
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:58:11.341349+00:00
-- url     : https://prove2.me/submissions/cda1dcff-963a-428e-ab62-102d3144c37d

import Mathlib
import Definitions.Def_FlowsNetworks_Graphs_Chains
open FlowsNetworks.Graphs

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

section g70fn1M
variable {N : Type} [Fintype N] [DecidableEq N]
set_option linter.unusedSectionVars false

theorem g70fn1_path_props {R : N → N → Prop} {v0 x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn1_Step R) (v0, [v0]) (x, l)) :
    l.Nodup ∧ l.head? = some x ∧ l.getLast? = some v0 ∧ l.IsChain (fun a b => R b a) ∧
      (∀ z ∈ l, z = x ∨ ∃ z' ∈ l, R z z') ∧ (∀ z ∈ l, z = v0 ∨ ∃ z' ∈ l, R z' z) := by
  generalize hb : (x, l) = b at h
  induction h generalizing x l with
  | refl =>
    cases hb
    refine ⟨by simp, rfl, rfl, by simp, ?_, ?_⟩ <;> intro z hz <;> simp at hz <;> simp [hz]
  | tail h1 hst ih =>
    rename_i b c
    obtain ⟨y, l0⟩ := b
    obtain ⟨hR, hx, h3⟩ := hst
    cases hb
    simp only at h3 hR hx
    subst h3
    obtain ⟨n0, hh, hl, hc, hs, hp⟩ := ih rfl
    obtain ⟨rest, rfl⟩ : ∃ rest, l0 = y :: rest := by
      cases l0 with
      | nil => simp at hh
      | cons a r => simp at hh; exact ⟨r, by rw [hh]⟩
    refine ⟨List.nodup_cons.2 ⟨hx, n0⟩, rfl, ?_, ?_, ?_, ?_⟩
    · rw [List.getLast?_cons_cons]; exact hl
    · rw [List.isChain_cons_cons]; exact ⟨hR, hc⟩
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · left; rfl
      · rcases hs z hz with rfl | ⟨z', hz', hr⟩
        · right; exact ⟨_, List.mem_cons_self, hR⟩
        · right; exact ⟨z', List.mem_cons_of_mem _ hz', hr⟩
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · right; exact ⟨y, List.mem_cons_of_mem _ List.mem_cons_self, hR⟩
      · rcases hp z hz with h | ⟨z', hz', hr⟩
        · left; exact h
        · right; exact ⟨z', List.mem_cons_of_mem _ hz', hr⟩

theorem g70fn1_fiber_in (H : Finset (N × N)) (Y : Finset N) :
    ∑ v ∈ Y, (H.filter (fun p => p.2 = v)).card = (H.filter (fun p => p.2 ∈ Y)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Y)]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro p _
    constructor
    · rintro rfl; exact ⟨hv, rfl⟩
    · rintro ⟨_, h⟩; exact h
  · intro p hp; exact (Finset.mem_filter.1 hp).2

theorem g70fn1_fiber_out (H : Finset (N × N)) (Y : Finset N) :
    ∑ v ∈ Y, (H.filter (fun p => p.1 = v)).card = (H.filter (fun p => p.1 ∈ Y)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Y)]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro p _
    constructor
    · rintro rfl; exact ⟨hv, rfl⟩
    · rintro ⟨_, h⟩; exact h
  · intro p hp; exact (Finset.mem_filter.1 hp).2

theorem g70fn1_two_le_card {s : Finset (N × N)} {a b : N × N} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) : 2 ≤ s.card := by
  have : ({a, b} : Finset (N × N)) ⊆ s := by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  have := Finset.card_le_card this
  rw [Finset.card_pair hab] at this; exact this

end g70fn1M

section g70fn1M2
variable {N : Type} [Fintype N] [DecidableEq N]
set_option linter.unusedSectionVars false

theorem g70fn1_decomp (G : FlowsNetworks.Graphs.Digraph N) (S T : Finset N) (hST : Disjoint S T) :
    ∀ (k : ℕ) (H : Finset (N × N)) (S0 T0 : Finset N), H ⊆ G.arcs → S0 ⊆ S → T0 ⊆ T →
      (∀ v, (H.filter (fun p => p.2 = v)).card + (if v ∈ S0 then 1 else 0) =
        (H.filter (fun p => p.1 = v)).card + (if v ∈ T0 then 1 else 0)) →
      (∀ v, (H.filter (fun p => p.2 = v)).card + (if v ∈ S0 then 1 else 0) ≤ 1) →
      S0.card = k →
      ∃ C : Fin k → List N, (∀ i, G.IsChainFromTo S T (C i)) ∧
        (∀ i j, i ≠ j → ∀ v ∈ C i, v ∉ C j) ∧ (∀ i, ∀ v ∈ C i, ∃ p ∈ H, p.1 = v ∨ p.2 = v) := by
  classical
  intro k
  induction k with
  | zero =>
    intro H S0 T0 _ _ _ _ _ _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro H S0 T0 hHG hS0 hT0 hbal hle hcard
    obtain ⟨v0, hv0⟩ : S0.Nonempty := Finset.card_pos.1 (by omega)
    let R : N → N → Prop := fun x y => (x, y) ∈ H
    set Y := Finset.univ.filter (fun y => Relation.ReflTransGen R v0 y) with hY
    have hreach : ∃ y ∈ Y, y ∈ T0 := by
      by_contra hno
      push_neg at hno
      have e := Finset.sum_congr rfl (fun v (_ : v ∈ Y) => hbal v)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, g70fn1_fiber_in, g70fn1_fiber_out] at e
      have z1 : ∑ v ∈ Y, (if v ∈ T0 then 1 else 0) = 0 :=
        Finset.sum_eq_zero fun v hv => by simp [hno v hv]
      have hv0Y : v0 ∈ Y := by
        simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and]; exact Relation.ReflTransGen.refl
      have z2 : 1 ≤ ∑ v ∈ Y, (if v ∈ S0 then 1 else 0) := by
        have := Finset.single_le_sum (f := fun v => if v ∈ S0 then 1 else 0)
          (fun _ _ => Nat.zero_le _) hv0Y
        simpa [hv0] using this
      have z3 : (H.filter (fun p => p.1 ∈ Y)).card ≤ (H.filter (fun p => p.2 ∈ Y)).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, hY, Finset.mem_univ, true_and] at hp ⊢
        exact ⟨hp.1, hp.2.tail hp.1⟩
      omega
    obtain ⟨y, hyY, hyT0⟩ := hreach
    have hy : Relation.ReflTransGen R v0 y := by simpa [hY] using hyY
    obtain ⟨l, hl⟩ := g70fn1_simple hy
    obtain ⟨lnd, lhead, llast, lchain, lsucc, lpred⟩ := g70fn1_path_props hl
    have hv0y : v0 ≠ y := by
      intro h; subst h
      exact Finset.disjoint_left.1 hST (hS0 hv0) (hT0 hyT0)
    have hyl : y ∈ l := List.mem_of_mem_head? lhead
    have hv0l : v0 ∈ l := List.mem_of_mem_getLast? llast
    set P := l.toFinset with hP
    -- degree facts
    have outpos : ∀ x, ∀ w, (x, w) ∈ H → 1 ≤ (H.filter (fun p => p.1 = x)).card := fun x w h =>
      Finset.card_pos.2 ⟨(x, w), Finset.mem_filter.2 ⟨h, rfl⟩⟩
    have inpos : ∀ x, ∀ w, (w, x) ∈ H → 1 ≤ (H.filter (fun p => p.2 = x)).card := fun x w h =>
      Finset.card_pos.2 ⟨(w, x), Finset.mem_filter.2 ⟨h, rfl⟩⟩
    have noOut : ∀ x ∈ P, ∀ w, w ∉ P → (x, w) ∉ H := by
      intro x hx w hw hxw
      rw [hP, List.mem_toFinset] at hx
      have hb := hbal x; have hl1 := hle x
      rcases lsucc x hx with rfl | ⟨x', hx', hr⟩
      · have := outpos x w hxw; rw [if_pos hyT0] at hb; split_ifs at hb hl1 <;> omega
      · have hne : (x, x') ≠ (x, w) := by
          intro h; apply hw; simp only [Prod.mk.injEq] at h; rw [← h.2, hP, List.mem_toFinset]
          exact hx'
        have := g70fn1_two_le_card (Finset.mem_filter.2 ⟨hr, rfl⟩ : (x, x') ∈ H.filter (fun p => p.1 = x))
          (Finset.mem_filter.2 ⟨hxw, rfl⟩ : (x, w) ∈ H.filter (fun p => p.1 = x)) hne
        split_ifs at hb hl1 <;> omega
    have noIn : ∀ x ∈ P, ∀ w, w ∉ P → (w, x) ∉ H := by
      intro x hx w hw hwx
      rw [hP, List.mem_toFinset] at hx
      have hl1 := hle x
      rcases lpred x hx with rfl | ⟨x', hx', hr⟩
      · have := inpos x w hwx; rw [if_pos hv0] at hl1; omega
      · have hne : (x', x) ≠ (w, x) := by
          intro h; apply hw; simp only [Prod.mk.injEq] at h; rw [← h.1, hP, List.mem_toFinset]
          exact hx'
        have := g70fn1_two_le_card (Finset.mem_filter.2 ⟨hr, rfl⟩ : (x', x) ∈ H.filter (fun p => p.2 = x))
          (Finset.mem_filter.2 ⟨hwx, rfl⟩ : (w, x) ∈ H.filter (fun p => p.2 = x)) hne
        split_ifs at hl1 <;> omega
    have hSP : S0 ∩ P = {v0} := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hzP⟩
        rw [hP, List.mem_toFinset] at hzP
        rcases lpred z hzP with h | ⟨x', _, hr⟩
        · exact h
        · have := inpos z x' hr; have h2 := hle z; rw [if_pos hz] at h2; omega
      · rintro rfl; exact ⟨hv0, by rw [hP, List.mem_toFinset]; exact hv0l⟩
    set H' := H.filter (fun p => p.1 ∉ P ∧ p.2 ∉ P) with hH'
    have degin : ∀ v, v ∉ P → H'.filter (fun p => p.2 = v) = H.filter (fun p => p.2 = v) := by
      intro v hv; ext p
      simp only [hH', Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, rfl⟩
        refine ⟨⟨h1, fun hp1 => noOut p.1 hp1 p.2 hv h1, hv⟩, rfl⟩
    have degout : ∀ v, v ∉ P → H'.filter (fun p => p.1 = v) = H.filter (fun p => p.1 = v) := by
      intro v hv; ext p
      simp only [hH', Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, rfl⟩
        refine ⟨⟨h1, hv, fun hp2 => noIn p.2 hp2 p.1 hv h1⟩, rfl⟩
    have degP : ∀ v, v ∈ P → H'.filter (fun p => p.2 = v) = ∅ ∧ H'.filter (fun p => p.1 = v) = ∅ := by
      intro v hv
      constructor <;> (apply Finset.filter_eq_empty_iff.2; intro p hp; simp only [hH', Finset.mem_filter] at hp
                       rintro rfl; tauto)
    obtain ⟨C', hC'1, hC'2, hC'3⟩ := ih H' (S0 \ P) (T0 \ P)
      ((Finset.filter_subset _ _).trans hHG) (Finset.sdiff_subset.trans hS0)
      (Finset.sdiff_subset.trans hT0)
      (by
        intro v
        by_cases hv : v ∈ P
        · obtain ⟨e1, e2⟩ := degP v hv; simp [e1, e2, hv]
        · rw [degin v hv, degout v hv]; simpa [hv] using hbal v)
      (by
        intro v
        by_cases hv : v ∈ P
        · obtain ⟨e1, _⟩ := degP v hv; simp [e1, hv]
        · rw [degin v hv]; simpa [hv] using hle v)
      (by
        have := Finset.card_sdiff_add_card_inter S0 P
        rw [hSP, Finset.card_singleton] at this; omega)
    -- new chain
    have hlen : 2 ≤ l.length := by
      have h1 : ({v0, y} : Finset N) ⊆ l.toFinset := by
        intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp [hv0l, hyl]
      have := Finset.card_le_card h1
      rw [Finset.card_pair hv0y] at this
      exact this.trans (List.toFinset_card_le l)
    have hc : G.IsChainFromTo S T l.reverse := by
      refine ⟨⟨by simpa using hlen, List.nodup_reverse.2 lnd, ?_⟩, ?_, ?_⟩
      · have hrc : l.reverse.IsChain R := List.isChain_reverse.2 lchain
        rw [List.isChain_iff_getElem] at hrc
        intro i hi
        exact hHG (hrc i hi)
      · rw [List.head?_reverse, llast]; exact ⟨v0, rfl, hS0 hv0⟩
      · rw [List.getLast?_reverse, lhead]; exact ⟨y, rfl, hT0 hyT0⟩
    have hcH : ∀ v ∈ l.reverse, ∃ p ∈ H, p.1 = v ∨ p.2 = v := by
      intro v hv
      rw [List.mem_reverse] at hv
      rcases lsucc v hv with rfl | ⟨z', _, hr⟩
      · rcases lpred v hv with h | ⟨z', _, hr⟩
        · exact absurd h.symm hv0y
        · exact ⟨_, hr, Or.inr rfl⟩
      · exact ⟨_, hr, Or.inl rfl⟩
    have hCP : ∀ i, ∀ v ∈ C' i, v ∉ P := by
      intro i v hv hvP
      obtain ⟨p, hp, hpv⟩ := hC'3 i v hv
      simp only [hH', Finset.mem_filter] at hp
      rcases hpv with rfl | rfl
      · exact hp.2.1 hvP
      · exact hp.2.2 hvP
    refine ⟨Fin.cons l.reverse C', ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hc
      · simpa using hC'1 j
    · intro i j hij v hvi hvj
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact hij rfl
      · simp only [Fin.cons_zero, Fin.cons_succ] at hvi hvj
        exact hCP j' v hvj (by rw [hP, List.mem_toFinset]; exact List.mem_reverse.1 hvi)
      · simp only [Fin.cons_zero, Fin.cons_succ] at hvi hvj
        exact hCP i' v hvi (by rw [hP, List.mem_toFinset]; exact List.mem_reverse.1 hvj)
      · simp only [Fin.cons_succ] at hvi hvj
        exact hC'2 i' j' (fun h => hij (by rw [h])) v hvi hvj
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hcH
      · intro v hv
        simp only [Fin.cons_succ] at hv
        obtain ⟨p, hp, h⟩ := hC'3 j v hv
        exact ⟨p, (Finset.mem_filter.1 hp).1, h⟩

end g70fn1M2

section g70fn1M3
variable {N : Type} [Fintype N] [DecidableEq N]
set_option linter.unusedSectionVars false

def g70fn1_arcP (G : FlowsNetworks.Graphs.Digraph N) (S T : Finset N) :
    (N × Bool) ⊕ Bool → (N × Bool) ⊕ Bool → Prop
  | Sum.inl (v, false), Sum.inl (w, true) => v = w
  | Sum.inl (x, true), Sum.inl (y, false) => (x, y) ∈ G.arcs
  | Sum.inr false, Sum.inl (v, false) => v ∈ S
  | Sum.inl (v, true), Sum.inr true => v ∈ T
  | _, _ => False

theorem g70fn1_weak (G : FlowsNetworks.Graphs.Digraph N) (S T : Finset N) (m : ℕ)
    (C : Fin m → List N) (hC : ∀ i, G.IsChainFromTo S T (C i))
    (hdis : ∀ i j, i ≠ j → ∀ v ∈ C i, v ∉ C j) (D : Finset N) (hD : G.IsDisconnecting S T D) :
    m ≤ D.card := by
  classical
  have hx : ∀ i, ∃ v ∈ C i, v ∈ D := fun i => hD (C i) (hC i)
  choose v hvC hvD using hx
  have hinj : Function.Injective (fun i => (⟨v i, hvD i⟩ : D)) := by
    intro i j h
    simp only [Subtype.mk.injEq] at h
    by_contra hij
    exact hdis i j hij (v i) (hvC i) (h ▸ hvC j)
  have := Fintype.card_le_of_injective _ hinj
  simpa using this

theorem g70fn1_deg_in' (H : Finset (N × N)) (y : N) :
    ((H.filter (fun p => p.2 = y)).card : ℝ) = ∑ x, (if (x, y) ∈ H then (1:ℝ) else 0) := by
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [← Finset.sum_filter]
  exact Finset.sum_nbij' Prod.fst (fun x => (x, y))
    (by intro p hp; obtain ⟨p1, p2⟩ := p; aesop) (by intro y hy; aesop)
    (by intro p hp; obtain ⟨p1, p2⟩ := p; aesop) (by intro y _; rfl) (by intro _ _; rfl)

theorem g70fn1_deg_out' (H : Finset (N × N)) (x : N) :
    ((H.filter (fun p => p.1 = x)).card : ℝ) = ∑ y, (if (x, y) ∈ H then (1:ℝ) else 0) := by
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [← Finset.sum_filter]
  exact Finset.sum_nbij' Prod.snd (fun y => (x, y))
    (by intro p hp; obtain ⟨p1, p2⟩ := p; aesop) (by intro y hy; aesop)
    (by intro p hp; obtain ⟨p1, p2⟩ := p; aesop) (by intro y _; rfl) (by intro _ _; rfl)

end g70fn1M3

section g70fn1M4
variable {N : Type} [Fintype N] [DecidableEq N]
set_option linter.unusedSectionVars false

theorem g70fn1_menger_core (G : FlowsNetworks.Graphs.Digraph N) (S T : Finset N)
    (hST : Disjoint S T) :
    ∃ k : ℕ, (∃ C : Fin k → List N, (∀ i, G.IsChainFromTo S T (C i)) ∧
        ∀ i j, i ≠ j → ∀ v ∈ C i, v ∉ C j) ∧
      ∃ D : Finset N, G.IsDisconnecting S T D ∧ D.card ≤ k := by
  classical
  set A := g70fn1_arcP G S T with hA
  let Gn : g70fn1_Net ((N × Bool) ⊕ Bool) :=
    ⟨Finset.univ.filter (fun p => A p.1 p.2), fun _ _ => 0, fun _ _ => 1⟩
  have hmem : ∀ u w, (u, w) ∈ Gn.arcs ↔ A u w := by intro u w; simp [Gn]
  let lo : ℕ → (N × Bool) ⊕ Bool → ℝ := fun k => Sum.elim (fun _ => 0) (fun b => if b then (k:ℝ) else -(k:ℝ))
  have hsumlo : ∀ k (Z : Finset ((N × Bool) ⊕ Bool)), ∑ z ∈ Z, lo k z =
      (if Sum.inr true ∈ Z then (k:ℝ) else 0) - (if Sum.inr false ∈ Z then (k:ℝ) else 0) := by
    intro k Z
    have : ∑ z ∈ Z, lo k z = ∑ z, if z ∈ Z then lo k z else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [this, Fintype.sum_sum_type]
    by_cases h1 : (Sum.inr true : (N × Bool) ⊕ Bool) ∈ Z <;>
      by_cases h2 : (Sum.inr false : (N × Bool) ⊕ Bool) ∈ Z <;> simp [h1, h2, lo, Fintype.sum_bool]
  have hfs1 : ∀ Z W, g70fn1_fsum Gn Gn.cap Z W =
      ((Gn.arcs.filter (fun p => p.1 ∈ Z ∧ p.2 ∈ W)).card : ℝ) := by
    intro Z W; unfold g70fn1_fsum; simp [Gn]
  have hfs0 : ∀ Z W, g70fn1_fsum Gn Gn.low Z W = 0 := by
    intro Z W; unfold g70fn1_fsum; simp [Gn]
  let Pk : ℕ → Prop := fun k => ∀ Z, -(∑ z ∈ Z, lo k z) ≤ g70fn1_fsum Gn Gn.cap Z Zᶜ
  have hex : ∃ k, ¬ Pk (k + 1) := by
    refine ⟨Fintype.card N, fun h => ?_⟩
    have h1 := h {Sum.inr false}
    rw [hsumlo, hfs1] at h1
    rw [if_neg (by simp), if_pos (Finset.mem_singleton_self _)] at h1
    have : (Gn.arcs.filter (fun p => p.1 ∈ ({Sum.inr false} : Finset _) ∧
        p.2 ∈ ({Sum.inr false} : Finset ((N × Bool) ⊕ Bool))ᶜ)) ⊆
        (Finset.univ : Finset N).image (fun v => (Sum.inr false, Sum.inl (v, false))) := by
      intro p hp
      obtain ⟨a, b⟩ := p
      simp only [Finset.mem_filter, hmem, Finset.mem_singleton, Finset.mem_compl] at hp
      obtain ⟨h1, rfl, -⟩ := hp
      rcases b with ⟨v, _ | _⟩ | _ | _ <;> simp [hA, g70fn1_arcP] at h1 ⊢
    have h2 := (Finset.card_le_card this).trans Finset.card_image_le
    rw [Finset.card_univ] at h2
    have : ((Gn.arcs.filter (fun p => p.1 ∈ ({Sum.inr false} : Finset _) ∧
        p.2 ∈ ({Sum.inr false} : Finset ((N × Bool) ⊕ Bool))ᶜ)).card : ℝ) ≤ Fintype.card N := by
      exact_mod_cast h2
    push_cast at h1
    linarith
  set k := Nat.find hex with hkdef
  have hk1 : ¬ Pk (k + 1) := Nat.find_spec hex
  have hk : Pk k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · intro Z
      rw [hsumlo, h0, hfs1]
      simp only [Nat.cast_zero, ite_self, sub_zero, neg_zero]
      positivity
    · have := Nat.find_min hex (show k - 1 < k by omega)
      push_neg at this
      have e : k - 1 + 1 = k := by omega
      rw [e] at this; exact this
  -- the flow
  obtain ⟨f, hK, hfi, hbd⟩ := g70fn1_main_int Gn (fun p _ => by simp [Gn]) (lo k) (lo k)
    (fun _ => le_rfl)
    (fun Z => by rw [hfs0]; have := hk Z; linarith)
    (fun Z => by
      rw [hfs0]
      have h1 := Finset.sum_add_sum_compl Z (lo k)
      have h2 := hsumlo k Finset.univ
      simp only [Finset.mem_univ, if_true, sub_self] at h2
      have := hk Z; linarith)
    (fun p _ => ⟨⟨0, by simp [Gn]⟩, ⟨1, by simp [Gn]⟩⟩)
    (fun z => by
      have : g70fn1_IsInt (lo k z) := by
        rcases z with _ | (_ | _)
        · exact ⟨0, by simp [lo]⟩
        · exact ⟨-(k:ℤ), by simp [lo]⟩
        · exact ⟨k, by simp [lo]⟩
      exact ⟨this, this⟩)
  have hz : ∀ u w, ¬ A u w → f u w = 0 := fun u w h => hK.1 u w (by rw [hmem]; exact h)
  have h01 : ∀ u w, f u w = 0 ∨ f u w = 1 := by
    intro u w
    by_cases h : (u, w) ∈ Gn.arcs
    · obtain ⟨m, hm⟩ := hfi _ h
      have hb2 := hK.2 _ h
      simp only [Gn] at hm hb2
      rw [hm] at hb2 ⊢
      have : (0:ℤ) ≤ m := by exact_mod_cast hb2.1
      have : m ≤ 1 := by exact_mod_cast hb2.2
      have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;> simp
    · left; exact hK.1 u w h
  have zinin : ∀ v w, f (Sum.inl (v, false)) (Sum.inl (w, false)) = 0 :=
    fun v w => hz _ _ (by simp [hA, g70fn1_arcP])
  have zoutout : ∀ v w, f (Sum.inl (v, true)) (Sum.inl (w, true)) = 0 :=
    fun v w => hz _ _ (by simp [hA, g70fn1_arcP])
  have zanys : ∀ u, f u (Sum.inr false) = 0 := by
    intro u; apply hz; rcases u with ⟨v, _ | _⟩ | (_ | _) <;> simp [hA, g70fn1_arcP]
  have ztany : ∀ u, f (Sum.inr true) u = 0 := by
    intro u; apply hz; rcases u with ⟨v, _ | _⟩ | (_ | _) <;> simp [hA, g70fn1_arcP]
  have zint : ∀ v, f (Sum.inl (v, false)) (Sum.inr true) = 0 :=
    fun v => hz _ _ (by simp [hA, g70fn1_arcP])
  have zsout : ∀ v, f (Sum.inr false) (Sum.inl (v, true)) = 0 :=
    fun v => hz _ _ (by simp [hA, g70fn1_arcP])
  have zst : f (Sum.inr false) (Sum.inr true) = 0 := hz _ _ (by simp [hA, g70fn1_arcP])
  have hsumM : ∀ g : (N × Bool) ⊕ Bool → ℝ, ∑ u, g u =
      ∑ w, (g (Sum.inl (w, true)) + g (Sum.inl (w, false))) + (g (Sum.inr true) + g (Sum.inr false)) := by
    intro g; rw [Fintype.sum_sum_type, Fintype.sum_prod_type]; simp [Fintype.sum_bool]
  have hs := hK.1
  have nfoE : ∀ z, g70fn1_nfo Gn f z = - lo k z := by
    intro z; have := hbd z; linarith [this.1, this.2]
  have nin : ∀ v, f (Sum.inr false) (Sum.inl (v, false)) +
      ∑ w, f (Sum.inl (w, true)) (Sum.inl (v, false)) = f (Sum.inl (v, false)) (Sum.inl (v, true)) := by
    intro v
    have e := nfoE (Sum.inl (v, false))
    rw [g70fn1_nfo_full Gn f hs, hsumM, hsumM] at e
    simp only [zinin, zanys, ztany, zint, add_zero, Finset.sum_const_zero, lo, Sum.elim_inl,
      neg_zero] at e
    rw [Finset.sum_eq_single v (fun w _ hw => hz _ _ (by simp [hA, g70fn1_arcP]; exact fun h => hw h.symm))
      (by simp)] at e
    linarith
  have nout : ∀ v, ∑ w, f (Sum.inl (v, true)) (Sum.inl (w, false)) +
      f (Sum.inl (v, true)) (Sum.inr true) = f (Sum.inl (v, false)) (Sum.inl (v, true)) := by
    intro v
    have e := nfoE (Sum.inl (v, true))
    rw [g70fn1_nfo_full Gn f hs, hsumM, hsumM] at e
    simp only [zoutout, zanys, ztany, zsout, add_zero, zero_add, Finset.sum_const_zero, lo,
      Sum.elim_inl, neg_zero] at e
    rw [Finset.sum_eq_single (f := fun x => f (Sum.inl (x, false)) (Sum.inl (v, true))) v
      (fun w _ hw => hz _ _ (by simp [hA, g70fn1_arcP]; exact hw)) (by simp)] at e
    linarith
  have ns : ∑ w, f (Sum.inr false) (Sum.inl (w, false)) = k := by
    have e := nfoE (Sum.inr false)
    rw [g70fn1_nfo_full Gn f hs, hsumM, hsumM] at e
    simp only [zsout, zanys, zst, add_zero, zero_add, Finset.sum_const_zero, lo, Sum.elim_inr,
      Bool.false_eq_true, if_false, neg_neg] at e
    have z2 : ∀ w, f (Sum.inl (w, true)) (Sum.inr false) = 0 := fun w => zanys _
    have z3 : ∀ w, f (Sum.inl (w, false)) (Sum.inr false) = 0 := fun w => zanys _
    simp only [z2, z3, add_zero, Finset.sum_const_zero, sub_zero] at e
    linarith
  -- combinatorial data
  set H := G.arcs.filter (fun p => f (Sum.inl (p.1, true)) (Sum.inl (p.2, false)) = 1) with hH
  set S0 := S.filter (fun v => f (Sum.inr false) (Sum.inl (v, false)) = 1) with hS0
  set T0 := T.filter (fun v => f (Sum.inl (v, true)) (Sum.inr true) = 1) with hT0
  have iH : ∀ x y, f (Sum.inl (x, true)) (Sum.inl (y, false)) = if (x, y) ∈ H then 1 else 0 := by
    intro x y
    by_cases hxy : (x, y) ∈ G.arcs
    · rcases h01 (Sum.inl (x, true)) (Sum.inl (y, false)) with h | h <;> simp [hH, hxy, h]
    · rw [hz _ _ (by simp [hA, g70fn1_arcP]; exact hxy)]; simp [hH, hxy]
  have iS : ∀ v, f (Sum.inr false) (Sum.inl (v, false)) = if v ∈ S0 then 1 else 0 := by
    intro v
    by_cases hv : v ∈ S
    · rcases h01 (Sum.inr false) (Sum.inl (v, false)) with h | h <;> simp [hS0, hv, h]
    · rw [hz _ _ (by simp [hA, g70fn1_arcP]; exact hv)]; simp [hS0, hv]
  have iT : ∀ v, f (Sum.inl (v, true)) (Sum.inr true) = if v ∈ T0 then 1 else 0 := by
    intro v
    by_cases hv : v ∈ T
    · rcases h01 (Sum.inl (v, true)) (Sum.inr true) with h | h <;> simp [hT0, hv, h]
    · rw [hz _ _ (by simp [hA, g70fn1_arcP]; exact hv)]; simp [hT0, hv]
  have ele : ∀ v, f (Sum.inl (v, false)) (Sum.inl (v, true)) ≤ 1 := by
    intro v; rcases h01 (Sum.inl (v, false)) (Sum.inl (v, true)) with h | h <;> rw [h] <;> norm_num
  have hbal : ∀ v, (H.filter (fun p => p.2 = v)).card + (if v ∈ S0 then 1 else 0) =
      (H.filter (fun p => p.1 = v)).card + (if v ∈ T0 then 1 else 0) := by
    intro v
    have e1 := nin v; have e2 := nout v
    simp only [iH, iS, iT] at e1 e2
    rw [← g70fn1_deg_in'] at e1; rw [← g70fn1_deg_out'] at e2
    have : ((H.filter (fun p => p.2 = v)).card + (if v ∈ S0 then 1 else 0) : ℕ) =
        (((H.filter (fun p => p.1 = v)).card + (if v ∈ T0 then 1 else 0) : ℕ) : ℝ) := by
      push_cast [Nat.cast_ite]; linarith
    exact_mod_cast this
  have hle : ∀ v, (H.filter (fun p => p.2 = v)).card + (if v ∈ S0 then 1 else 0) ≤ 1 := by
    intro v
    have e1 := nin v
    simp only [iH, iS] at e1
    rw [← g70fn1_deg_in'] at e1
    have : (((H.filter (fun p => p.2 = v)).card + (if v ∈ S0 then 1 else 0) : ℕ) : ℝ) ≤ 1 := by
      push_cast [Nat.cast_ite]; linarith [ele v]
    exact_mod_cast this
  have hcard : S0.card = k := by
    have e := ns
    simp only [iS] at e
    rw [Finset.sum_boole] at e
    have : (Finset.univ.filter (fun w => w ∈ S0)) = S0 := by ext; simp
    rw [this] at e
    exact_mod_cast e
  obtain ⟨C, hC1, hC2, -⟩ := g70fn1_decomp G S T hST k H S0 T0 (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) hbal hle hcard
  refine ⟨k, ⟨C, hC1, hC2⟩, ?_⟩
  -- the cut
  simp only [Pk, not_forall, not_le] at hk1
  obtain ⟨Z, hZ⟩ := hk1
  rw [hsumlo, hfs1] at hZ
  set cut := Gn.arcs.filter (fun p => p.1 ∈ Z ∧ p.2 ∈ Zᶜ) with hcut
  have hc0 : (0:ℝ) ≤ (cut.card : ℝ) := Nat.cast_nonneg _
  have hsZ : (Sum.inr false : (N × Bool) ⊕ Bool) ∈ Z := by
    by_contra h; rw [if_neg h] at hZ
    split_ifs at hZ <;> push_cast at hZ <;> linarith
  have htZ : (Sum.inr true : (N × Bool) ⊕ Bool) ∉ Z := by
    intro h; rw [if_pos h, if_pos hsZ] at hZ; linarith
  rw [if_neg htZ, if_pos hsZ] at hZ
  have hcutk : cut.card ≤ k := by
    have : (cut.card : ℝ) < (k : ℝ) + 1 := by push_cast at hZ; linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  set D := Finset.univ.filter (fun v : N =>
    (Sum.inl (v, false) ∈ Z ∧ Sum.inl (v, true) ∉ Z) ∨ (v ∈ S ∧ Sum.inl (v, false) ∉ Z) ∨
    (v ∈ T ∧ Sum.inl (v, true) ∈ Z) ∨
    (Sum.inl (v, true) ∈ Z ∧ ∃ y, (v, y) ∈ G.arcs ∧ Sum.inl (y, false) ∉ Z)) with hD
  refine ⟨D, ?_, ?_⟩
  · intro l hl
    by_contra hno
    push_neg at hno
    obtain ⟨⟨hlen, -, harc⟩, ⟨x, hx, hxS⟩, ⟨y, hy, hyT⟩⟩ := hl
    have notD : ∀ (i : ℕ) (hi : i < l.length), l[i] ∉ D := fun i hi => hno _ (List.getElem_mem hi)
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_and, not_not,
      not_exists] at notD
    have key : ∀ (i : ℕ) (hi : i < l.length),
        Sum.inl (l[i], false) ∈ Z ∧ Sum.inl (l[i], true) ∈ Z := by
      intro i
      induction i with
      | zero =>
        intro hi
        have hx0 : l[0] = x := by
          cases l with
          | nil => simp at hi
          | cons a r => simp at hx; simp [hx]
        have h1 : Sum.inl (l[0], false) ∈ Z := by
          by_contra h; exact h ((notD 0 hi).2.1 (hx0 ▸ hxS))
        exact ⟨h1, (notD 0 hi).1 h1⟩
      | succ i ih =>
        intro hi
        have ⟨_, hout⟩ := ih (by omega)
        have ha := harc i hi
        have h1 : Sum.inl (l[i+1], false) ∈ Z := (notD i (by omega)).2.2.2 hout (l[i+1]) ha
        exact ⟨h1, (notD (i+1) hi).1 h1⟩
    have hylast : l[l.length - 1]'(by omega) = y := by
      rw [List.getLast?_eq_getElem?] at hy
      simp only [List.getElem?_eq_getElem (by omega : l.length - 1 < l.length), Option.mem_def,
        Option.some.injEq] at hy
      exact hy
    have := (notD (l.length - 1) (by omega)).2.2.1 (hylast ▸ hyT)
    exact this (key _ (by omega)).2
  · let φ : ((N × Bool) ⊕ Bool) × ((N × Bool) ⊕ Bool) → Option N := fun p =>
      Sum.elim (fun q => some q.1) (fun _ => Sum.elim (fun q => some q.1) (fun _ => none) p.2) p.1
    have hsub : D.map ⟨some, Option.some_injective _⟩ ⊆ cut.image φ := by
      intro o ho
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at ho
      obtain ⟨v, hv, rfl⟩ := ho
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [Finset.mem_image, hcut, Finset.mem_filter, hmem, Finset.mem_compl]
      rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, y, h2, h3⟩
      · exact ⟨(Sum.inl (v, false), Sum.inl (v, true)), ⟨by simp [hA, g70fn1_arcP], h1, h2⟩, rfl⟩
      · exact ⟨(Sum.inr false, Sum.inl (v, false)), ⟨by simp [hA, g70fn1_arcP, h1], hsZ, h2⟩, rfl⟩
      · exact ⟨(Sum.inl (v, true), Sum.inr true), ⟨by simp [hA, g70fn1_arcP, h1], h2, htZ⟩, rfl⟩
      · exact ⟨(Sum.inl (v, true), Sum.inl (y, false)), ⟨by simp [hA, g70fn1_arcP, h2], h1, h3⟩, rfl⟩
    have := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_map] at this
    omega

end g70fn1M4

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 4.2 (Menger, p. 34). Let `S` and `T`
be two disjoint subsets of the nodes of the graph `G = [N; 𝒜]`. The maximal number of pairwise
node disjoint chains from `S` to `T` is equal to the minimal number of nodes in an `S, T`
disconnecting set of nodes. Both extremes are stated as attained, with a common value `k`. -/
theorem solution {N : Type} [Fintype N] [DecidableEq N] (G : FlowsNetworks.Graphs.Digraph N)
    (S T : Finset N) (hST : Disjoint S T) :
    ∃ k : ℕ,
      IsGreatest {m : ℕ | ∃ C : Fin m → List N, (∀ i, G.IsChainFromTo S T (C i)) ∧
          ∀ i j, i ≠ j → ∀ v ∈ C i, v ∉ C j} k ∧
      IsLeast {m : ℕ | ∃ D : Finset N, G.IsDisconnecting S T D ∧ D.card = m} k := by
  obtain ⟨k, ⟨C, hC1, hC2⟩, D, hD, hDk⟩ := g70fn1_menger_core G S T hST
  have hkD := g70fn1_weak G S T k C hC1 hC2 D hD
  refine ⟨k, ⟨⟨C, hC1, hC2⟩, ?_⟩, ⟨⟨D, hD, by omega⟩, ?_⟩⟩
  · rintro m ⟨C', h1, h2⟩
    have := g70fn1_weak G S T m C' h1 h2 D hD
    omega
  · rintro m ⟨D', h1, rfl⟩
    exact g70fn1_weak G S T k C hC1 hC2 D' h1

