-- Prove2me | solution 1 for FlowsNetworks.Feasibility.two_sided_iff_one_sided
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:13:40.423274+00:00
-- url     : https://prove2.me/submissions/f327f4fd-c827-4990-92ac-17f2a773df38

import Mathlib
import Definitions.Def_FlowsNetworks_Feasibility_Network
open FlowsNetworks.Feasibility

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

section g70fn1F
open FlowsNetworks.Feasibility
variable {N : Type} [Fintype N] [DecidableEq N]
set_option linter.unusedSectionVars false

theorem g70fn1_out_eq (G : Network N) (f : N → N → ℝ) (x : N) :
    outflow G f x = ∑ p ∈ G.arcs.filter (fun p => p.1 = x), f p.1 p.2 := by
  unfold outflow arcSum; congr 1; apply Finset.filter_congr; intro p _; simp

theorem g70fn1_in_eq (G : Network N) (f : N → N → ℝ) (x : N) :
    inflow G f x = ∑ p ∈ G.arcs.filter (fun p => p.2 = x), f p.1 p.2 := by
  unfold inflow arcSum; congr 1; apply Finset.filter_congr; intro p _; simp

theorem g70fn1_net_eq (G : Network N) (ℓ : N → N → ℝ) (f : N → N → ℝ) (x : N) :
    inflow G f x - outflow G f x = - g70fn1_nfo ⟨G.arcs, ℓ, G.cap⟩ f x := by
  rw [g70fn1_out_eq, g70fn1_in_eq]; unfold g70fn1_nfo; ring

theorem g70fn1_sumnet (G : Network N) (f : N → N → ℝ) (X : Finset N) :
    ∑ x ∈ X, (inflow G f x - outflow G f x) = arcSum G f Xᶜ X - arcSum G f X Xᶜ := by
  simp_rw [g70fn1_net_eq G (fun _ _ => 0) f]
  rw [Finset.sum_neg_distrib, g70fn1_sum_nfo]
  unfold g70fn1_fsum arcSum; ring

theorem g70fn1_arcSum_le (G : Network N) (f g : N → N → ℝ) (h : ∀ p ∈ G.arcs, f p.1 p.2 ≤ g p.1 p.2)
    (X Y : Finset N) : arcSum G f X Y ≤ arcSum G g X Y :=
  Finset.sum_le_sum fun p hp => h p (Finset.mem_filter.1 hp).1

theorem g70fn1_arcSum_nonneg (G : Network N) (X Y : Finset N) : 0 ≤ arcSum G G.cap X Y :=
  Finset.sum_nonneg fun p hp => G.cap_nonneg p (Finset.mem_filter.1 hp).1

theorem g70fn1_arcSum_zero (G : Network N) (X Y : Finset N) : arcSum G (fun _ _ => 0) X Y = 0 := by
  unfold arcSum; simp

/-- necessity: net inflow into a set is bounded by the capacity of arcs entering it -/
theorem g70fn1_nec (G : Network N) (ℓ f : N → N → ℝ)
    (hf : ∀ p ∈ G.arcs, ℓ p.1 p.2 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2) (X : Finset N) :
    ∑ x ∈ Xᶜ, (inflow G f x - outflow G f x) ≤ arcSum G G.cap X Xᶜ - arcSum G ℓ Xᶜ X ∧
    ∑ x ∈ X, (outflow G f x - inflow G f x) ≤ arcSum G G.cap X Xᶜ - arcSum G ℓ Xᶜ X := by
  have e1 := g70fn1_sumnet G f Xᶜ
  have e2 := g70fn1_sumnet G f X
  rw [compl_compl] at e1
  have h1 := g70fn1_arcSum_le G f G.cap (fun p hp => (hf p hp).2) X Xᶜ
  have h2 := g70fn1_arcSum_le G ℓ f (fun p hp => (hf p hp).1) Xᶜ X
  have e3 : ∑ x ∈ X, (outflow G f x - inflow G f x) = - ∑ x ∈ X, (inflow G f x - outflow G f x) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext; ring
  rw [e3]
  constructor <;> linarith

theorem g70fn1_hoffman (G : Network N) (ℓ : N → N → ℝ) (lo hi : N → ℝ) (hlh : ∀ z, lo z ≤ hi z)
    (hℓ : ∀ p ∈ G.arcs, ℓ p.1 p.2 ≤ G.cap p.1 p.2)
    (C1 : ∀ X : Finset N, arcSum G ℓ Xᶜ X - ∑ x ∈ X, hi x ≤ arcSum G G.cap X Xᶜ)
    (C2 : ∀ X : Finset N, arcSum G ℓ Xᶜ X + ∑ x ∈ Xᶜ, lo x ≤ arcSum G G.cap X Xᶜ) :
    ∃ f, SupportedOnArcs G f ∧
      (∀ x, lo x ≤ inflow G f x - outflow G f x ∧ inflow G f x - outflow G f x ≤ hi x) ∧
      ∀ p ∈ G.arcs, ℓ p.1 p.2 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2 := by
  obtain ⟨f, hK, hb⟩ := g70fn1_main ⟨G.arcs, ℓ, G.cap⟩ hℓ lo hi hlh C1 C2
  refine ⟨f, hK.1, fun x => ?_, hK.2⟩
  rw [g70fn1_net_eq G ℓ]; exact hb x

theorem g70fn1_part_sum (S R T : Finset N) (hpart : IsPartition S R T) (g : N → ℝ) (X : Finset N) :
    ∑ x ∈ X, g x = ∑ x ∈ S ∩ X, g x + ∑ x ∈ R ∩ X, g x + ∑ x ∈ T ∩ X, g x := by
  obtain ⟨h1, h2, h3, h4⟩ := hpart
  rw [← Finset.sum_union, ← Finset.sum_union]
  · congr 1
    ext x
    have : x ∈ S ∪ R ∪ T := by rw [h4]; exact Finset.mem_univ x
    simp only [Finset.mem_union, Finset.mem_inter] at this ⊢
    tauto
  · rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left h2),
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left h3)⟩
  · exact Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left h1)

theorem g70fn1_two_sided (G : Network N) (S R T : Finset N) (hpart : IsPartition S R T)
    (a a' b b' : N → ℝ)
    (ha : ∀ x ∈ S, 0 ≤ a x ∧ a x ≤ a' x) (hb : ∀ x ∈ T, 0 ≤ b x ∧ b x ≤ b' x) :
    (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
        (∀ x ∈ S, a x ≤ outflow G f x - inflow G f x ∧ outflow G f x - inflow G f x ≤ a' x) ∧
        (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
        (∀ x ∈ T, b x ≤ inflow G f x - outflow G f x ∧ inflow G f x - outflow G f x ≤ b' x) ∧
        (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ↔
      ∀ X : Finset N,
        arcSum G G.cap X Xᶜ ≥ (∑ x ∈ T ∩ Xᶜ, b x) - (∑ x ∈ S ∩ Xᶜ, a' x) ∧
        arcSum G G.cap X Xᶜ ≥ (∑ x ∈ S ∩ X, a x) - (∑ x ∈ T ∩ X, b' x) := by
  have hST : ∀ x ∈ S, x ∉ T := fun x hx => Finset.disjoint_left.1 hpart.2.1 hx
  have hSR : ∀ x ∈ S, x ∉ R := fun x hx => Finset.disjoint_left.1 hpart.1 hx
  have hRT : ∀ x ∈ R, x ∉ T := fun x hx => Finset.disjoint_left.1 hpart.2.2.1 hx
  constructor
  · rintro ⟨f, hs, hS, hR, hT, hc⟩ X
    obtain ⟨n1, n2⟩ := g70fn1_nec G (fun _ _ => 0) f hc X
    rw [g70fn1_arcSum_zero, sub_zero] at n1 n2
    rw [g70fn1_part_sum S R T hpart] at n1 n2
    have s1 : ∑ x ∈ S ∩ Xᶜ, -a' x ≤ ∑ x ∈ S ∩ Xᶜ, (inflow G f x - outflow G f x) :=
      Finset.sum_le_sum fun x hx => by have := (hS x (Finset.mem_inter.1 hx).1).2; linarith
    have s2 : ∑ x ∈ R ∩ Xᶜ, (inflow G f x - outflow G f x) = 0 :=
      Finset.sum_eq_zero fun x hx => by have := hR x (Finset.mem_inter.1 hx).1; linarith
    have s3 : ∑ x ∈ T ∩ Xᶜ, b x ≤ ∑ x ∈ T ∩ Xᶜ, (inflow G f x - outflow G f x) :=
      Finset.sum_le_sum fun x hx => (hT x (Finset.mem_inter.1 hx).1).1
    have t1 : ∑ x ∈ S ∩ X, a x ≤ ∑ x ∈ S ∩ X, (outflow G f x - inflow G f x) :=
      Finset.sum_le_sum fun x hx => (hS x (Finset.mem_inter.1 hx).1).1
    have t2 : ∑ x ∈ R ∩ X, (outflow G f x - inflow G f x) = 0 :=
      Finset.sum_eq_zero fun x hx => hR x (Finset.mem_inter.1 hx).1
    have t3 : ∑ x ∈ T ∩ X, -b' x ≤ ∑ x ∈ T ∩ X, (outflow G f x - inflow G f x) :=
      Finset.sum_le_sum fun x hx => by have := (hT x (Finset.mem_inter.1 hx).1).2; linarith
    simp only [Finset.sum_neg_distrib] at s1 t3
    constructor <;> linarith
  · intro hX
    set lo : N → ℝ := fun x => if x ∈ S then -a' x else if x ∈ T then b x else 0 with hlo
    set hi : N → ℝ := fun x => if x ∈ S then -a x else if x ∈ T then b' x else 0 with hhi
    have loS : ∀ x ∈ S, lo x = -a' x := fun x hx => by simp [hlo, hx]
    have loR : ∀ x ∈ R, lo x = 0 := fun x hx => by
      have : x ∉ S := fun h => hSR x h hx
      simp [hlo, this, hRT x hx]
    have loT : ∀ x ∈ T, lo x = b x := fun x hx => by
      have : x ∉ S := fun h => hST x h hx
      simp [hlo, this, hx]
    have hiS : ∀ x ∈ S, hi x = -a x := fun x hx => by simp [hhi, hx]
    have hiR : ∀ x ∈ R, hi x = 0 := fun x hx => by
      have : x ∉ S := fun h => hSR x h hx
      simp [hhi, this, hRT x hx]
    have hiT : ∀ x ∈ T, hi x = b' x := fun x hx => by
      have : x ∉ S := fun h => hST x h hx
      simp [hhi, this, hx]
    have hlh : ∀ z, lo z ≤ hi z := by
      intro z
      have : z ∈ S ∪ R ∪ T := by rw [hpart.2.2.2]; exact Finset.mem_univ z
      simp only [Finset.mem_union] at this
      rcases this with (h | h) | h
      · rw [loS z h, hiS z h]; linarith [ha z h]
      · rw [loR z h, hiR z h]
      · rw [loT z h, hiT z h]; exact (hb z h).2
    have sumlo : ∀ Y : Finset N, ∑ x ∈ Y, lo x = ∑ x ∈ T ∩ Y, b x - ∑ x ∈ S ∩ Y, a' x := by
      intro Y
      rw [g70fn1_part_sum S R T hpart, Finset.sum_congr rfl (fun x hx => loS x (Finset.mem_inter.1 hx).1),
        Finset.sum_congr rfl (fun x hx => loR x (Finset.mem_inter.1 hx).1),
        Finset.sum_congr rfl (fun x hx => loT x (Finset.mem_inter.1 hx).1)]
      simp only [Finset.sum_neg_distrib, Finset.sum_const_zero]; ring
    have sumhi : ∀ Y : Finset N, ∑ x ∈ Y, hi x = ∑ x ∈ T ∩ Y, b' x - ∑ x ∈ S ∩ Y, a x := by
      intro Y
      rw [g70fn1_part_sum S R T hpart, Finset.sum_congr rfl (fun x hx => hiS x (Finset.mem_inter.1 hx).1),
        Finset.sum_congr rfl (fun x hx => hiR x (Finset.mem_inter.1 hx).1),
        Finset.sum_congr rfl (fun x hx => hiT x (Finset.mem_inter.1 hx).1)]
      simp only [Finset.sum_neg_distrib, Finset.sum_const_zero]; ring
    obtain ⟨f, hs, hn, hc⟩ := g70fn1_hoffman G (fun _ _ => 0) lo hi hlh
      (fun p hp => G.cap_nonneg p hp)
      (fun X => by rw [g70fn1_arcSum_zero, sumhi]; linarith [(hX X).2])
      (fun X => by rw [g70fn1_arcSum_zero, sumlo]; linarith [(hX X).1])
    refine ⟨f, hs, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, hc⟩
    · have := hn x; rw [loS x hx, hiS x hx] at this; constructor <;> linarith [this.1, this.2]
    · have := hn x; rw [loR x hx, hiR x hx] at this; linarith [this.1, this.2]
    · have := hn x; rw [loT x hx, hiT x hx] at this; exact this

end g70fn1F

section g70fn1E
open FlowsNetworks.Feasibility
variable {N : Type} [Fintype N] [DecidableEq N]
set_option linter.unusedSectionVars false

theorem g70fn1_sd (G : Network N) (S R T : Finset N) (hpart : IsPartition S R T)
    (a b : N → ℝ) (ha : ∀ x ∈ S, 0 ≤ a x) (hb : ∀ x ∈ T, 0 ≤ b x) :
    (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
        (∀ x ∈ S, outflow G f x - inflow G f x ≤ a x) ∧
        (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
        (∀ x ∈ T, inflow G f x - outflow G f x ≥ b x) ∧
        (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ↔
      ∀ X : Finset N,
        (∑ x ∈ T ∩ Xᶜ, b x) - (∑ x ∈ S ∩ Xᶜ, a x) ≤ arcSum G G.cap X Xᶜ := by
  constructor
  · rintro ⟨f, hs, hS, hR, hT, hc⟩ X
    obtain ⟨n1, -⟩ := g70fn1_nec G (fun _ _ => 0) f hc X
    rw [g70fn1_arcSum_zero, sub_zero, g70fn1_part_sum S R T hpart] at n1
    have s1 : ∑ x ∈ S ∩ Xᶜ, -a x ≤ ∑ x ∈ S ∩ Xᶜ, (inflow G f x - outflow G f x) :=
      Finset.sum_le_sum fun x hx => by have := hS x (Finset.mem_inter.1 hx).1; linarith
    have s2 : ∑ x ∈ R ∩ Xᶜ, (inflow G f x - outflow G f x) = 0 :=
      Finset.sum_eq_zero fun x hx => by have := hR x (Finset.mem_inter.1 hx).1; linarith
    have s3 : ∑ x ∈ T ∩ Xᶜ, b x ≤ ∑ x ∈ T ∩ Xᶜ, (inflow G f x - outflow G f x) :=
      Finset.sum_le_sum fun x hx => hT x (Finset.mem_inter.1 hx).1
    simp only [Finset.sum_neg_distrib] at s1
    linarith
  · intro hX
    obtain ⟨f, hs, hS, hR, hT, hc⟩ := (g70fn1_two_sided G S R T hpart (fun _ => 0) a b b
      (fun x hx => ⟨le_refl 0, ha x hx⟩) (fun x hx => ⟨hb x hx, le_refl _⟩)).2 (fun X => by
        refine ⟨by linarith [hX X], ?_⟩
        have h1 : 0 ≤ ∑ x ∈ T ∩ X, b x :=
          Finset.sum_nonneg fun x hx => hb x (Finset.mem_inter.1 hx).1
        have h2 := g70fn1_arcSum_nonneg G X Xᶜ
        simp only [Finset.sum_const_zero]; linarith)
    exact ⟨f, hs, fun x hx => (hS x hx).2, hR, fun x hx => (hT x hx).1, hc⟩

theorem g70fn1_arcSum_ite (G : Network N) (g : N → N → ℝ) (X Y : Finset N) :
    arcSum G g X Y = ∑ p ∈ G.arcs, if p.1 ∈ X ∧ p.2 ∈ Y then g p.1 p.2 else 0 := by
  unfold arcSum; rw [Finset.sum_filter]

theorem g70fn1_net_set (G : Network N) (f : N → N → ℝ) (X : Finset N) :
    arcSum G f Finset.univ X - arcSum G f X Finset.univ =
      ∑ x ∈ X, (inflow G f x - outflow G f x) := by
  rw [g70fn1_sumnet, g70fn1_arcSum_ite, g70fn1_arcSum_ite, g70fn1_arcSum_ite, g70fn1_arcSum_ite,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h1 : p.1 ∈ X <;> by_cases h2 : p.2 ∈ X <;> simp [h1, h2]

theorem g70fn1_tsos (G : Network N) (S R T : Finset N) (hpart : IsPartition S R T)
    (a a' b b' : N → ℝ)
    (ha : ∀ x ∈ S, 0 ≤ a x ∧ a x ≤ a' x) (hb : ∀ x ∈ T, 0 ≤ b x ∧ b x ≤ b' x) :
    (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
        (∀ x ∈ S, a x ≤ outflow G f x - inflow G f x ∧ outflow G f x - inflow G f x ≤ a' x) ∧
        (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
        (∀ x ∈ T, b x ≤ inflow G f x - outflow G f x ∧ inflow G f x - outflow G f x ≤ b' x) ∧
        (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ↔
      (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
          (∀ x ∈ S, a x ≤ outflow G f x - inflow G f x) ∧
          (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
          (∀ x ∈ T, inflow G f x - outflow G f x ≤ b' x) ∧
          (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ∧
        (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
          (∀ x ∈ S, outflow G f x - inflow G f x ≤ a' x) ∧
          (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
          (∀ x ∈ T, b x ≤ inflow G f x - outflow G f x) ∧
          (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) := by
  constructor
  · rintro ⟨f, hs, hS, hR, hT, hc⟩
    exact ⟨⟨f, hs, fun x hx => (hS x hx).1, hR, fun x hx => (hT x hx).2, hc⟩,
      ⟨f, hs, fun x hx => (hS x hx).2, hR, fun x hx => (hT x hx).1, hc⟩⟩
  · rintro ⟨⟨f, hs, hS, hR, hT, hc⟩, ⟨g, gs, gS, gR, gT, gc⟩⟩
    refine (g70fn1_two_sided G S R T hpart a a' b b' ha hb).2 (fun X => ⟨?_, ?_⟩)
    · obtain ⟨n1, -⟩ := g70fn1_nec G (fun _ _ => 0) g gc X
      rw [g70fn1_arcSum_zero, sub_zero, g70fn1_part_sum S R T hpart] at n1
      have s1 : ∑ x ∈ S ∩ Xᶜ, -a' x ≤ ∑ x ∈ S ∩ Xᶜ, (inflow G g x - outflow G g x) :=
        Finset.sum_le_sum fun x hx => by have := gS x (Finset.mem_inter.1 hx).1; linarith
      have s2 : ∑ x ∈ R ∩ Xᶜ, (inflow G g x - outflow G g x) = 0 :=
        Finset.sum_eq_zero fun x hx => by have := gR x (Finset.mem_inter.1 hx).1; linarith
      have s3 : ∑ x ∈ T ∩ Xᶜ, b x ≤ ∑ x ∈ T ∩ Xᶜ, (inflow G g x - outflow G g x) :=
        Finset.sum_le_sum fun x hx => gT x (Finset.mem_inter.1 hx).1
      simp only [Finset.sum_neg_distrib] at s1
      rw [ge_iff_le]; linarith
    · obtain ⟨-, n2⟩ := g70fn1_nec G (fun _ _ => 0) f hc X
      rw [g70fn1_arcSum_zero, sub_zero, g70fn1_part_sum S R T hpart] at n2
      have t1 : ∑ x ∈ S ∩ X, a x ≤ ∑ x ∈ S ∩ X, (outflow G f x - inflow G f x) :=
        Finset.sum_le_sum fun x hx => hS x (Finset.mem_inter.1 hx).1
      have t2 : ∑ x ∈ R ∩ X, (outflow G f x - inflow G f x) = 0 :=
        Finset.sum_eq_zero fun x hx => hR x (Finset.mem_inter.1 hx).1
      have t3 : ∑ x ∈ T ∩ X, -b' x ≤ ∑ x ∈ T ∩ X, (outflow G f x - inflow G f x) :=
        Finset.sum_le_sum fun x hx => by have := hT x (Finset.mem_inter.1 hx).1; linarith
      simp only [Finset.sum_neg_distrib] at t3
      rw [ge_iff_le]; linarith

end g70fn1E

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 2.2 (p. 22). Under the hypotheses of
Theorem 2.1 (`0 ≤ a(x) ≤ a'(x)` on `S`, `0 ≤ b(x) ≤ b'(x)` on `T`), the constraints (2.1)–(2.4) are
feasible if and only if each of the constraint sets (2.7) (only the lower bound `a` on `S` and the
upper bound `b'` on `T`) and (2.8) (only the upper bound `a'` on `S` and the lower bound `b` on
`T`) is feasible. -/
theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (S R T : Finset N) (hpart : IsPartition S R T)
    (a a' b b' : N → ℝ)
    (ha : ∀ x ∈ S, 0 ≤ a x ∧ a x ≤ a' x) (hb : ∀ x ∈ T, 0 ≤ b x ∧ b x ≤ b' x) :
    (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
        (∀ x ∈ S, a x ≤ outflow G f x - inflow G f x ∧ outflow G f x - inflow G f x ≤ a' x) ∧
        (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
        (∀ x ∈ T, b x ≤ inflow G f x - outflow G f x ∧ inflow G f x - outflow G f x ≤ b' x) ∧
        (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ↔
      (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
          (∀ x ∈ S, a x ≤ outflow G f x - inflow G f x) ∧
          (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
          (∀ x ∈ T, inflow G f x - outflow G f x ≤ b' x) ∧
          (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ∧
        (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
          (∀ x ∈ S, outflow G f x - inflow G f x ≤ a' x) ∧
          (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
          (∀ x ∈ T, b x ≤ inflow G f x - outflow G f x) ∧
          (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) := by
  exact g70fn1_tsos G S R T hpart a a' b b' ha hb

