-- Prove2me | solution 1 for FlowsNetworks.Matrices.zero_trace_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:38:58.930083+00:00
-- url     : https://prove2.me/submissions/ba77a22c-839a-4bcf-981a-3e858c3e2b33

import Mathlib
import Definitions.Def_FlowsNetworks_Matrices_ZeroOne
open FlowsNetworks.Matrices

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

theorem g70fn1_sumZ2 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (Z : Finset (α ⊕ β)) (h : α ⊕ β → ℝ) :
    ∑ z ∈ Z, h z = ∑ x ∈ Finset.univ.filter (fun x => Sum.inl x ∈ Z), h (Sum.inl x) +
      ∑ y ∈ Finset.univ.filter (fun y => Sum.inr y ∈ Z), h (Sum.inr y) := by
  have : ∑ z ∈ Z, h z = ∑ z, if z ∈ Z then h z else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [this, Fintype.sum_sum_type, Finset.sum_filter, Finset.sum_filter]

theorem g70fn1_ztr_gen (n : ℕ) (a b : Fin n → ℕ)
    (hcut : ∀ X1 Yc : Finset (Fin n), ∑ y ∈ Yc, b y ≤
      ∑ x ∈ X1ᶜ, a x + ((X1 ×ˢ Yc).filter (fun q => q.1 ≠ q.2)).card) :
    ∃ A : Matrix (Fin n) (Fin n) ℕ, FlowsNetworks.Matrices.IsZeroOne A ∧
        (∀ i, ∑ j, A i j ≤ a i) ∧ (∀ j, b j ≤ ∑ i, A i j) ∧ ∑ i, A i i = 0 := by
  classical
  let e : Fin n × Fin n ↪ (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) := ⟨fun q => (Sum.inl q.1, Sum.inr q.2), by
    intro q r h; simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h; exact Prod.ext h.1 h.2⟩
  let G' : g70fn1_Net (Fin n ⊕ Fin n) :=
    ⟨(Finset.univ.filter (fun q : Fin n × Fin n => q.1 ≠ q.2)).map e, fun _ _ => 0, fun _ _ => 1⟩
  have hfs : ∀ (g : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) (Z W : Finset (Fin n ⊕ Fin n)),
      g70fn1_fsum G' g Z W =
      ∑ q ∈ (Finset.univ.filter (fun q : Fin n × Fin n => q.1 ≠ q.2)).filter
        (fun q => Sum.inl q.1 ∈ Z ∧ Sum.inr q.2 ∈ W), g (Sum.inl q.1) (Sum.inr q.2) := by
    intro g Z W; unfold g70fn1_fsum; rw [Finset.filter_map, Finset.sum_map]; rfl
  let lo : Fin n ⊕ Fin n → ℝ := Sum.elim (fun x => -(a x : ℝ)) (fun y => (b y : ℝ))
  let hi : Fin n ⊕ Fin n → ℝ := Sum.elim (fun _ => 0) (fun y => (b y : ℝ))
  have hlh : ∀ z, lo z ≤ hi z := by
    intro z; cases z with
    | inl x => simp [lo, hi]
    | inr y => simp [lo, hi]
  have C1 : ∀ Z : Finset (Fin n ⊕ Fin n), g70fn1_fsum G' G'.low Zᶜ Z - ∑ z ∈ Z, hi z ≤
      g70fn1_fsum G' G'.cap Z Zᶜ := by
    intro Z
    rw [hfs, hfs, g70fn1_sumZ2]
    simp only [G', hi, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (0:ℝ) ≤ ∑ y ∈ Finset.univ.filter (fun y => Sum.inr y ∈ Z), (b y : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have : (0:ℝ) ≤ (((Finset.univ.filter (fun q : Fin n × Fin n => q.1 ≠ q.2)).filter
      (fun q => Sum.inl q.1 ∈ Z ∧ Sum.inr q.2 ∈ Zᶜ)).card : ℝ) := by positivity
    linarith
  have C2 : ∀ Z : Finset (Fin n ⊕ Fin n), g70fn1_fsum G' G'.low Zᶜ Z + ∑ z ∈ Zᶜ, lo z ≤
      g70fn1_fsum G' G'.cap Z Zᶜ := by
    intro Z
    rw [hfs, hfs, g70fn1_sumZ2]
    set X1 := Finset.univ.filter (fun x => Sum.inl x ∈ Z) with hX1
    set Xc := Finset.univ.filter (fun x => Sum.inl x ∈ Zᶜ) with hXc
    set Yc := Finset.univ.filter (fun y => Sum.inr y ∈ Zᶜ) with hYc
    set P := (X1 ×ˢ Yc).filter (fun q => q.1 ≠ q.2) with hP
    set D := (X1 ×ˢ Yc).filter (fun q => ¬ q.1 ≠ q.2) with hD
    have k2 : (Finset.univ.filter (fun q : Fin n × Fin n => q.1 ≠ q.2)).filter
        (fun q => Sum.inl q.1 ∈ Z ∧ Sum.inr q.2 ∈ Zᶜ) = P := by
      ext q; simp [hP, hX1, hYc]; tauto
    have kc : X1.card + Xc.card = n := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (fun x => Sum.inl x ∈ Z)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have hXc' : Xc = Finset.univ.filter (fun x => ¬ Sum.inl x ∈ Z) := by ext; simp [hXc]
      rw [hXc']; exact this
    have kPD : P.card + D.card = X1.card * Yc.card := by
      rw [hP, hD, Finset.card_filter_add_card_filter_not, Finset.card_product]
    have kD1 : D.card ≤ X1.card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro q hq; simp only [hD, Finset.coe_filter, Finset.mem_product] at hq; exact hq.1.1
      · intro q hq r hr h
        simp only [hD, Finset.coe_filter, Finset.mem_product, not_not] at hq hr
        exact Prod.ext h (by rw [← hq.2, ← hr.2, h])
    have kD2 : D.card ≤ Yc.card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro q hq; simp only [hD, Finset.coe_filter, Finset.mem_product] at hq; exact hq.1.2
      · intro q hq r hr h
        simp only [hD, Finset.coe_filter, Finset.mem_product, not_not] at hq hr
        exact Prod.ext (by rw [hq.2, hr.2, h]) h
    have key : ∑ y ∈ Yc, b y ≤ ∑ x ∈ Xc, a x + P.card := by
      have hXc2 : Xc = X1ᶜ := by ext x; simp [hXc, hX1]
      rw [hXc2]; exact hcut X1 Yc
    rw [k2]
    simp only [G', lo, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, Finset.sum_neg_distrib,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    have key' : ((∑ y ∈ Yc, b y : ℕ) : ℝ) ≤ ((∑ x ∈ Xc, a x + P.card : ℕ) : ℝ) := by
      exact_mod_cast key
    push_cast at key' ⊢
    linarith
  obtain ⟨f, hK, hfi, hbd⟩ := g70fn1_main_int G' (fun p _ => by simp [G'])
    lo hi hlh C1 C2 (fun p _ => ⟨⟨0, by simp [G']⟩, ⟨1, by simp [G']⟩⟩)
    (fun z => by
      cases z with
      | inl x => exact ⟨⟨-(a x : ℤ), by simp [lo]⟩, ⟨0, by simp [hi]⟩⟩
      | inr y => exact ⟨⟨(b y : ℤ), by simp [lo]⟩, ⟨(b y : ℤ), by simp [hi]⟩⟩)
  have hs := hK.1
  have hmem : ∀ u v, (u, v) ∈ G'.arcs ↔ ∃ x y, x ≠ y ∧ u = Sum.inl x ∧ v = Sum.inr y := by
    intro u v
    simp only [G', Finset.mem_map]
    constructor
    · rintro ⟨⟨x, y⟩, hxy, he⟩
      have he' : ((Sum.inl x : Fin n ⊕ Fin n), (Sum.inr y : Fin n ⊕ Fin n)) = (u, v) := he
      simp only [Prod.mk.injEq] at he'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxy
      exact ⟨x, y, hxy, he'.1.symm, he'.2.symm⟩
    · rintro ⟨x, y, hxy, rfl, rfl⟩
      exact ⟨⟨x, y⟩, by simpa using hxy, rfl⟩
  have z1 : ∀ x x', f (Sum.inl x) (Sum.inl x') = 0 := fun x x' => hs _ _ (by rw [hmem]; simp)
  have z2 : ∀ y v, f (Sum.inr y) v = 0 := fun y v => hs _ _ (by rw [hmem]; simp)
  let A : Matrix (Fin n) (Fin n) ℕ := fun i j => if f (Sum.inl i) (Sum.inr j) = 1 then 1 else 0
  have h01 : ∀ i j, f (Sum.inl i) (Sum.inr j) = ((A i j : ℕ) : ℝ) := by
    intro i j
    by_cases hij : i = j
    · have : (Sum.inl i, Sum.inr j) ∉ G'.arcs := by
        rw [hmem]; rintro ⟨x, y, hxy, hx, hy⟩
        simp only [Sum.inl.injEq, Sum.inr.injEq] at hx hy; subst hx; subst hy; exact hxy hij
      simp only [A, hs _ _ this]; simp
    have harc : (Sum.inl i, Sum.inr j) ∈ G'.arcs := (hmem _ _).2 ⟨i, j, hij, rfl, rfl⟩
    obtain ⟨k, hk⟩ := hfi _ harc
    have hb2 := hK.2 _ harc
    simp only [G'] at hk hb2
    rw [hk] at hb2
    have k0 : (0 : ℤ) ≤ k := by exact_mod_cast hb2.1
    have k1 : k ≤ 1 := by exact_mod_cast hb2.2
    have : k = 0 ∨ k = 1 := by omega
    simp only [A]
    rcases this with rfl | rfl
    · simp [hk]
    · simp [hk]
  have hdiag : ∀ i, A i i = 0 := by
    intro i
    have : (Sum.inl i, Sum.inr i) ∉ G'.arcs := by
      rw [hmem]; rintro ⟨x, y, hxy, hx, hy⟩
      simp only [Sum.inl.injEq, Sum.inr.injEq] at hx hy; subst hx; subst hy; exact hxy rfl
    simp [A, hs _ _ this]
  have drow : ∀ i, - g70fn1_nfo G' f (Sum.inl i) = - ((∑ j, A i j : ℕ) : ℝ) := by
    intro i
    rw [g70fn1_nfo_full G' f hs, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [z1, z2, h01]
  have dcol : ∀ j, - g70fn1_nfo G' f (Sum.inr j) = ((∑ i, A i j : ℕ) : ℝ) := by
    intro j
    rw [g70fn1_nfo_full G' f hs, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [z1, z2, h01]
  refine ⟨A, fun i j => by simp only [A]; split_ifs <;> simp, fun i => ?_, fun j => ?_,
    Finset.sum_eq_zero fun i _ => hdiag i⟩
  · have := (hbd (Sum.inl i)).1; rw [drow] at this; simp only [lo, Sum.elim_inl] at this
    exact_mod_cast (by linarith : ((∑ j, A i j : ℕ) : ℝ) ≤ a i)
  · have := (hbd (Sum.inr j)).1; rw [dcol] at this; simp only [lo, Sum.elim_inr] at this
    exact_mod_cast this

theorem g70fn1_conj_sum {m n : ℕ} (a : Fin m → ℕ) (t : ℕ) (ht : t ≤ n) :
    ∑ j : Fin n with j.val < t, FlowsNetworks.Matrices.conj a j = ∑ i, min (a i) t := by
  classical
  unfold FlowsNetworks.Matrices.conj
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  trans ∑ i, ∑ j : Fin n, if (j:ℕ) < t then (if (j:ℕ) + 1 ≤ a i then 1 else 0) else 0
  · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> simp
  apply Finset.sum_congr rfl
  intro i _
  have : (∑ j : Fin n, if j.val < t then (if j.val + 1 ≤ a i then 1 else 0) else 0) =
      (Finset.univ.filter (fun j : Fin n => (j : ℕ) < min t (a i))).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : j.val < t <;> by_cases h2 : j.val + 1 ≤ a i <;> simp [h1, h2] <;> omega
  rw [this, Fin.card_filter_val_lt]
  rw [min_comm (a i) t]; omega

theorem g70fn1_antitone_sum {n : ℕ} (b : Fin n → ℕ) (hb : Antitone b) (Y : Finset (Fin n)) :
    ∑ y ∈ Y, b y ≤ ∑ j : Fin n with j.val < Y.card, b j := by
  classical
  set F := Finset.univ.filter (fun j : Fin n => j.val < Y.card) with hF
  have hFc : F.card = Y.card := by
    rw [hF, Fin.card_filter_val_lt]
    have := Y.card_le_univ; simp at this; omega
  have e1 : ∀ s t : Finset (Fin n), ∑ y ∈ s, b y = ∑ y ∈ s \ t, b y + ∑ y ∈ s ∩ t, b y := by
    intro s t
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter s t), Finset.sdiff_union_inter]
  rw [e1 Y F, e1 F Y, Finset.inter_comm]
  apply Nat.add_le_add_right
  have hc : (Y \ F).card = (F \ Y).card := by
    have h1 := Finset.card_sdiff_add_card_inter Y F
    have h2 := Finset.card_sdiff_add_card_inter F Y
    rw [Finset.inter_comm] at h2; omega
  by_cases hne : (Y \ F).Nonempty
  · obtain ⟨y0, hy0⟩ := hne
    have hlt : Y.card < n := by
      have := (Finset.mem_sdiff.1 hy0).2; simp [hF] at this; omega
    set v := b ⟨Y.card, hlt⟩
    have s1 : ∑ y ∈ Y \ F, b y ≤ (Y \ F).card • v := by
      apply Finset.sum_le_card_nsmul
      intro y hy
      have := (Finset.mem_sdiff.1 hy).2; simp [hF] at this
      exact hb (show (⟨Y.card, hlt⟩ : Fin n) ≤ y from this)
    have s2 : (F \ Y).card • v ≤ ∑ x ∈ F \ Y, b x := by
      apply Finset.card_nsmul_le_sum
      intro x hx
      have := (Finset.mem_sdiff.1 hx).1; simp [hF] at this
      exact hb (show x ≤ (⟨Y.card, hlt⟩ : Fin n) from Fin.le_def.2 (by simp; omega))
    rw [hc] at s1; exact s1.trans s2
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp

/-- Gale–Ryser sufficiency in cut form -/
theorem g70fn1_gr (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (hcut : ∀ Y : Finset (Fin n), ∑ y ∈ Y, b y ≤ ∑ i, min (a i) Y.card) :
    ∃ A : Matrix (Fin m) (Fin n) ℕ, FlowsNetworks.Matrices.IsZeroOne A ∧
        (∀ j, b j ≤ ∑ i, A i j) ∧ (∀ i, ∑ j, A i j ≤ a i) := by
  classical
  let e : Fin m × Fin n ↪ (Fin m ⊕ Fin n) × (Fin m ⊕ Fin n) := ⟨fun q => (Sum.inl q.1, Sum.inr q.2), by
    intro q r h; simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h; exact Prod.ext h.1 h.2⟩
  let G' : g70fn1_Net (Fin m ⊕ Fin n) := ⟨Finset.univ.map e, fun _ _ => 0, fun _ _ => 1⟩
  have hfs : ∀ (g : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ) (Z W : Finset (Fin m ⊕ Fin n)),
      g70fn1_fsum G' g Z W =
      ∑ q ∈ Finset.univ.filter (fun q : Fin m × Fin n => Sum.inl q.1 ∈ Z ∧ Sum.inr q.2 ∈ W),
        g (Sum.inl q.1) (Sum.inr q.2) := by
    intro g Z W; unfold g70fn1_fsum; rw [Finset.filter_map, Finset.sum_map]; rfl
  let lo : Fin m ⊕ Fin n → ℝ := Sum.elim (fun x => -(a x : ℝ)) (fun y => (b y : ℝ))
  let hi : Fin m ⊕ Fin n → ℝ := Sum.elim (fun _ => 0) (fun y => (b y : ℝ))
  have hlh : ∀ z, lo z ≤ hi z := by
    intro z; cases z with
    | inl x => simp [lo, hi]
    | inr y => simp [lo, hi]
  have C1 : ∀ Z : Finset (Fin m ⊕ Fin n), g70fn1_fsum G' G'.low Zᶜ Z - ∑ z ∈ Z, hi z ≤
      g70fn1_fsum G' G'.cap Z Zᶜ := by
    intro Z
    rw [hfs, hfs, g70fn1_sumZ2]
    simp only [G', hi, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (0:ℝ) ≤ ∑ y ∈ Finset.univ.filter (fun y => Sum.inr y ∈ Z), (b y : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have : (0:ℝ) ≤ ((Finset.univ.filter (fun q : Fin m × Fin n =>
      Sum.inl q.1 ∈ Z ∧ Sum.inr q.2 ∈ Zᶜ)).card : ℝ) := by positivity
    linarith
  have C2 : ∀ Z : Finset (Fin m ⊕ Fin n), g70fn1_fsum G' G'.low Zᶜ Z + ∑ z ∈ Zᶜ, lo z ≤
      g70fn1_fsum G' G'.cap Z Zᶜ := by
    intro Z
    rw [hfs, hfs, g70fn1_sumZ2]
    set X1 := Finset.univ.filter (fun x => Sum.inl x ∈ Z) with hX1
    set Xc := Finset.univ.filter (fun x => Sum.inl x ∈ Zᶜ) with hXc
    set Yc := Finset.univ.filter (fun y => Sum.inr y ∈ Zᶜ) with hYc
    have k2 : (Finset.univ.filter (fun q : Fin m × Fin n => Sum.inl q.1 ∈ Z ∧ Sum.inr q.2 ∈ Zᶜ)) =
        X1 ×ˢ Yc := by
      ext q; simp [hX1, hYc]
    have kc : X1.card + Xc.card = m := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
        (fun x => Sum.inl x ∈ Z)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have hXc' : Xc = Finset.univ.filter (fun x => ¬ Sum.inl x ∈ Z) := by ext; simp [hXc]
      rw [hXc']; exact this
    have key : ∑ y ∈ Yc, b y ≤ ∑ x ∈ Xc, a x + X1.card * Yc.card := by
      refine le_trans (hcut Yc) ?_
      refine le_trans (Finset.sum_le_sum (fun x _ => (?_ : min (a x) Yc.card ≤
        if Sum.inl x ∈ Z then Yc.card else a x))) ?_
      · split_ifs <;> simp
      · rw [Finset.sum_ite, add_comm, Finset.sum_const, smul_eq_mul]
        apply le_of_eq; congr 1
        apply Finset.sum_congr _ (fun _ _ => rfl); ext x; simp [hXc]
    rw [k2]
    simp only [G', lo, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, Finset.sum_neg_distrib,
      Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_product]
    have key' : ((∑ y ∈ Yc, b y : ℕ) : ℝ) ≤ ((∑ x ∈ Xc, a x + X1.card * Yc.card : ℕ) : ℝ) := by
      exact_mod_cast key
    push_cast at key' ⊢
    linarith
  obtain ⟨f, hK, hfi, hbd⟩ := g70fn1_main_int G' (fun p _ => by simp [G'])
    lo hi hlh C1 C2 (fun p _ => ⟨⟨0, by simp [G']⟩, ⟨1, by simp [G']⟩⟩)
    (fun z => by
      cases z with
      | inl x => exact ⟨⟨-(a x : ℤ), by simp [lo]⟩, ⟨0, by simp [hi]⟩⟩
      | inr y => exact ⟨⟨(b y : ℤ), by simp [lo]⟩, ⟨(b y : ℤ), by simp [hi]⟩⟩)
  have hs := hK.1
  have hmem : ∀ u v, (u, v) ∈ G'.arcs ↔ ∃ x y, u = Sum.inl x ∧ v = Sum.inr y := by
    intro u v
    simp only [G', Finset.mem_map]
    constructor
    · rintro ⟨⟨x, y⟩, _, he⟩
      have he' : ((Sum.inl x : Fin m ⊕ Fin n), (Sum.inr y : Fin m ⊕ Fin n)) = (u, v) := he
      simp only [Prod.mk.injEq] at he'
      exact ⟨x, y, he'.1.symm, he'.2.symm⟩
    · rintro ⟨x, y, rfl, rfl⟩; exact ⟨⟨x, y⟩, Finset.mem_univ _, rfl⟩
  have z1 : ∀ x x', f (Sum.inl x) (Sum.inl x') = 0 := fun x x' => hs _ _ (by rw [hmem]; simp)
  have z2 : ∀ y v, f (Sum.inr y) v = 0 := fun y v => hs _ _ (by rw [hmem]; simp)
  let A : Matrix (Fin m) (Fin n) ℕ := fun i j => if f (Sum.inl i) (Sum.inr j) = 1 then 1 else 0
  have h01 : ∀ i j, f (Sum.inl i) (Sum.inr j) = ((A i j : ℕ) : ℝ) := by
    intro i j
    have harc : (Sum.inl i, Sum.inr j) ∈ G'.arcs := (hmem _ _).2 ⟨i, j, rfl, rfl⟩
    obtain ⟨k, hk⟩ := hfi _ harc
    have hb2 := hK.2 _ harc
    simp only [G'] at hk hb2
    rw [hk] at hb2
    have k0 : (0 : ℤ) ≤ k := by exact_mod_cast hb2.1
    have k1 : k ≤ 1 := by exact_mod_cast hb2.2
    have : k = 0 ∨ k = 1 := by omega
    simp only [A]
    rcases this with rfl | rfl
    · simp [hk]
    · simp [hk]
  have drow : ∀ i, - g70fn1_nfo G' f (Sum.inl i) = - ((∑ j, A i j : ℕ) : ℝ) := by
    intro i
    rw [g70fn1_nfo_full G' f hs, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [z1, z2, h01]
  have dcol : ∀ j, - g70fn1_nfo G' f (Sum.inr j) = ((∑ i, A i j : ℕ) : ℝ) := by
    intro j
    rw [g70fn1_nfo_full G' f hs, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [z1, z2, h01]
  refine ⟨A, fun i j => by simp only [A]; split_ifs <;> simp, fun j => ?_, fun i => ?_⟩
  · have := (hbd (Sum.inr j)).1; rw [dcol] at this; simp only [lo, Sum.elim_inr] at this
    exact_mod_cast this
  · have := (hbd (Sum.inl i)).1; rw [drow] at this; simp only [lo, Sum.elim_inl] at this
    exact_mod_cast (by linarith : ((∑ j, A i j : ℕ) : ℝ) ≤ a i)

theorem g70fn1_dd_succAbove {m : ℕ} (a : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (j : Fin m) :
    FlowsNetworks.Matrices.diagDot a i (i.succAbove j) ↔ (j : ℕ) < a i := by
  unfold FlowsNetworks.Matrices.diagDot
  rcases lt_or_ge (Fin.castSucc j) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt i j h]
    have h1 : ¬ i < Fin.castSucc j := not_lt.2 h.le
    have h2 : i ≠ Fin.castSucc j := ne_of_gt h
    simp [h1, h2]
  · rw [Fin.succAbove_of_le_castSucc i j h]
    have h1 : i < j.succ := lt_of_le_of_lt h (Fin.castSucc_lt_succ)
    simp [h1, ne_of_lt h1]

theorem g70fn1_dd_row {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    (Finset.univ.filter (fun k => FlowsNetworks.Matrices.diagDot a i k)).card = min (a i) (n - 1) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.isLt; omega⟩
  have : Finset.univ.filter (fun k => FlowsNetworks.Matrices.diagDot a i k) =
      (Finset.univ.filter (fun j : Fin m => (j : ℕ) < a i)).map (Fin.succAboveEmb i) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.succAboveEmb,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hk
      have hne : k ≠ i := fun h => hk.1 h.symm
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hne
      exact ⟨j, (g70fn1_dd_succAbove a i j).1 hk, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact (g70fn1_dd_succAbove a i j).2 hj
  rw [this, Finset.card_map, Fin.card_filter_val_lt]
  simp [min_comm]

theorem g70fn1_dc_sum {n : ℕ} (a : Fin n → ℕ) :
    ∑ k, FlowsNetworks.Matrices.diagConj a k = ∑ i, min (a i) (n - 1) := by
  classical
  unfold FlowsNetworks.Matrices.diagConj
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← g70fn1_dd_row a i, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem g70fn1_zc_arith (n t b c S' s : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ n) (hs : n * b ≤ s)
    (h1 : s ≤ S' + c * (n - t)) (h2 : c * (t - 1) ≤ S') : t * b ≤ S' + (c - t) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = t' + 1 + d := ⟨n - (t' + 1), by omega⟩
  simp only [Nat.add_sub_cancel] at h2
  have e1 : t' + 1 + d - (t' + 1) = d := by omega
  rw [e1] at h1
  rcases lt_or_ge b c with hbc | hbc
  · obtain ⟨c', rfl⟩ : ∃ c', c = b + 1 + c' := ⟨c - (b + 1), by omega⟩
    rcases le_or_gt (t' + 1) (b + 1 + c') with hct | hct
    · have : b + 1 + c' - (t' + 1) = b + c' - t' := by omega
      rw [this]
      have : t' ≤ b + c' := by omega
      obtain ⟨r, hr⟩ : ∃ r, b + c' = t' + r := ⟨b + c' - t', by omega⟩
      rw [hr, Nat.add_sub_cancel_left]
      nlinarith
    · have : b + 1 + c' - (t' + 1) = 0 := by omega
      rw [this]
      nlinarith
  · obtain ⟨e, rfl⟩ : ∃ e, b = c + e := ⟨b - c, by omega⟩
    nlinarith

theorem g70fn1_dd_rowk {n : ℕ} (a : Fin n → ℕ) (i : Fin n) (k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun j : Fin n => j.val < k ∧ FlowsNetworks.Matrices.diagDot a i j)).card =
      min (a i) (k - if i.val < k then 1 else 0) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.isLt; omega⟩
  set k' := k - if i.val < k then 1 else 0 with hk'
  have hk'm : k' ≤ m := by
    have := i.isLt; rw [hk']; split_ifs <;> omega
  have : Finset.univ.filter (fun j : Fin (m + 1) => j.val < k ∧ FlowsNetworks.Matrices.diagDot a i j) =
      (Finset.univ.filter (fun j : Fin m => (j : ℕ) < min (a i) k')).map (Fin.succAboveEmb i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.succAboveEmb,
      Function.Embedding.coeFn_mk]
    have key : ∀ j : Fin m, ((i.succAbove j).val < k ∧ FlowsNetworks.Matrices.diagDot a i (i.succAbove j))
        ↔ (j : ℕ) < min (a i) k' := by
      intro j
      rw [g70fn1_dd_succAbove]
      rcases lt_or_ge (Fin.castSucc j) i with h | h
      · rw [Fin.succAbove_of_castSucc_lt i j h]
        have : (j : ℕ) < i := h
        simp only [Fin.coe_castSucc, lt_min_iff, hk']
        split_ifs <;> omega
      · rw [Fin.succAbove_of_le_castSucc i j h]
        have : (i : ℕ) ≤ j := h
        simp only [Fin.val_succ, lt_min_iff, hk']
        split_ifs <;> omega
    constructor
    · intro hx
      have hne : x ≠ i := fun h => hx.2.1 h.symm
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hne
      exact ⟨j, (key j).1 hx, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact (key j).2 hj
  rw [this, Finset.card_map, Fin.card_filter_val_lt]
  omega

theorem g70fn1_dc_sumk {n : ℕ} (a : Fin n → ℕ) (k : ℕ) (hk : k ≤ n) :
    ∑ j : Fin n with j.val < k, FlowsNetworks.Matrices.diagConj a j =
      ∑ i, min (a i) (k - if i.val < k then 1 else 0) := by
  classical
  unfold FlowsNetworks.Matrices.diagConj
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  trans ∑ i, ∑ j : Fin n, if (j:ℕ) < k then (if FlowsNetworks.Matrices.diagDot a i j then 1 else 0) else 0
  · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> simp
  apply Finset.sum_congr rfl
  intro i _
  rw [← g70fn1_dd_rowk a i k hk, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro j _; split_ifs <;> simp_all

theorem g70fn1_prefix {n : ℕ} (C : Finset (Fin n)) (hC : ∀ i j, i ∈ C → j ≤ i → j ∈ C) (t : ℕ) :
    min t C.card ≤ (Finset.univ.filter (fun i : Fin n => i.val < t ∧ i ∈ C)).card := by
  classical
  by_cases hct : C.card ≤ t
  · rw [min_eq_right hct]
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hi⟩
    by_contra hlt; push_neg at hlt
    have : Finset.univ.filter (fun j : Fin n => j.val < i.val + 1) ⊆ C := by
      intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hC i j hi (Fin.le_def.2 (by omega))
    have := Finset.card_le_card this
    rw [Fin.card_filter_val_lt] at this
    have := i.isLt; omega
  · push_neg at hct
    rw [min_eq_left hct.le]
    have : Finset.univ.filter (fun i : Fin n => i.val < t ∧ i ∈ C) =
        Finset.univ.filter (fun i : Fin n => i.val < t) := by
      apply Finset.filter_congr
      intro i _
      constructor
      · exact fun h => h.1
      · intro hit
        refine ⟨hit, ?_⟩
        by_contra hiC
        have : C ⊆ Finset.univ.filter (fun j : Fin n => j.val < i.val) := by
          intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_contra hji; push_neg at hji
          exact hiC (hC j i hj (Fin.le_def.2 hji))
        have := Finset.card_le_card this
        rw [Fin.card_filter_val_lt] at this
        omega
    rw [this, Fin.card_filter_val_lt]
    have : t ≤ n := by have := C.card_le_univ; simp at this; omega
    omega

/-- Chapter II, Theorem 12.4 (Ford–Fulkerson, *Flows in Networks*, p. 89). Let
`a_1 ≥ a_2 ≥ ⋯ ≥ a_n` and `b_1 ≥ b_2 ≥ ⋯ ≥ b_n` be nonnegative integers. There is an `n × n`
(0, 1)-matrix `(a_ij)` with `∑_j a_ij ≤ a_i`, `∑_i a_ij ≥ b_j` and `∑_i a_ii = 0` (12.20) if and
only if `∑_{i=1}^k b_i ≤ ∑_{i=1}^k a**_i` for `k = 1, …, n` (12.21), where `(a**_i)` is the
diagonally restricted conjugate of `(a_i)`. Indices are 0-based: the book's `i` is `i + 1`. -/
theorem solution (n : ℕ) (a b : Fin n → ℕ) (ha : Antitone a) (hb : Antitone b) :
    (∃ A : Matrix (Fin n) (Fin n) ℕ, IsZeroOne A ∧
        (∀ i, ∑ j, A i j ≤ a i) ∧ (∀ j, b j ≤ ∑ i, A i j) ∧ ∑ i, A i i = 0) ↔
      ∀ k : ℕ, 1 ≤ k → k ≤ n →
        ∑ i : Fin n with i.val < k, b i ≤ ∑ i : Fin n with i.val < k, diagConj a i := by
  classical
  constructor
  · rintro ⟨A, hA, hrow, hcol, htr⟩ k _ hkn
    rw [g70fn1_dc_sumk a k hkn]
    calc ∑ j : Fin n with j.val < k, b j ≤ ∑ j : Fin n with j.val < k, ∑ i, A i j :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = ∑ i, ∑ j : Fin n with j.val < k, A i j := Finset.sum_comm
      _ ≤ ∑ i, min (a i) (k - if i.val < k then 1 else 0) := Finset.sum_le_sum fun i _ => by
          apply le_min ((Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans (hrow i))
          have hd : A i i = 0 := (Finset.sum_eq_zero_iff.1 htr) i (Finset.mem_univ _)
          have hF : (Finset.univ.filter (fun j : Fin n => j.val < k)).card = k := by
            rw [Fin.card_filter_val_lt]; omega
          split_ifs with hik
          · have hiF : i ∈ Finset.univ.filter (fun j : Fin n => j.val < k) := by simp [hik]
            rw [← Finset.add_sum_erase _ _ hiF, hd, zero_add]
            refine (Finset.sum_le_sum fun j _ => hA i j).trans ?_
            rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hiF, hF]
          · refine (Finset.sum_le_sum fun j _ => hA i j).trans ?_
            rw [Finset.sum_const, smul_eq_mul, mul_one, hF]; omega
  · intro hcond
    apply g70fn1_ztr_gen n a b
    intro X1 Yc
    set t := Yc.card with ht
    by_cases ht0 : t = 0
    · rw [Finset.card_eq_zero.1 ht0]; simp
    have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.2 ht0
    have htn : t ≤ n := by simpa using Yc.card_le_univ
    have stepAB : ∑ y ∈ Yc, b y ≤ ∑ i, min (a i) (t - if i.val < t then 1 else 0) := by
      calc ∑ y ∈ Yc, b y ≤ ∑ j : Fin n with j.val < t, b j := g70fn1_antitone_sum b hb Yc
        _ ≤ _ := hcond t ht1 htn
        _ = _ := g70fn1_dc_sumk a t htn
    set P := (X1 ×ˢ Yc).filter (fun q => q.1 ≠ q.2) with hP
    set D := (X1 ×ˢ Yc).filter (fun q => ¬ q.1 ≠ q.2) with hD
    have kPD : P.card + D.card = X1.card * t := by
      rw [hP, hD, Finset.card_filter_add_card_filter_not, Finset.card_product]
    have kD : D.card ≤ (X1 ∩ Yc).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro q hq
        simp only [hD, Finset.coe_filter, Finset.mem_product, not_not] at hq
        simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe]
        exact ⟨hq.1.1, hq.2 ▸ hq.1.2⟩
      · intro q hq r hr h
        simp only [hD, Finset.coe_filter, Finset.mem_product, not_not] at hq hr
        exact Prod.ext h (by rw [← hq.2, ← hr.2, h])
    set C := Finset.univ.filter (fun i => t ≤ a i) with hC
    have hU : ∑ i, (if i ∈ X1 then t else a i) = X1.card * t + ∑ x ∈ X1ᶜ, a x := by
      have f1 : Finset.univ.filter (fun i => i ∈ X1) = X1 := by ext; simp
      have f2 : Finset.univ.filter (fun i => ¬ i ∈ X1) = X1ᶜ := by ext; simp
      rw [Finset.sum_ite, Finset.sum_const, smul_eq_mul, f1, f2]
    have hv : (X1 ∩ Yc).card = ∑ i, (if i ∈ X1 ∧ i ∈ Yc then 1 else 0) := by
      rw [Finset.sum_boole]; congr 1; ext x; simp
    have hw' : (Yc.filter (fun i => t ≤ a i)).card = ∑ i, (if i ∈ Yc ∧ t ≤ a i then 1 else 0) := by
      rw [Finset.sum_boole]; congr 1; ext x; simp
    have hpre : (Finset.univ.filter (fun i : Fin n => i.val < t ∧ i ∈ C)).card =
        ∑ i, (if i.val < t ∧ t ≤ a i then 1 else 0) := by
      rw [Finset.sum_boole]; congr 1; ext x; simp [hC]
    have pw0 : ∀ i, (if i ∈ X1 ∧ i ∈ Yc then 1 else 0) +
        min (a i) (t - if i.val < t then 1 else 0) + (if i.val < t ∧ t ≤ a i then 1 else 0) ≤
        (if i ∈ X1 then t else a i) + (if i ∈ Yc ∧ t ≤ a i then 1 else 0) := by
      intro i
      by_cases h1 : i ∈ X1 <;> by_cases h2 : i ∈ Yc <;> by_cases h3 : t ≤ a i <;>
        by_cases h4 : i.val < t <;>
        simp only [h1, h2, h3, h4, and_true, and_false, true_and, false_and, if_true, if_false] <;>
        omega
    have pw := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => pw0 i)
    simp only [Finset.sum_add_distrib] at pw
    rw [← hv, ← hw', ← hpre, hU] at pw
    have hwC : (Yc.filter (fun i => t ≤ a i)).card ≤ min t C.card := by
      apply le_min
      · rw [ht]; exact Finset.card_le_card (Finset.filter_subset _ _)
      · apply Finset.card_le_card; intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hC] at hx ⊢; exact hx.2
    have hpref := g70fn1_prefix C (fun i j hi hji => by
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi.trans (ha hji)) t
    generalize X1.card * t = XT at pw kPD
    generalize ∑ x ∈ X1ᶜ, a x = SA at pw ⊢
    omega

