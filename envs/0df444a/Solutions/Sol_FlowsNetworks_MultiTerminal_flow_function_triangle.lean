-- Prove2me | solution 1 for FlowsNetworks.MultiTerminal.flow_function_triangle
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:16:15.34645+00:00
-- url     : https://prove2.me/submissions/fa8f862c-0798-4f01-939f-3dd711569628

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_UndirectedNetwork
namespace g70fn2_MF

structure Network (N : Type) [Fintype N] [DecidableEq N] where
  arcs : Finset (N × N)
  loopless : ∀ p ∈ arcs, p.1 ≠ p.2
  cap : N → N → ℝ
  cap_nonneg : ∀ p ∈ arcs, 0 ≤ cap p.1 p.2

variable {N : Type} [Fintype N] [DecidableEq N]

def arcsBetween (G : Network N) (X Y : Finset N) : Finset (N × N) :=
  G.arcs.filter (fun p => p.1 ∈ X ∧ p.2 ∈ Y)

def arcSum (G : Network N) (g : N → N → ℝ) (X Y : Finset N) : ℝ :=
  ∑ p ∈ arcsBetween G X Y, g p.1 p.2

def netFlowOut (G : Network N) (f : N → N → ℝ) (x : N) : ℝ :=
  (∑ p ∈ G.arcs.filter (fun p => p.1 = x), f p.1 p.2) -
    ∑ p ∈ G.arcs.filter (fun p => p.2 = x), f p.1 p.2

def Conservation (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) : Prop :=
  netFlowOut G f s = v ∧ netFlowOut G f t = -v ∧
    ∀ x, x ≠ s → x ≠ t → netFlowOut G f x = 0

def SupportedOnArcs (G : Network N) (f : N → N → ℝ) : Prop :=
  ∀ x y, (x, y) ∉ G.arcs → f x y = 0

def IsFlow (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) : Prop :=
  SupportedOnArcs G f ∧ (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2) ∧
    (∀ p ∈ G.arcs, f p.1 p.2 ≤ G.cap p.1 p.2) ∧ Conservation G s t f v

def cutCapacity (G : Network N) (X : Finset N) : ℝ :=
  arcSum G G.cap X Xᶜ

def AugStep (G : Network N) (f : N → N → ℝ) (x y : N) : Prop :=
  ((x, y) ∈ G.arcs ∧ f x y < G.cap x y) ∨ ((y, x) ∈ G.arcs ∧ 0 < f y x)

noncomputable def sourceSet (G : Network N) (f : N → N → ℝ) (s : N) : Finset N := by
  classical
  exact Finset.univ.filter (fun x => ∀ Z : Finset N, s ∈ Z →
    (∀ u w, u ∈ Z → AugStep G f u w → w ∈ Z) → x ∈ Z)

end g70fn2_MF

section g70fn2
open g70fn2_MF
variable {N : Type} [Fintype N] [DecidableEq N]
set_option linter.unusedSectionVars false

def g70fn2_Res (G : Network N) (f : N → N → ℝ) (ε : ℝ) (u w : N) : Prop :=
  ((u, w) ∈ G.arcs ∧ f u w + ε ≤ G.cap u w) ∨ ((w, u) ∈ G.arcs ∧ ε ≤ f w u)

def g70fn2_Step (R : N → N → Prop) (a b : N × List N) : Prop :=
  R a.1 b.1 ∧ b.1 ∉ a.2 ∧ b.2 = b.1 :: a.2

def g70fn2_e (a b : N) : N → N → ℝ := fun u w => if u = a ∧ w = b then 1 else 0

theorem g70fn2_netFlowOut_add (G : Network N) (f g : N → N → ℝ) (z : N) :
    netFlowOut G (f + g) z = netFlowOut G f z + netFlowOut G g z := by
  unfold netFlowOut; simp only [Pi.add_apply, Finset.sum_add_distrib]; ring

theorem g70fn2_netFlowOut_smul (G : Network N) (f : N → N → ℝ) (c : ℝ) (z : N) :
    netFlowOut G (c • f) z = c * netFlowOut G f z := by
  unfold netFlowOut; simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring

theorem g70fn2_netFlowOut_e (G : Network N) (a b : N) (hab : (a, b) ∈ G.arcs) (z : N) :
    netFlowOut G (g70fn2_e a b) z = (if z = a then 1 else 0) - (if z = b then 1 else 0) := by
  unfold netFlowOut g70fn2_e
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

theorem g70fn2_step_mem {R : N → N → Prop} {s : N} {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn2_Step R) (s, [s]) (x, l)) : x ∈ l ∧ s ∈ l := by
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

theorem g70fn2_step_prefix {R : N → N → Prop} {s : N} {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn2_Step R) (s, [s]) (x, l)) :
    ∀ z ∈ l, ∃ l', Relation.ReflTransGen (g70fn2_Step R) (s, [s]) (z, l') := by
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

theorem g70fn2_simple {R : N → N → Prop} {s x : N} (h : Relation.ReflTransGen R s x) :
    ∃ l, Relation.ReflTransGen (g70fn2_Step R) (s, [s]) (x, l) := by
  induction h with
  | refl => exact ⟨_, Relation.ReflTransGen.refl⟩
  | @tail y x _ hyx ih =>
    obtain ⟨l, hl⟩ := ih
    by_cases hx : x ∈ l
    · exact g70fn2_step_prefix hl x hx
    · exact ⟨x :: l, hl.tail ⟨hyx, hx, rfl⟩⟩

/-- augmentation along a simple residual path -/
theorem g70fn2_augment (G : Network N) (f : N → N → ℝ) (s : N)
    (hnn : ∀ p ∈ G.arcs, 0 ≤ f p.1 p.2) (hcap : ∀ p ∈ G.arcs, f p.1 p.2 ≤ G.cap p.1 p.2)
    (ε : ℝ) (hε : 0 < ε) {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn2_Step (g70fn2_Res G f ε)) (s, [s]) (x, l)) :
    ∃ g : N → N → ℝ, (∀ a b, g a b ≠ 0 → a ∈ l ∧ b ∈ l) ∧
      (∀ a b, (a, b) ∉ G.arcs → g a b = 0) ∧
      (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 + g p.1 p.2 ∧ f p.1 p.2 + g p.1 p.2 ≤ G.cap p.1 p.2) ∧
      (∀ z, netFlowOut G g z = (if z = s then ε else 0) - (if z = x then ε else 0)) ∧
      (∀ a b, ∃ k : ℤ, g a b = k * ε) := by
  generalize hb : (x, l) = b at h
  induction h generalizing x l with
  | refl =>
    cases hb
    refine ⟨0, by simp, by simp, fun p hp => by simpa using ⟨hnn p hp, hcap p hp⟩, ?_, ?_⟩
    · intro z; unfold netFlowOut; simp
    · intro a b; exact ⟨0, by simp⟩
  | tail h1 hst ih =>
    rename_i b c
    obtain ⟨y, l0⟩ := b
    obtain ⟨hR, hx, h3⟩ := hst
    cases hb
    simp only at h3 hR hx
    subst h3
    obtain ⟨g, hgl, hgs, hgf, hgn, hgk⟩ := ih rfl
    have hyl : y ∈ l0 := (g70fn2_step_mem h1).1
    have hxy : x ≠ y := fun e => hx (e ▸ hyl)
    rcases hR with ⟨harc, hres⟩ | ⟨harc, hres⟩
    · refine ⟨g + ε • g70fn2_e y x, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab
        by_cases he : a = y ∧ b = x
        · obtain ⟨rfl, rfl⟩ := he; simp [hyl]
        · have : g a b ≠ 0 := by simpa [g70fn2_e, he] using hab
          have := hgl a b this
          exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩
      · intro a b hab
        have : ¬ (a = y ∧ b = x) := by rintro ⟨rfl, rfl⟩; exact hab harc
        simp [g70fn2_e, this, hgs a b hab]
      · intro p hp
        obtain ⟨p1, p2⟩ := p
        by_cases he : p1 = y ∧ p2 = x
        · obtain ⟨rfl, rfl⟩ := he
          have hg0 : g p1 p2 = 0 := by
            by_contra hne; exact hx (hgl _ _ hne).2
          have hfp := hnn _ hp
          simp only [Pi.add_apply, Pi.smul_apply, g70fn2_e, and_self, if_true, smul_eq_mul,
            mul_one, hg0] at hfp ⊢
          constructor <;> linarith
        · simpa [g70fn2_e, he] using hgf _ hp
      · intro z
        rw [g70fn2_netFlowOut_add, g70fn2_netFlowOut_smul, g70fn2_netFlowOut_e G y x harc, hgn]
        clear ih h1 hgf hgk hgl hgs hgn
        by_cases hzs : z = s <;> by_cases hzy : z = y <;> by_cases hzx : z = x <;>
          simp_all
      · intro a b
        obtain ⟨k, hk⟩ := hgk a b
        by_cases he : a = y ∧ b = x
        · refine ⟨k + 1, ?_⟩
          have hk' := hk
          rw [he.1, he.2] at hk' ⊢
          simp only [Pi.add_apply, Pi.smul_apply, g70fn2_e, and_self, if_true,
            smul_eq_mul, mul_one, hk']
          push_cast; ring
        · exact ⟨k, by simp [g70fn2_e, he, hk]⟩
    · refine ⟨g - ε • g70fn2_e x y, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab
        by_cases he : a = x ∧ b = y
        · obtain ⟨rfl, rfl⟩ := he; simp [hyl]
        · have : g a b ≠ 0 := by simpa [g70fn2_e, he] using hab
          have := hgl a b this
          exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩
      · intro a b hab
        have : ¬ (a = x ∧ b = y) := by rintro ⟨rfl, rfl⟩; exact hab harc
        simp [g70fn2_e, this, hgs a b hab]
      · intro p hp
        obtain ⟨p1, p2⟩ := p
        by_cases he : p1 = x ∧ p2 = y
        · obtain ⟨rfl, rfl⟩ := he
          have hg0 : g p1 p2 = 0 := by
            by_contra hne; exact hx (hgl _ _ hne).1
          have hfp := hcap _ hp
          simp only [Pi.sub_apply, Pi.smul_apply, g70fn2_e, and_self, if_true, smul_eq_mul,
            mul_one, hg0] at hfp ⊢
          constructor <;> linarith
        · simpa [g70fn2_e, he] using hgf _ hp
      · intro z
        rw [sub_eq_add_neg, g70fn2_netFlowOut_add, ← neg_smul, g70fn2_netFlowOut_smul,
          g70fn2_netFlowOut_e G x y harc, hgn]
        clear ih h1 hgf hgk hgl hgs hgn
        by_cases hzs : z = s <;> by_cases hzy : z = y <;> by_cases hzx : z = x <;>
          simp_all
      · intro a b
        obtain ⟨k, hk⟩ := hgk a b
        by_cases he : a = x ∧ b = y
        · refine ⟨k - 1, ?_⟩
          have hk' := hk
          rw [he.1, he.2] at hk' ⊢
          simp only [Pi.sub_apply, Pi.smul_apply, g70fn2_e, and_self, if_true,
            smul_eq_mul, mul_one, hk']
          push_cast; ring
        · exact ⟨k, by simp [g70fn2_e, he, hk]⟩

theorem g70fn2_arcSum_eq {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (g : N → N → ℝ)
    (X Y : Finset N) :
    arcSum G g X Y = ∑ p ∈ G.arcs, if p.1 ∈ X ∧ p.2 ∈ Y then g p.1 p.2 else 0 := by
  unfold arcSum arcsBetween; rw [Finset.sum_filter]

theorem g70fn2_cut_submod {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (X Y : Finset N) :
    cutCapacity G (X ∪ Y) + cutCapacity G (X ∩ Y) ≤ cutCapacity G X + cutCapacity G Y := by
  unfold cutCapacity
  simp only [g70fn2_arcSum_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have h := G.cap_nonneg p hp
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
  by_cases a1 : p.1 ∈ X <;> by_cases a2 : p.1 ∈ Y <;> by_cases b1 : p.2 ∈ X <;> by_cases b2 : p.2 ∈ Y <;>
    simp [a1, a2, b1, b2, h]

theorem g70fn2_sum_netFlowOut {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ)
    (X : Finset N) :
    ∑ x ∈ X, netFlowOut G f x = arcSum G f X Xᶜ - arcSum G f Xᶜ X := by
  have key : ∀ (q : N × N → N), ∑ x ∈ X, ∑ p ∈ G.arcs.filter (fun p => q p = x), f p.1 p.2
      = ∑ p ∈ G.arcs, if q p ∈ X then f p.1 p.2 else 0 := by
    intro q
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_ite_eq]
  unfold netFlowOut
  rw [Finset.sum_sub_distrib, key (fun p => p.1), key (fun p => p.2), g70fn2_arcSum_eq, g70fn2_arcSum_eq,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Finset.mem_compl]
  by_cases a : p.1 ∈ X <;> by_cases b : p.2 ∈ X <;> simp [a, b]


theorem g70fn2_flow41 {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) (hf : IsFlow G s t f v)
    (X : Finset N) (hs : s ∈ X) (ht : t ∉ X) :
    v = arcSum G f X Xᶜ - arcSum G f Xᶜ X ∧
      arcSum G f X Xᶜ - arcSum G f Xᶜ X ≤ cutCapacity G X := by
  obtain ⟨hsupp, hnn, hcap, h1, h2, h3⟩ := hf
  constructor
  · rw [← g70fn2_sum_netFlowOut, ← Finset.add_sum_erase X _ hs, h1, Finset.sum_eq_zero]
    · ring
    intro x hx
    exact h3 x (Finset.ne_of_mem_erase hx) (fun h => ht (h ▸ Finset.mem_of_mem_erase hx))
  · have e1 : arcSum G f X Xᶜ ≤ cutCapacity G X := Finset.sum_le_sum fun p hp =>
      hcap p (Finset.mem_filter.1 hp).1
    have e2 : 0 ≤ arcSum G f Xᶜ X := Finset.sum_nonneg fun p hp => hnn p (Finset.mem_filter.1 hp).1
    linarith

theorem g70fn2_sourceSet_s (G : Network N) (f : N → N → ℝ) (s : N) : s ∈ sourceSet G f s := by
  unfold sourceSet; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro Z hs _; exact hs

theorem g70fn2_sourceSet_closed (G : Network N) (f : N → N → ℝ) (s : N) {x y : N}
    (hx : x ∈ sourceSet G f s) (hxy : AugStep G f x y) : y ∈ sourceSet G f s := by
  unfold sourceSet at *; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  intro Z hs hZ; exact hZ x y (hx Z hs hZ) hxy

theorem g70fn2_sourceSet_min (G : Network N) (f : N → N → ℝ) (s : N) (Z : Finset N) (hs : s ∈ Z)
    (hZ : ∀ u w, u ∈ Z → AugStep G f u w → w ∈ Z) : sourceSet G f s ⊆ Z := by
  intro x hx; unfold sourceSet at hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx Z hs hZ

theorem g70fn2_sourceSet_reach (G : Network N) (f : N → N → ℝ) (s : N) {x : N}
    (hx : x ∈ sourceSet G f s) : Relation.ReflTransGen (AugStep G f) s x := by
  classical
  have := g70fn2_sourceSet_min G f s (Finset.univ.filter (fun y => Relation.ReflTransGen (AugStep G f) s y))
    (by simpa using Relation.ReflTransGen.refl) (by
      intro u w hu huw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact hu.tail huw)
  simpa using this hx

theorem g70fn2_res_mono (G : Network N) (f : N → N → ℝ) {ε ε' : ℝ} (h : ε' ≤ ε) {u w : N}
    (hr : g70fn2_Res G f ε u w) : g70fn2_Res G f ε' u w := by
  rcases hr with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨a, by linarith⟩
  · exact Or.inr ⟨a, by linarith⟩

theorem g70fn2_res_exists (G : Network N) (f : N → N → ℝ) (s : N) {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn2_Step (AugStep G f)) (s, [s]) (x, l)) :
    ∃ ε > 0, Relation.ReflTransGen (g70fn2_Step (g70fn2_Res G f ε)) (s, [s]) (x, l) := by
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
    have : ∃ δ > 0, g70fn2_Res G f δ y x := by
      rcases hR with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨G.cap y x - f y x, by linarith, Or.inl ⟨a, by linarith⟩⟩
      · exact ⟨f x y, b, Or.inr ⟨a, le_rfl⟩⟩
    obtain ⟨δ, hδ, hr⟩ := this
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩
    refine Relation.ReflTransGen.tail (Relation.ReflTransGen.mono (fun a b (hab : g70fn2_Step (g70fn2_Res G f ε) a b) => (⟨g70fn2_res_mono G f (min_le_left _ _) hab.1, hab.2⟩ : g70fn2_Step (g70fn2_Res G f (min ε δ)) a b)) _ _ hrt) ?_
    refine ⟨g70fn2_res_mono G f (min_le_right _ _) hr, hx, ?_⟩
    simpa using h3

theorem g70fn2_res_one (G : Network N) (f : N → N → ℝ)
    (hfi : ∀ p ∈ G.arcs, ∃ n : ℤ, f p.1 p.2 = n) (hci : ∀ p ∈ G.arcs, ∃ n : ℤ, G.cap p.1 p.2 = n)
    {u w : N} (h : AugStep G f u w) : g70fn2_Res G f 1 u w := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · obtain ⟨m, hm⟩ := hfi _ a; obtain ⟨n, hn⟩ := hci _ a
    simp only at hm hn
    rw [hm, hn] at b
    have : m < n := by exact_mod_cast b
    have : (m : ℝ) + 1 ≤ n := by exact_mod_cast this
    exact Or.inl ⟨a, by rw [hm, hn]; exact this⟩
  · obtain ⟨m, hm⟩ := hfi _ a
    simp only at hm
    rw [hm] at b
    have : 0 < m := by exact_mod_cast b
    have : (1 : ℝ) ≤ m := by exact_mod_cast this
    exact Or.inr ⟨a, by rw [hm]; exact this⟩

theorem g70fn2_augment_flow (G : Network N) (s t : N) (hst : s ≠ t) (f : N → N → ℝ) (v : ℝ)
    (hf : IsFlow G s t f v) (ε : ℝ) (hε : 0 < ε) {l : List N}
    (h : Relation.ReflTransGen (g70fn2_Step (g70fn2_Res G f ε)) (s, [s]) (t, l)) :
    ∃ g : N → N → ℝ, IsFlow G s t (f + g) (v + ε) ∧ ∀ a b, ∃ k : ℤ, g a b = k * ε := by
  obtain ⟨hsupp, hnn, hcap, h1, h2, h3⟩ := hf
  obtain ⟨g, -, hgs, hgf, hgn, hgk⟩ := g70fn2_augment G f s hnn hcap ε hε h
  refine ⟨g, ⟨?_, fun p hp => (hgf p hp).1, fun p hp => (hgf p hp).2, ?_, ?_, ?_⟩, hgk⟩
  · intro a b hab; simp [hsupp a b hab, hgs a b hab]
  · rw [g70fn2_netFlowOut_add, h1, hgn]; simp [hst]
  · rw [g70fn2_netFlowOut_add, h2, hgn]; simp [Ne.symm hst]; ring
  · intro x hxs hxt; rw [g70fn2_netFlowOut_add, h3 x hxs hxt, hgn]; simp [hxs, hxt]

theorem g70fn2_max_not_mem (G : Network N) (s t : N) (hst : s ≠ t) (f : N → N → ℝ) (v : ℝ)
    (hf : IsFlow G s t f v) (hmax : ∀ g w, IsFlow G s t g w → w ≤ v) : t ∉ sourceSet G f s := by
  intro ht
  obtain ⟨l, hl⟩ := g70fn2_simple (g70fn2_sourceSet_reach G f s ht)
  obtain ⟨ε, hε, hl'⟩ := g70fn2_res_exists G f s hl
  obtain ⟨g, hg, -⟩ := g70fn2_augment_flow G s t hst f v hf ε hε hl'
  have := hmax _ _ hg
  linarith

theorem g70fn2_tight (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) (hf : IsFlow G s t f v)
    (Y : Finset N) (hs : s ∈ Y) (ht : t ∉ Y) (hv : cutCapacity G Y ≤ v) :
    (∀ p ∈ arcsBetween G Y Yᶜ, f p.1 p.2 = G.cap p.1 p.2) ∧
      (∀ p ∈ arcsBetween G Yᶜ Y, f p.1 p.2 = 0) := by
  have h41 := (g70fn2_flow41 G s t f v hf Y hs ht).1
  obtain ⟨hsupp, hnn, hcap, -⟩ := hf
  have e1 : arcSum G f Y Yᶜ ≤ cutCapacity G Y := Finset.sum_le_sum fun p hp =>
      hcap p (Finset.mem_filter.1 hp).1
  have e2 : 0 ≤ arcSum G f Yᶜ Y := Finset.sum_nonneg fun p hp => hnn p (Finset.mem_filter.1 hp).1
  have q1 : ∑ p ∈ arcsBetween G Y Yᶜ, (G.cap p.1 p.2 - f p.1 p.2) = 0 := by
    rw [Finset.sum_sub_distrib]; unfold cutCapacity arcSum at *; linarith
  have q2 : arcSum G f Yᶜ Y = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p hp => by
    have := hcap p (Finset.mem_filter.1 hp).1; linarith)] at q1
  unfold arcSum at q2
  have q3 := (Finset.sum_eq_zero_iff_of_nonneg (fun p hp => hnn p (Finset.mem_filter.1 hp).1)).1 q2
  exact ⟨fun p hp => by linarith [q1 p hp], q3⟩

theorem g70fn2_cut_eq (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) (hf : IsFlow G s t f v)
    (X : Finset N) (hs : s ∈ X) (ht : t ∉ X) (hX : ∀ u w, u ∈ X → AugStep G f u w → w ∈ X) :
    v = cutCapacity G X := by
  rw [(g70fn2_flow41 G s t f v hf X hs ht).1]
  obtain ⟨hsupp, hnn, hcap, -⟩ := hf
  have a1 : arcSum G f X Xᶜ = cutCapacity G X := by
    unfold cutCapacity arcSum
    apply Finset.sum_congr rfl
    intro p hp
    simp only [arcsBetween, Finset.mem_filter, Finset.mem_compl] at hp
    by_contra hne
    have : f p.1 p.2 < G.cap p.1 p.2 := lt_of_le_of_ne (hcap p hp.1) hne
    exact hp.2.2 (hX p.1 p.2 hp.2.1 (Or.inl ⟨hp.1, this⟩))
  have a2 : arcSum G f Xᶜ X = 0 := by
    unfold arcSum
    apply Finset.sum_eq_zero
    intro p hp
    simp only [arcsBetween, Finset.mem_filter, Finset.mem_compl] at hp
    by_contra hne
    have : 0 < f p.1 p.2 := lt_of_le_of_ne (hnn p hp.1) (Ne.symm hne)
    exact hp.2.1 (hX p.2 p.1 hp.2.2 (Or.inr ⟨hp.1, this⟩))
  rw [a1, a2, sub_zero]

theorem g70fn2_max_cut (G : Network N) (s t : N) (hst : s ≠ t) (f : N → N → ℝ) (v : ℝ)
    (hf : IsFlow G s t f v) (hmax : ∀ g w, IsFlow G s t g w → w ≤ v) :
    t ∉ sourceSet G f s ∧ v = cutCapacity G (sourceSet G f s) := by
  have ht := g70fn2_max_not_mem G s t hst f v hf hmax
  exact ⟨ht, g70fn2_cut_eq G s t f v hf _ (g70fn2_sourceSet_s G f s) ht
    (fun u w hu huw => g70fn2_sourceSet_closed G f s hu huw)⟩

end g70fn2

section g70fn2U
variable {N : Type} [Fintype N] [DecidableEq N]

noncomputable def g70fn2_D (G : FlowsNetworks.MultiTerminal.UNetwork N) : g70fn2_MF.Network N := by
  classical
  exact { arcs := Finset.univ.filter (fun p => G.graph.Adj p.1 p.2)
          loopless := fun p hp => by
            have := (Finset.mem_filter.1 hp).2
            exact G.graph.ne_of_adj this
          cap := G.cap
          cap_nonneg := fun p hp => G.cap_nonneg _ _ (Finset.mem_filter.1 hp).2 }

theorem g70fn2_D_arcs (G : FlowsNetworks.MultiTerminal.UNetwork N) (a b : N) :
    (a, b) ∈ (g70fn2_D G).arcs ↔ G.graph.Adj a b := by
  classical
  unfold g70fn2_D; simp

open Classical in
theorem g70fn2_L1 (G : FlowsNetworks.MultiTerminal.UNetwork N) (h : N → N → ℝ) (z : N) :
    ∑ p ∈ (g70fn2_D G).arcs.filter (fun p => p.1 = z), h p.1 p.2 =
      ∑ y, if G.graph.Adj z y then h z y else 0 := by
  have e : (g70fn2_D G).arcs.filter (fun p => p.1 = z) =
      (Finset.univ.filter (fun y => G.graph.Adj z y)).map ⟨Prod.mk z, Prod.mk_right_injective z⟩ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, g70fn2_D_arcs, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨b, h1, rfl, rfl⟩
    · rintro ⟨y, h1, rfl, rfl⟩; exact ⟨h1, rfl⟩
  rw [e, Finset.sum_map, Finset.sum_filter]
  rfl

open Classical in
theorem g70fn2_L2 (G : FlowsNetworks.MultiTerminal.UNetwork N) (h : N → N → ℝ) (z : N) :
    ∑ p ∈ (g70fn2_D G).arcs.filter (fun p => p.2 = z), h p.1 p.2 =
      ∑ y, if G.graph.Adj y z then h y z else 0 := by
  have e : (g70fn2_D G).arcs.filter (fun p => p.2 = z) =
      (Finset.univ.filter (fun y => G.graph.Adj y z)).map ⟨fun y => (y, z), fun a b h => by
        simpa using h⟩ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, g70fn2_D_arcs, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨a, h1, rfl⟩
    · rintro ⟨y, h1, he⟩; cases he; exact ⟨h1, rfl⟩
  rw [e, Finset.sum_map, Finset.sum_filter]
  rfl

open Classical in
theorem g70fn2_net (G : FlowsNetworks.MultiTerminal.UNetwork N) (h : N → N → ℝ) (z : N) :
    g70fn2_MF.netFlowOut (g70fn2_D G) h z =
      ∑ y, ((if G.graph.Adj z y then h z y else 0) - if G.graph.Adj y z then h y z else 0) := by
  unfold g70fn2_MF.netFlowOut
  rw [g70fn2_L1, g70fn2_L2, Finset.sum_sub_distrib]

open Classical in
theorem g70fn2_to_dir (G : FlowsNetworks.MultiTerminal.UNetwork N) (s t : N) (f : N → N → ℝ)
    (w : ℝ) (hf : FlowsNetworks.MultiTerminal.IsFlow G s t f w) :
    g70fn2_MF.IsFlow (g70fn2_D G) s t f w := by
  obtain ⟨h0, hnn, hc, h1, h2, h3⟩ := hf
  have hn : ∀ z, g70fn2_MF.netFlowOut (g70fn2_D G) f z = FlowsNetworks.MultiTerminal.netFlowOut f z := by
    intro z
    rw [g70fn2_net]
    unfold FlowsNetworks.MultiTerminal.netFlowOut
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases ha : G.graph.Adj z y
    · simp [ha, G.graph.adj_symm ha]
    · have hb : ¬ G.graph.Adj y z := fun h => ha (G.graph.adj_symm h)
      simp [ha, hb, h0 z y ha, h0 y z hb]
  refine ⟨fun a b hab => h0 a b (fun h => hab ((g70fn2_D_arcs G a b).2 h)),
    fun p _ => hnn _ _, fun p hp => (hc _ _ ((g70fn2_D_arcs G p.1 p.2).1 hp)).1, ?_, ?_, ?_⟩
  · rw [hn]; exact h1
  · rw [hn]; exact h2
  · intro x hxs hxt; rw [hn]; exact h3 x hxs hxt

open Classical in
theorem g70fn2_to_undir (G : FlowsNetworks.MultiTerminal.UNetwork N) (s t : N) (g : N → N → ℝ)
    (w : ℝ) (hg : g70fn2_MF.IsFlow (g70fn2_D G) s t g w) :
    ∃ f, FlowsNetworks.MultiTerminal.IsFlow G s t f w := by
  obtain ⟨h0, hnn, hc, h1, h2, h3⟩ := hg
  let f : N → N → ℝ := fun a b => if G.graph.Adj a b then max 0 (g a b - g b a) else 0
  have hn : ∀ z, FlowsNetworks.MultiTerminal.netFlowOut f z = g70fn2_MF.netFlowOut (g70fn2_D G) g z := by
    intro z
    rw [g70fn2_net]
    unfold FlowsNetworks.MultiTerminal.netFlowOut
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases ha : G.graph.Adj z y
    · have hb := G.graph.adj_symm ha
      simp only [f, ha, hb, if_true]
      rcases le_total (g z y - g y z) 0 with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · have hb : ¬ G.graph.Adj y z := fun h => ha (G.graph.adj_symm h)
      simp [f, ha, hb]
  refine ⟨f, fun a b hab => by simp [f, hab], fun a b => ?_, fun a b hab => ?_, ?_, ?_, ?_⟩
  · simp only [f]; split_ifs <;> simp
  · have hab' := G.graph.adj_symm hab
    have c1 := hc (a, b) ((g70fn2_D_arcs G a b).2 hab)
    have c2 := hc (b, a) ((g70fn2_D_arcs G b a).2 hab')
    have n1 := hnn (a, b) ((g70fn2_D_arcs G a b).2 hab)
    have n2 := hnn (b, a) ((g70fn2_D_arcs G b a).2 hab')
    have hcs := G.cap_symm a b
    simp only [g70fn2_D] at c1 c2 n1 n2
    simp only [f, hab, hab', if_true]
    refine ⟨max_le (G.cap_nonneg a b hab) (by linarith), max_le (G.cap_nonneg a b hab) (by linarith), ?_⟩
    rcases le_total (g a b - g b a) 0 with h | h
    · rw [max_eq_left h]; ring
    · rw [max_eq_left (by linarith : g b a - g a b ≤ 0)]; ring
  · rw [hn]; exact h1
  · rw [hn]; exact h2
  · intro x hxs hxt; rw [hn]; exact h3 x hxs hxt

end g70fn2U

open FlowsNetworks.MultiTerminal

theorem g70fn2_weak {N : Type} [Fintype N] [DecidableEq N] (G : UNetwork N) (s t : N) (f : N → N → ℝ)
    (w : ℝ) (hf : IsFlow G s t f w) (X : Finset N) (hs : s ∈ X) (ht : t ∉ X) :
    w ≤ g70fn2_MF.cutCapacity (g70fn2_D G) X := by
  have := g70fn2_flow41 (g70fn2_D G) s t f w (g70fn2_to_dir G s t f w hf) X hs ht
  linarith [this.1, this.2]

theorem g70fn2_mincut {N : Type} [Fintype N] [DecidableEq N] (G : UNetwork N) (x y : N) (hxy : x ≠ y)
    (w : ℝ) (hw : IsMaxFlowValue G x y w) :
    ∃ X : Finset N, x ∈ X ∧ y ∉ X ∧ w = g70fn2_MF.cutCapacity (g70fn2_D G) X := by
  obtain ⟨⟨f, hf⟩, hmax⟩ := hw
  have hfD := g70fn2_to_dir G x y f w hf
  have hmaxD : ∀ g u, g70fn2_MF.IsFlow (g70fn2_D G) x y g u → u ≤ w := by
    intro g u hg
    obtain ⟨f', hf'⟩ := g70fn2_to_undir G x y g u hg
    exact hmax ⟨f', hf'⟩
  obtain ⟨hy, hc⟩ := g70fn2_max_cut (g70fn2_D G) x y hxy f w hfD hmaxD
  exact ⟨_, g70fn2_sourceSet_s _ f x, hy, hc⟩

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : UNetwork N) (v : N → N → ℝ) (hv : IsFlowFunction G v)
    (x y z : N) (hxy : x ≠ y) (hxz : x ≠ z) (hzy : z ≠ y) :
    v x y ≥ min (v x z) (v z y) := by
  obtain ⟨X, hx, hy, hc⟩ := g70fn2_mincut G x y hxy (v x y) (hv x y hxy)
  by_cases hz : z ∈ X
  · obtain ⟨⟨f, hf⟩, -⟩ := hv z y hzy
    have := g70fn2_weak G z y f _ hf X hz hy
    exact min_le_of_right_le (by linarith)
  · obtain ⟨⟨f, hf⟩, -⟩ := hv x z hxz
    have := g70fn2_weak G x z f _ hf X hx hz
    exact min_le_of_left_le (by linarith)
