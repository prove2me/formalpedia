-- Prove2me | solution 1 for FlowsNetworks.MultiTerminal.realizability_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:50:27.549677+00:00
-- url     : https://prove2.me/submissions/3382cc00-d810-4672-bd8c-0f97a3d9227e

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

theorem g71n_tri {N : Type} [Fintype N] [DecidableEq N]
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


open FlowsNetworks.MultiTerminal

section g71n
set_option linter.unusedSectionVars false
variable {N : Type} [Fintype N] [DecidableEq N]

lemma g71n_net_add (f g : N → N → ℝ) (a : N) :
    netFlowOut (fun p q => f p q + g p q) a = netFlowOut f a + netFlowOut g a := by
  simp only [netFlowOut, Finset.sum_add_distrib]; ring

lemma g71n_net_smul (s : ℝ) (f : N → N → ℝ) (a : N) :
    netFlowOut (fun p q => s * f p q) a = s * netFlowOut f a := by
  simp only [netFlowOut, ← Finset.mul_sum]; ring

lemma g71n_net_delta (z y : N) (t : ℝ) (a : N) :
    netFlowOut (fun p q => if p = z ∧ q = y then t else 0) a
      = (if a = z then t else 0) - (if a = y then t else 0) := by
  simp only [netFlowOut]
  congr 1
  · by_cases h : a = z
    · subst h; simp
    · simp [h]
  · by_cases h : a = y
    · subst h; simp
    · simp [h]

lemma g71n_net_transpose (f : N → N → ℝ) (a : N) :
    netFlowOut (fun p q => f q p) a = - netFlowOut f a := by
  simp only [netFlowOut]; ring

lemma g71n_flow_rev (G : UNetwork N) (s t : N) (f : N → N → ℝ) (w : ℝ) (hf : IsFlow G s t f w) :
    IsFlow G t s (fun p q => f q p) w := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  refine ⟨fun x y h => h1 y x (fun h' => h h'.symm), fun x y => h2 y x, fun x y h => ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := h3 y x h.symm
    refine ⟨?_, ?_, ?_⟩
    · rw [G.cap_symm]; exact a
    · rw [G.cap_symm]; exact b
    · exact c
  · rw [g71n_net_transpose, h5]; ring
  · rw [g71n_net_transpose, h4]
  · intro x hx1 hx2; rw [g71n_net_transpose, h6 x hx2 hx1]; ring

lemma g71n_max_rev (G : UNetwork N) (s t : N) (w : ℝ) (h : IsMaxFlowValue G s t w) :
    IsMaxFlowValue G t s w := by
  obtain ⟨⟨f, hf⟩, hmax⟩ := h
  refine ⟨⟨_, g71n_flow_rev G s t f w hf⟩, ?_⟩
  rintro u ⟨g, hg⟩
  exact hmax ⟨_, g71n_flow_rev G t s g u hg⟩

/-- the network with an extra arc z—y of capacity c -/
noncomputable def g71n_ext (G : UNetwork N) (z y : N) (c : ℝ) (hc : 0 ≤ c) : UNetwork N where
  graph := G.graph ⊔ SimpleGraph.fromRel (fun a b => a = z ∧ b = y)
  cap := fun a b => if (a = z ∧ b = y) ∨ (a = y ∧ b = z) then c else G.cap a b
  cap_symm := by
    intro a b
    by_cases h : (a = z ∧ b = y) ∨ (a = y ∧ b = z)
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto), G.cap_symm]
  cap_nonneg := by
    intro a b hab
    by_cases h : (a = z ∧ b = y) ∨ (a = y ∧ b = z)
    · rw [if_pos h]; exact hc
    · rw [if_neg h]
      rcases hab with hab | hab
      · exact G.cap_nonneg _ _ hab
      · simp [SimpleGraph.fromRel_adj] at hab; tauto

lemma g71n_ext_adj (G : UNetwork N) (z y : N) (c : ℝ) (hc : 0 ≤ c) (hzy : z ≠ y) (a b : N) :
    (g71n_ext G z y c hc).graph.Adj a b ↔ G.graph.Adj a b ∨ (a = z ∧ b = y) ∨ (a = y ∧ b = z) := by
  simp only [g71n_ext, SimpleGraph.sup_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact Or.inl h
    · right; tauto
  · rintro (h | h | h)
    · exact Or.inl h
    · right; refine ⟨?_, Or.inl h⟩; rw [h.1, h.2]; exact hzy
    · right; refine ⟨?_, Or.inr ⟨h.2, h.1⟩⟩; rw [h.1, h.2]; exact hzy.symm


lemma g71n_zero_flow {N : Type} [Fintype N] [DecidableEq N] (H : UNetwork N) (s t : N) (hst : s ≠ t) :
    IsFlow H s t (fun _ _ => 0) 0 := by
  refine ⟨fun _ _ _ => rfl, fun _ _ => le_refl 0, fun a b hab => ⟨H.cap_nonneg a b hab, H.cap_nonneg a b hab, by ring⟩, ?_, ?_, ?_⟩
  · simp [netFlowOut]
  · simp [netFlowOut]
  · intro _ _ _; simp [netFlowOut]

section g71nB
set_option linter.unusedSectionVars false
variable {N : Type} [Fintype N] [DecidableEq N]
variable (G : UNetwork N) (S : Finset N) (hsupp : ∀ a b, G.graph.Adj a b → a ∈ S ∧ b ∈ S)
  (z y : N) (hz : z ∉ S) (hy : y ∈ S) (c : ℝ) (hc : 0 ≤ c)
include hsupp hz hy

lemma g71n_zy : z ≠ y := fun h => hz (h ▸ hy)

lemma g71n_notadj_z (b : N) (hb : b ≠ y) : ¬ (g71n_ext G z y c hc).graph.Adj z b := by
  rw [g71n_ext_adj G z y c hc (g71n_zy G S hsupp z y hz hy)]
  rintro (h | h | h)
  · exact hz (hsupp _ _ h).1
  · exact hb h.2
  · exact (g71n_zy G S hsupp z y hz hy) h.1

lemma g71n_cap_old (a b : N) (h : G.graph.Adj a b) : (g71n_ext G z y c hc).cap a b = G.cap a b := by
  have ha := (hsupp _ _ h).1; have hb := (hsupp _ _ h).2
  show (if (a = z ∧ b = y) ∨ (a = y ∧ b = z) then c else G.cap a b) = G.cap a b
  rw [if_neg]
  rintro (⟨rfl, -⟩ | ⟨-, rfl⟩)
  · exact hz ha
  · exact hz hb

lemma g71n_cap_new : (g71n_ext G z y c hc).cap z y = c := by
  show (if (z = z ∧ y = y) ∨ (z = y ∧ y = z) then c else G.cap z y) = c
  rw [if_pos (Or.inl ⟨rfl, rfl⟩)]

lemma g71n_cap_new' : (g71n_ext G z y c hc).cap y z = c := by
  rw [(g71n_ext G z y c hc).cap_symm]; exact g71n_cap_new G S hsupp z y hz hy c hc

lemma g71n_net_z (f : N → N → ℝ) (hf : ∀ a b, ¬ (g71n_ext G z y c hc).graph.Adj a b → f a b = 0) :
    netFlowOut f z = f z y - f y z := by
  have hzy := g71n_zy G S hsupp z y hz hy
  simp only [netFlowOut]
  rw [Finset.sum_eq_single y, Finset.sum_eq_single y]
  · intro b _ hb
    apply hf
    intro h; exact g71n_notadj_z G S hsupp z y hz hy c hc b hb ((g71n_ext G z y c hc).graph.adj_symm h)
  · simp
  · intro b _ hb; exact hf _ _ (g71n_notadj_z G S hsupp z y hz hy c hc b hb)
  · simp

/-- flows of the extended network avoiding z are flows of the old one -/
lemma g71n_restrict (s t : N) (hs : s ≠ z) (ht : t ≠ z) (f : N → N → ℝ) (w : ℝ)
    (hf : IsFlow (g71n_ext G z y c hc) s t f w) : IsFlow G s t f w := by
  have hzy := g71n_zy G S hsupp z y hz hy
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  have hnet := g71n_net_z G S hsupp z y hz hy c hc f h1
  rw [h6 z hs.symm ht.symm] at hnet
  have hadj : (g71n_ext G z y c hc).graph.Adj z y := by
    rw [g71n_ext_adj G z y c hc hzy]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  have hp := (h3 z y hadj).2.2
  have hzy0 : f z y = 0 := by
    rcases mul_eq_zero.1 hp with h | h
    · exact h
    · linarith
  have hyz0 : f y z = 0 := by linarith
  refine ⟨fun a b hab => ?_, h2, fun a b hab => ?_, h4, h5, h6⟩
  · by_cases hG : (g71n_ext G z y c hc).graph.Adj a b
    · rw [g71n_ext_adj G z y c hc hzy] at hG
      rcases hG with hG | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hG hab
      · exact hzy0
      · exact hyz0
    · exact h1 a b hG
  · have hG : (g71n_ext G z y c hc).graph.Adj a b := by
      rw [g71n_ext_adj G z y c hc hzy]; exact Or.inl hab
    rw [← g71n_cap_old G S hsupp z y hz hy c hc a b hab]
    exact h3 a b hG

/-- flows of the old network are flows of the extended one -/
lemma g71n_extend (s t : N) (f : N → N → ℝ) (w : ℝ)
    (hf : IsFlow G s t f w) : IsFlow (g71n_ext G z y c hc) s t f w := by
  have hzy := g71n_zy G S hsupp z y hz hy
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  have hzy0 : f z y = 0 := h1 z y (fun h => hz (hsupp _ _ h).1)
  have hyz0 : f y z = 0 := h1 y z (fun h => hz (hsupp _ _ h).2)
  refine ⟨fun a b hab => ?_, h2, fun a b hab => ?_, h4, h5, h6⟩
  · apply h1; intro h; apply hab; rw [g71n_ext_adj G z y c hc hzy]; exact Or.inl h
  · rw [g71n_ext_adj G z y c hc hzy] at hab
    rcases hab with hab | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [g71n_cap_old G S hsupp z y hz hy c hc a b hab]; exact h3 a b hab
    · rw [ha, hb, g71n_cap_new G S hsupp z y hz hy c hc, hzy0, hyz0]; exact ⟨hc, hc, by ring⟩
    · rw [ha, hb, g71n_cap_new' G S hsupp z y hz hy c hc, hzy0, hyz0]; exact ⟨hc, hc, by ring⟩

lemma g71n_max_iff (s t : N) (hs : s ≠ z) (ht : t ≠ z) (w : ℝ) :
    IsMaxFlowValue (g71n_ext G z y c hc) s t w ↔ IsMaxFlowValue G s t w := by
  have : {u : ℝ | ∃ f, IsFlow (g71n_ext G z y c hc) s t f u} = {u : ℝ | ∃ f, IsFlow G s t f u} := by
    ext u; constructor
    · rintro ⟨f, hf⟩; exact ⟨f, g71n_restrict G S hsupp z y hz hy c hc s t hs ht f u hf⟩
    · rintro ⟨f, hf⟩; exact ⟨f, g71n_extend G S hsupp z y hz hy c hc s t f u hf⟩
  unfold IsMaxFlowValue; rw [this]


/-- upper bound: flows from z through the pendant arc -/
lemma g71n_up1 (x : N) (hx : x ≠ z) (f : N → N → ℝ) (w : ℝ)
    (hf : IsFlow (g71n_ext G z y c hc) z x f w) : w ≤ c ∧ f z y - f y z = w := by
  have hzy := g71n_zy G S hsupp z y hz hy
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  have hnet := g71n_net_z G S hsupp z y hz hy c hc f h1
  have hadj : (g71n_ext G z y c hc).graph.Adj z y := by
    rw [g71n_ext_adj G z y c hc hzy]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  have := (h3 z y hadj).1
  rw [g71n_cap_new G S hsupp z y hz hy c hc] at this
  have := h2 y z
  constructor <;> linarith

lemma g71n_up2 (x : N) (hx : x ≠ z) (hxy : x ≠ y) (f : N → N → ℝ) (w : ℝ)
    (hf : IsFlow (g71n_ext G z y c hc) z x f w) :
    IsFlow G y x (fun a b => if (a = z ∧ b = y) ∨ (a = y ∧ b = z) then 0 else f a b) w := by
  have hzy := g71n_zy G S hsupp z y hz hy
  have hw := (g71n_up1 G S hsupp z y hz hy c hc x hx f w hf).2
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  have hfe : (fun a b => if (a = z ∧ b = y) ∨ (a = y ∧ b = z) then 0 else f a b)
      = fun a b => (f a b + (-1) * (if a = z ∧ b = y then f z y else 0))
          + (-1) * (if a = y ∧ b = z then f y z else 0) := by
    funext a b
    by_cases h1' : a = z ∧ b = y
    · rw [if_pos (Or.inl h1'), if_pos h1', if_neg]; · obtain ⟨rfl, rfl⟩ := h1'; ring
      rintro ⟨ha, hb⟩; exact hzy (h1'.1 ▸ ha)
    · by_cases h2' : a = y ∧ b = z
      · rw [if_pos (Or.inr h2'), if_neg h1', if_pos h2']; obtain ⟨rfl, rfl⟩ := h2'; ring
      · rw [if_neg (by tauto), if_neg h1', if_neg h2']; ring
  have hnet : ∀ a, netFlowOut (fun a b => if (a = z ∧ b = y) ∨ (a = y ∧ b = z) then 0 else f a b) a
      = netFlowOut f a - ((if a = z then f z y else 0) - (if a = y then f z y else 0))
          - ((if a = y then f y z else 0) - (if a = z then f y z else 0)) := by
    intro a
    rw [hfe, g71n_net_add, g71n_net_add, g71n_net_smul, g71n_net_smul, g71n_net_delta, g71n_net_delta]
    ring
  refine ⟨fun a b hab => ?_, fun a b => ?_, fun a b hab => ?_, ?_, ?_, ?_⟩
  · by_cases hn : (a = z ∧ b = y) ∨ (a = y ∧ b = z)
    · simp only [if_pos hn]
    · simp only [if_neg hn]
      apply h1
      rw [g71n_ext_adj G z y c hc hzy]; tauto
  · by_cases hn : (a = z ∧ b = y) ∨ (a = y ∧ b = z)
    · simp only [if_pos hn]; exact le_refl 0
    · simp only [if_neg hn]; exact h2 a b
  · have ha := (hsupp _ _ hab).1; have hb := (hsupp _ _ hab).2
    have hn : ¬ ((a = z ∧ b = y) ∨ (a = y ∧ b = z)) := by
      rintro (⟨rfl, -⟩ | ⟨-, rfl⟩) <;> contradiction
    have hn' : ¬ ((b = z ∧ a = y) ∨ (b = y ∧ a = z)) := by tauto
    simp only [if_neg hn, if_neg hn']
    have hG : (g71n_ext G z y c hc).graph.Adj a b := by
      rw [g71n_ext_adj G z y c hc hzy]; exact Or.inl hab
    rw [← g71n_cap_old G S hsupp z y hz hy c hc a b hab]
    exact h3 a b hG
  · rw [hnet, h6 y hzy.symm hxy.symm]; simp [hzy.symm]; linarith
  · rw [hnet, h5]; simp [hx, hxy]
  · intro a ha1 ha2
    rw [hnet]
    by_cases haz : a = z
    · subst haz; simp [hzy, h4]; linarith
    · rw [h6 a haz ha2]; simp [haz, ha1]


/-- the lower-bound flow: scaled old flow plus pendant arc -/
lemma g71n_low (x : N) (hxS : x ∈ S) (hxy : x ≠ y) (g : N → N → ℝ) (V : ℝ) (hg : IsFlow G y x g V)
    (σ t : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (ht0 : 0 ≤ t) (htc : t ≤ c) (hσV : σ * V = t) :
    IsFlow (g71n_ext G z y c hc) z x (fun a b => σ * g a b + (if a = z ∧ b = y then t else 0)) t := by
  have hzy := g71n_zy G S hsupp z y hz hy
  have hxz : x ≠ z := fun h => hz (h ▸ hxS)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  have hnet : ∀ a, netFlowOut (fun a b => σ * g a b + (if a = z ∧ b = y then t else 0)) a
      = σ * netFlowOut g a + ((if a = z then t else 0) - (if a = y then t else 0)) := by
    intro a
    rw [g71n_net_add (fun a b => σ * g a b), g71n_net_smul, g71n_net_delta]
  have gz1 : ∀ b, g z b = 0 := fun b => h1 z b (fun h => hz (hsupp _ _ h).1)
  have gz2 : ∀ b, g b z = 0 := fun b => h1 b z (fun h => hz (hsupp _ _ h).2)
  refine ⟨fun a b hab => ?_, fun a b => ?_, fun a b hab => ?_, ?_, ?_, ?_⟩
  · rw [g71n_ext_adj G z y c hc hzy] at hab
    beta_reduce
    rw [h1 a b (fun h => hab (Or.inl h)), if_neg (fun h => hab (Or.inr (Or.inl h)))]; ring
  · have := h2 a b
    have : 0 ≤ (if a = z ∧ b = y then t else 0) := by split_ifs <;> linarith
    positivity
  · rw [g71n_ext_adj G z y c hc hzy] at hab
    rcases hab with hab | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have ha' := (hsupp _ _ hab).1; have hb' := (hsupp _ _ hab).2
      have hnz : a ≠ z := fun h => hz (h ▸ ha')
      have hnz' : b ≠ z := fun h => hz (h ▸ hb')
      simp only [hnz, hnz', false_and, if_false, add_zero]
      rw [g71n_cap_old G S hsupp z y hz hy c hc a b hab]
      obtain ⟨q1, q2, q3⟩ := h3 a b hab
      have := h2 a b; have := h2 b a
      refine ⟨?_, ?_, ?_⟩
      · nlinarith
      · nlinarith
      · have : σ * g a b * (σ * g b a) = σ * σ * (g a b * g b a) := by ring
        rw [this, q3, mul_zero]
    · beta_reduce; rw [ha, hb, g71n_cap_new G S hsupp z y hz hy c hc, gz1, gz2]
      simp [hzy, hzy.symm]
      exact ⟨htc, hc⟩
    · beta_reduce; rw [ha, hb, g71n_cap_new' G S hsupp z y hz hy c hc, gz1, gz2]
      simp [hzy, hzy.symm]
      exact ⟨hc, htc⟩
  · rw [hnet, h6 z hzy hxz.symm]; simp [hzy]
  · rw [hnet, h5]; simp [hxz, hxy]; linarith
  · intro a ha1 ha2
    rw [hnet]
    by_cases hay : a = y
    · subst hay; rw [h4]; simp [ha1]; linarith
    · rw [h6 a hay ha2]; simp [ha1, hay]

lemma g71n_pend (x : N) (hxS : x ∈ S) (hxy : x ≠ y) (V : ℝ) (hV : IsMaxFlowValue G y x V) :
    IsMaxFlowValue (g71n_ext G z y c hc) z x (min c V) := by
  have hzy := g71n_zy G S hsupp z y hz hy
  have hxz : x ≠ z := fun h => hz (h ▸ hxS)
  obtain ⟨⟨g, hg⟩, hmax⟩ := hV
  have hV0 : 0 ≤ V := hmax ⟨_, g71n_zero_flow G y x hxy.symm⟩
  refine ⟨⟨_, g71n_low G S hsupp z y hz hy c hc x hxS hxy g V hg (min c V / V) (min c V)
      (div_nonneg (le_min hc hV0) hV0) ?_ (le_min hc hV0) (min_le_left _ _) ?_⟩, ?_⟩
  · rcases hV0.lt_or_eq with h | h
    · rw [div_le_one h]; exact min_le_right _ _
    · rw [← h]; simp
  · rcases hV0.lt_or_eq with h | h
    · field_simp
    · rw [← h]; simp [min_eq_right hc]
  · rintro w ⟨f, hf⟩
    have u1 := (g71n_up1 G S hsupp z y hz hy c hc x hxz f w hf).1
    have u2 := hmax ⟨_, g71n_up2 G S hsupp z y hz hy c hc x hxz hxy f w hf⟩
    exact le_min u1 u2

lemma g71n_pend_y : IsMaxFlowValue (g71n_ext G z y c hc) z y c := by
  have hzy := g71n_zy G S hsupp z y hz hy
  refine ⟨⟨fun a b => if a = z ∧ b = y then c else 0, ?_⟩, ?_⟩
  · refine ⟨fun a b hab => ?_, fun a b => ?_, fun a b hab => ?_, ?_, ?_, ?_⟩
    · beta_reduce; rw [if_neg]; rintro ⟨ha, hb⟩; apply hab
      rw [g71n_ext_adj G z y c hc hzy]; exact Or.inr (Or.inl ⟨ha, hb⟩)
    · beta_reduce; split_ifs <;> linarith
    · have hcap := (g71n_ext G z y c hc).cap_nonneg a b hab
      rw [g71n_ext_adj G z y c hc hzy] at hab
      rcases hab with hab | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have ha' := (hsupp _ _ hab).1; have hb' := (hsupp _ _ hab).2
        have hnz : a ≠ z := fun h => hz (h ▸ ha')
        have hnz' : b ≠ z := fun h => hz (h ▸ hb')
        simp only [hnz, hnz', false_and, if_false]
        exact ⟨hcap, by rw [(g71n_ext G z y c hc).cap_symm] at hcap ⊢; exact (g71n_ext G z y c hc).cap_nonneg b a (by
          rw [g71n_ext_adj G z y c hc hzy]; exact Or.inl hab.symm), by ring⟩
      · rw [ha, hb, g71n_cap_new G S hsupp z y hz hy c hc]; simp [hzy, hzy.symm, hc]
      · rw [ha, hb, g71n_cap_new' G S hsupp z y hz hy c hc]; simp [hzy, hzy.symm, hc]
    · rw [g71n_net_delta]; simp [hzy]
    · rw [g71n_net_delta]; simp [hzy.symm]
    · intro a h1 h2; rw [g71n_net_delta]; simp [h1, h2]
  · rintro w ⟨f, hf⟩
    exact (g71n_up1 G S hsupp z y hz hy c hc y hzy.symm f w hf).1

end g71nB

lemma g71n_edgeSet_ext {N : Type} [Fintype N] [DecidableEq N] (G : UNetwork N) (z y : N) (c : ℝ)
    (hc : 0 ≤ c) (hzy : z ≠ y) :
    (g71n_ext G z y c hc).graph.edgeSet = insert s(z, y) G.graph.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet, g71n_ext_adj G z y c hc hzy, Set.mem_insert_iff, SimpleGraph.mem_edgeSet,
      Sym2.eq_iff]
    tauto

lemma g71n_mainT {N : Type} [Fintype N] [DecidableEq N]
    (v : N → N → ℝ)
    (hsymm : ∀ x y : N, x ≠ y → v x y = v y x)
    (hnonneg : ∀ x y : N, x ≠ y → 0 ≤ v x y)
    (htri : ∀ x y z : N, x ≠ y → x ≠ z → z ≠ y → v x y ≥ min (v x z) (v z y)) (S : Finset N) :
    ∃ G : UNetwork N, (∀ a b, G.graph.Adj a b → a ∈ S ∧ b ∈ S) ∧
      (∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → IsMaxFlowValue G x x' (v x x')) ∧
      (∀ a ∈ S, ∀ b ∈ S, G.graph.Reachable a b) ∧
      (S.Nonempty → Nat.card G.graph.edgeSet + 1 = S.card) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⟨⊥, fun _ _ => 0, fun _ _ => rfl, fun _ _ h => absurd h (by simp)⟩, ?_, ?_, ?_, ?_⟩
    · intro a b h; exact absurd h (by simp)
    · intro x hx; simp at hx
    · intro a ha; simp at ha
    · intro h; simp at h
  | insert z S hzS ih =>
    obtain ⟨G', hsupp, hG', hreach, hcard⟩ := ih
    by_cases hne : S = ∅
    · subst hne
      have hE : G'.graph.edgeSet = ∅ := by
        ext e; induction e using Sym2.ind with
        | h a b => simp only [SimpleGraph.mem_edgeSet, Set.mem_empty_iff_false, iff_false]
                   intro h; have := (hsupp a b h).1; simp at this
      refine ⟨G', fun a b h => by have := (hsupp a b h).1; simp at this, ?_, ?_, ?_⟩
      · intro x hx x' hx' hxx'
        simp at hx hx'; exact absurd (hx.trans hx'.symm) hxx'
      · intro a ha b hb; simp at ha hb; rw [ha, hb]
      · intro _; rw [hE]; simp
    obtain ⟨y, hy, hymax⟩ := Finset.exists_max_image S (fun b => v z b) (Finset.nonempty_iff_ne_empty.2 hne)
    have hzy : z ≠ y := fun h => hzS (h ▸ hy)
    have hc := hnonneg z y hzy
    obtain ⟨G, -, hGv⟩ := (⟨g71n_ext G' z y (v z y) hc, rfl, trivial⟩ : ∃ G, G = g71n_ext G' z y (v z y) hc ∧ True)
    have hle : G'.graph ≤ (g71n_ext G' z y (v z y) hc).graph := by
      intro a b h; rw [g71n_ext_adj G' z y (v z y) hc hzy]; exact Or.inl h
    have hzyA : (g71n_ext G' z y (v z y) hc).graph.Adj z y := by
      rw [g71n_ext_adj G' z y (v z y) hc hzy]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    refine ⟨g71n_ext G' z y (v z y) hc, ?_, ?_, ?_, ?_⟩
    · intro a b h
      rw [g71n_ext_adj G' z y (v z y) hc hzy] at h
      rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Finset.mem_insert_of_mem (hsupp a b h).1, Finset.mem_insert_of_mem (hsupp a b h).2⟩
      · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hy⟩
      · exact ⟨Finset.mem_insert_of_mem hy, Finset.mem_insert_self _ _⟩
    · have hzx : ∀ x ∈ S, IsMaxFlowValue (g71n_ext G' z y (v z y) hc) z x (v z x) := by
        intro x hx
        have hxz : x ≠ z := fun h => hzS (h ▸ hx)
        by_cases hxy : x = y
        · subst hxy; exact g71n_pend_y G' S hsupp z x hzS hy (v z x) hc
        · have h1 := g71n_pend G' S hsupp z y hzS hy (v z y) hc x hx hxy (v y x) (hG' y hy x hx (Ne.symm hxy))
          have heq : min (v z y) (v y x) = v z x := by
            apply le_antisymm
            · exact htri z x y hxz.symm hzy (Ne.symm hxy)
            · apply le_min (hymax x hx)
              have := htri y x z (Ne.symm hxy) hzy.symm hxz.symm
              rw [hsymm y z hzy.symm] at this
              have h2 : min (v z y) (v z x) = v z x := min_eq_right (hymax x hx)
              rw [h2] at this; exact this
          rw [heq] at h1; exact h1
      intro x hx x' hx' hxx'
      rcases Finset.mem_insert.1 hx with h1 | hxS
      · rcases Finset.mem_insert.1 hx' with h2 | hx'S
        · exact absurd (h1.trans h2.symm) hxx'
        · rw [h1]; exact hzx x' hx'S
      · rcases Finset.mem_insert.1 hx' with h2 | hx'S
        · rw [h2]
          have hxz : x ≠ z := fun h => hzS (h ▸ hxS)
          have := g71n_max_rev _ _ _ _ (hzx x hxS)
          rw [hsymm z x hxz.symm] at this; exact this
        · have hxz : x ≠ z := fun h => hzS (h ▸ hxS)
          have hxz' : x' ≠ z := fun h => hzS (h ▸ hx'S)
          exact (g71n_max_iff G' S hsupp z y hzS hy (v z y) hc x x' hxz hxz' _).2 (hG' x hxS x' hx'S hxx')
    · have hr : ∀ a ∈ insert z S, (g71n_ext G' z y (v z y) hc).graph.Reachable a y := by
        intro a ha
        rcases Finset.mem_insert.1 ha with h | h
        · rw [h]; exact hzyA.reachable
        · exact (hreach a h y hy).mono hle
      intro a ha b hb
      exact (hr a ha).trans (hr b hb).symm
    · intro _
      rw [g71n_edgeSet_ext G' z y (v z y) hc hzy, Finset.card_insert_of_notMem hzS,
        ← hcard (Finset.nonempty_iff_ne_empty.2 hne)]
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem]
      · rw [SimpleGraph.mem_edgeSet]; intro h; exact hzS (hsupp z y h).1

theorem g71n_tree {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
    (v : N → N → ℝ)
    (hsymm : ∀ x y : N, x ≠ y → v x y = v y x)
    (hnonneg : ∀ x y : N, x ≠ y → 0 ≤ v x y)
    (htri : ∀ x y z : N, x ≠ y → x ≠ z → z ≠ y → v x y ≥ min (v x z) (v z y)) :
    ∃ T : UNetwork N, T.graph.IsTree ∧ IsFlowFunction T v := by
  obtain ⟨G, -, hG, hR, hC⟩ := g71n_mainT v hsymm hnonneg htri Finset.univ
  refine ⟨G, ?_, fun x y hxy => hG x (Finset.mem_univ _) y (Finset.mem_univ _) hxy⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨⟨fun a b => hR a (Finset.mem_univ _) b (Finset.mem_univ _)⟩, ?_⟩
  rw [hC Finset.univ_nonempty, Finset.card_univ, Nat.card_eq_fintype_card]


open FlowsNetworks.MultiTerminal
/-- Ford–Fulkerson, *Flows in Networks*, Chapter IV, Theorem 2.1 (p. 8). Let `v` be a symmetric
function on pairs of distinct nodes of a nonempty finite node set `N`, with nonnegative values.
Then `v` is realizable as the flow function of an undirected network on `N` if and only if `v`
satisfies (2.1) `v(x, y) ≥ min [v(x, z), v(z, y)]` for all pairwise distinct `x, y, z`. If `v` is
realizable, it is realizable by a tree: by an undirected network whose arcs form a tree on `N`. -/
theorem solution {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
    (v : N → N → ℝ)
    (hsymm : ∀ x y : N, x ≠ y → v x y = v y x)
    (hnonneg : ∀ x y : N, x ≠ y → 0 ≤ v x y) :
    ((∃ G : UNetwork N, IsFlowFunction G v) ↔
        ∀ x y z : N, x ≠ y → x ≠ z → z ≠ y → v x y ≥ min (v x z) (v z y)) ∧
      ((∃ G : UNetwork N, IsFlowFunction G v) →
        ∃ T : UNetwork N, T.graph.IsTree ∧ IsFlowFunction T v) := by
  have back := g71n_tree v hsymm hnonneg
  have fwd : (∃ G : UNetwork N, IsFlowFunction G v) →
      ∀ x y z : N, x ≠ y → x ≠ z → z ≠ y → v x y ≥ min (v x z) (v z y) :=
    fun ⟨G, hG⟩ x y z h1 h2 h3 => g71n_tri G v hG x y z h1 h2 h3
  exact ⟨⟨fwd, fun h => (back h).imp fun T hT => hT.2⟩, fun h => back (fwd h)⟩


