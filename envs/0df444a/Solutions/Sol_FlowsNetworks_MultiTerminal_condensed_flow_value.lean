-- Prove2me | solution 1 for FlowsNetworks.MultiTerminal.condensed_flow_value
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:38:53.971909+00:00
-- url     : https://prove2.me/submissions/47bbb4ed-0492-420d-a0ca-7b6cefbd217d

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

section g70fn2E
open g70fn2_MF
theorem g70fn2_zero_flow {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (s t : N) :
    IsFlow G s t 0 0 := by
  refine ⟨fun _ _ _ => rfl, fun p _ => le_rfl, fun p hp => G.cap_nonneg p hp, ?_, ?_, ?_⟩ <;>
    simp [netFlowOut]
theorem g70fn2_exists_max {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (s t : N) :
    ∃ f v, IsFlow G s t f v ∧ ∀ g w, IsFlow G s t g w → w ≤ v := by
  set F : Set (N → N → ℝ) := {f | (∀ x y, (x, y) ∉ G.arcs → f x y = 0) ∧
    (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2) ∧ (∀ p ∈ G.arcs, f p.1 p.2 ≤ G.cap p.1 p.2) ∧
    netFlowOut G f t = -netFlowOut G f s ∧ ∀ x, x ≠ s → x ≠ t → netFlowOut G f x = 0} with hF
  have hmem : ∀ f v, IsFlow G s t f v → f ∈ F ∧ v = netFlowOut G f s := by
    rintro f v ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨h1, h2, h3, by rw [h4, h5], h6⟩, h4.symm⟩
  have hmem' : ∀ f ∈ F, IsFlow G s t f (netFlowOut G f s) := by
    rintro f ⟨h1, h2, h3, h5, h6⟩
    exact ⟨h1, h2, h3, rfl, h5, h6⟩
  have hcont : ∀ x, Continuous (fun f : N → N → ℝ => netFlowOut G f x) := by
    intro x; unfold netFlowOut; fun_prop
  have hev : ∀ x y, Continuous (fun f : N → N → ℝ => f x y) := by
    intro x y; fun_prop
  have hclosed : IsClosed F := by
    simp only [hF, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_eq (hev x y) continuous_const) (IsClosed.inter (isClosed_iInter fun p =>
      isClosed_iInter fun _ => isClosed_le continuous_const (hev _ _)) (IsClosed.inter
      (isClosed_iInter fun p => isClosed_iInter fun _ => isClosed_le (hev _ _) continuous_const)
      (IsClosed.inter (isClosed_eq (hcont t) (hcont s).neg) (isClosed_iInter fun x =>
        isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (hcont x) continuous_const))))
  set C := ∑ p ∈ G.arcs, G.cap p.1 p.2
  have hC : 0 ≤ C := Finset.sum_nonneg fun p hp => G.cap_nonneg p hp
  have hbdd : Bornology.IsBounded F := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨C, fun f hf => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hC]
    intro x
    rw [pi_norm_le_iff_of_nonneg hC]
    intro y
    rw [Real.norm_eq_abs]
    by_cases hxy : (x, y) ∈ G.arcs
    · have a := hf.2.1 _ hxy
      have b := hf.2.2.1 _ hxy
      have c : G.cap x y ≤ C := Finset.single_le_sum (f := fun p => G.cap p.1 p.2)
        (fun p hp => G.cap_nonneg p hp) hxy
      simp only at a b
      rw [abs_le]; constructor <;> linarith
    · rw [hf.1 x y hxy]; simpa using hC
  have hcpt : IsCompact F := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : F.Nonempty := ⟨0, (hmem 0 0 (g70fn2_zero_flow G s t)).1⟩
  obtain ⟨f0, hf0, hmax⟩ := hcpt.exists_isMaxOn hne (hcont s).continuousOn
  refine ⟨f0, _, hmem' f0 hf0, fun g w hg => ?_⟩
  obtain ⟨hgF, rfl⟩ := hmem g w hg
  exact hmax hgF


end g70fn2E

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


open FlowsNetworks.MultiTerminal

section g70fn2C
variable {M : Type} [Fintype M] [DecidableEq M]

noncomputable def g70fn2_cD (H : UNetwork M) (Z : Finset M) : ℝ :=
  g70fn2_MF.cutCapacity (g70fn2_D H) Z

open Classical in
theorem g70fn2_cD_eq (H : UNetwork M) (Z : Finset M) :
    g70fn2_cD H Z = ∑ a, ∑ b, if H.graph.Adj a b ∧ a ∈ Z ∧ b ∉ Z then H.cap a b else 0 := by
  unfold g70fn2_cD g70fn2_MF.cutCapacity g70fn2_MF.arcSum g70fn2_MF.arcsBetween
  rw [Finset.sum_filter, ← Fintype.sum_prod_type']
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : M × M => p ∈ (g70fn2_D H).arcs)]
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : M × M => ¬ p ∈ (g70fn2_D H).arcs),
      (if H.graph.Adj p.1 p.2 ∧ p.1 ∈ Z ∧ p.2 ∉ Z then H.cap p.1 p.2 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter, g70fn2_D_arcs] at hp
    simp [hp.2]
  rw [h1, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [g70fn2_D_arcs] at hp
  simp only [Finset.mem_compl, hp, true_and]
  rfl

theorem g70fn2_cD_compl (H : UNetwork M) (Z : Finset M) : g70fn2_cD H Zᶜ = g70fn2_cD H Z := by
  classical
  rw [g70fn2_cD_eq, g70fn2_cD_eq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.mem_compl, not_not]
  by_cases h : H.graph.Adj b a
  · have h' := H.graph.adj_symm h
    simp only [h, h', true_and, H.cap_symm b a]
    by_cases ha : a ∈ Z <;> by_cases hb : b ∈ Z <;> simp [ha, hb]
  · have h' : ¬ H.graph.Adj a b := fun h'' => h (H.graph.adj_symm h'')
    simp [h, h']

theorem g70fn2_cD_submod (H : UNetwork M) (A B : Finset M) :
    g70fn2_cD H (A ∪ B) + g70fn2_cD H (A ∩ B) ≤ g70fn2_cD H A + g70fn2_cD H B :=
  g70fn2_cut_submod (g70fn2_D H) A B

theorem g70fn2_cutCap_eq (H : UNetwork M) (Z : Finset M) : cutCap H Z = g70fn2_cD H Z := by
  classical
  rw [g70fn2_cD_eq]
  unfold cutCap
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Z)]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h0 : ∑ a ∈ Finset.univ.filter (fun a => a ∉ Z), ∑ b,
      (if H.graph.Adj a b ∧ a ∈ Z ∧ b ∉ Z then H.cap a b else 0) = 0 :=
    Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b _ => by
      rw [Finset.mem_filter] at ha; simp [ha.2]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Zᶜ)]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h1 : ∑ b ∈ Finset.univ.filter (fun b => b ∉ Zᶜ),
      (if H.graph.Adj a b ∧ a ∈ Z ∧ b ∉ Z then H.cap a b else 0) = 0 :=
    Finset.sum_eq_zero fun b hb => by
      rw [Finset.mem_filter, Finset.mem_compl, not_not] at hb; simp [hb.2]
  rw [h1, add_zero]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_compl] at hb
  simp only [ha, hb, not_false_eq_true, and_true]

theorem g70fn2_exists (H : UNetwork M) (a b : M) (hab : a ≠ b) :
    ∃ w, IsMaxFlowValue H a b w := by
  obtain ⟨f0, v0, hf0, hmax⟩ := g70fn2_exists_max (g70fn2_D H) a b
  obtain ⟨f', hf'⟩ := g70fn2_to_undir H a b f0 v0 hf0
  exact ⟨v0, ⟨f', hf'⟩, fun u ⟨g, hg⟩ => hmax g u (g70fn2_to_dir H a b g u hg)⟩

theorem g70fn2_A (H : UNetwork M) (a b : M) (hab : a ≠ b) (w : ℝ) :
    IsMaxFlowValue H a b w ↔
      IsLeast {c | ∃ Y : Finset M, a ∈ Y ∧ b ∉ Y ∧ c = g70fn2_cD H Y} w := by
  have fwd : ∀ w, IsMaxFlowValue H a b w →
      IsLeast {c | ∃ Y : Finset M, a ∈ Y ∧ b ∉ Y ∧ c = g70fn2_cD H Y} w := by
    intro w hw
    obtain ⟨Y, ha, hb, hc⟩ := g70fn2_mincut H a b hab w hw
    refine ⟨⟨Y, ha, hb, hc⟩, ?_⟩
    rintro c ⟨Z, hZa, hZb, rfl⟩
    obtain ⟨f, hf⟩ := hw.1
    exact g70fn2_weak H a b f w hf Z hZa hZb
  refine ⟨fwd w, fun hw => ?_⟩
  obtain ⟨w0, hw0⟩ := g70fn2_exists H a b hab
  have := (fwd w0 hw0).unique hw
  rw [← this]; exact hw0

end g70fn2C

theorem g70fn2_fiber {N : Type} [Fintype N] [DecidableEq N] (X : Finset N) (a : X) :
    Finset.univ.filter (fun n : N => (if h : n ∈ X then some ⟨n, h⟩ else none) = some a) =
      {a.val} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    split_ifs at h with hn
    · cases h; rfl
  · rintro rfl
    simp [a.2]

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : UNetwork N) (s t : N) (hst : s ≠ t) (X : Finset N) (hX : IsMinCut G s t X)
    (x y : N) (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) (w : ℝ) :
    IsMaxFlowValue (condense G X) (some ⟨x, hx⟩) (some ⟨y, hy⟩) w ↔
      IsMaxFlowValue G x y w := by
  classical
  let φ : N → Option X := fun n => if h : n ∈ X then some ⟨n, h⟩ else none
  have hφX : ∀ n (h : n ∈ X), φ n = some ⟨n, h⟩ := fun n h => by simp [φ, h]
  have hφn : ∀ n, n ∉ X → φ n = none := fun n h => by simp [φ, h]
  -- claim 1: condensed cut capacities are G cut capacities
  have claim1 : ∀ Y : Finset (Option X),
      g70fn2_cD (condense G X) Y = g70fn2_cD G (Finset.univ.filter (fun n => φ n ∈ Y)) := by
    intro Y
    rw [g70fn2_cD_eq, g70fn2_cD_eq]
    symm
    have hfib : ∀ (F : N → N → ℝ), ∑ a, ∑ b, F a b =
        ∑ u : Option X, ∑ v : Option X, ∑ a ∈ Finset.univ.filter (fun a => φ a = u),
          ∑ b ∈ Finset.univ.filter (fun b => φ b = v), F a b := by
      intro F
      calc ∑ a, ∑ b, F a b
          = ∑ a, ∑ v : Option X, ∑ b ∈ Finset.univ.filter (fun b => φ b = v), F a b :=
            Finset.sum_congr rfl fun a _ => (Finset.sum_fiberwise Finset.univ φ (F a)).symm
        _ = ∑ v : Option X, ∑ a, ∑ b ∈ Finset.univ.filter (fun b => φ b = v), F a b :=
            Finset.sum_comm
        _ = ∑ v : Option X, ∑ u : Option X, ∑ a ∈ Finset.univ.filter (fun a => φ a = u),
              ∑ b ∈ Finset.univ.filter (fun b => φ b = v), F a b :=
            Finset.sum_congr rfl fun v _ => (Finset.sum_fiberwise Finset.univ φ _).symm
        _ = _ := Finset.sum_comm
    rw [hfib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases hu : u ∈ Y
    · by_cases hv : v ∈ Y
      · -- both in Y: all terms zero
        rw [Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => by
          rw [Finset.mem_filter] at ha hb
          simp [Finset.mem_filter, ha.2, hb.2, hv]]
        simp [hv]
      · have huv : u ≠ v := fun h => hv (h ▸ hu)
        have e1 : ∀ a ∈ Finset.univ.filter (fun a => φ a = u), ∀ b ∈ Finset.univ.filter (fun b => φ b = v),
            (if G.graph.Adj a b ∧ a ∈ Finset.univ.filter (fun n => φ n ∈ Y) ∧
              b ∉ Finset.univ.filter (fun n => φ n ∈ Y) then G.cap a b else 0) =
            if G.graph.Adj a b then G.cap a b else 0 := by
          intro a ha b hb
          rw [Finset.mem_filter] at ha hb
          simp [ha.2, hb.2, hu, hv]
        rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => e1 a ha b hb]
        simp only [hu, hv, not_false_eq_true, and_true, true_and]
        rcases u with _ | a' <;> rcases v with _ | b'
        · exact absurd rfl huv
        · -- none, some b'
          rw [g70fn2_fiber]
          simp only [Finset.sum_singleton]
          have : Finset.univ.filter (fun a => φ a = none) = Xᶜ := by
            ext n; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
            constructor
            · intro h hn; rw [hφX n hn] at h; cases h
            · exact hφn n
          rw [this]
          show _ = if condensedAdj G X none (some b') then capToComplement G X b' else 0
          unfold capToComplement condensedAdj
          split_ifs with hadj
          · refine Finset.sum_congr rfl fun a _ => ?_
            by_cases h : G.graph.Adj a b'
            · simp [h, G.graph.adj_symm h, G.cap_symm a b']
            · have h' : ¬ G.graph.Adj b' a := fun h'' => h (G.graph.adj_symm h'')
              simp [h, h']
          · push_neg at hadj
            refine Finset.sum_eq_zero fun a ha => ?_
            rw [Finset.mem_compl] at ha
            have : ¬ G.graph.Adj a b' := fun h => hadj a ha (G.graph.adj_symm h)
            simp [this]
        · -- some a', none
          rw [g70fn2_fiber]
          simp only [Finset.sum_singleton]
          have : Finset.univ.filter (fun b => φ b = none) = Xᶜ := by
            ext n; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
            constructor
            · intro h hn; rw [hφX n hn] at h; cases h
            · exact hφn n
          rw [this]
          show _ = if condensedAdj G X (some a') none then capToComplement G X a' else 0
          unfold capToComplement condensedAdj
          split_ifs with hadj
          · refine Finset.sum_congr rfl fun b _ => ?_
            congr 1
          · push_neg at hadj
            refine Finset.sum_eq_zero fun b hb => ?_
            rw [Finset.mem_compl] at hb
            simp [hadj b hb]
        · -- some, some
          rw [g70fn2_fiber, g70fn2_fiber]
          simp only [Finset.sum_singleton]
          show _ = if condensedAdj G X (some a') (some b') then condensedCap G X (some a') (some b') else 0
          unfold condensedAdj condensedCap
          congr 1
    · rw [Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => by
          rw [Finset.mem_filter] at ha hb
          simp [Finset.mem_filter, ha.2, hu]]
      simp [hu]
  -- sets
  set SC := {c | ∃ Y : Finset (Option X), some ⟨x, hx⟩ ∈ Y ∧ some ⟨y, hy⟩ ∉ Y ∧
    c = g70fn2_cD (condense G X) Y}
  set SG := {c | ∃ Y : Finset N, x ∈ Y ∧ y ∉ Y ∧ c = g70fn2_cD G Y}
  have hsub : SC ⊆ SG := by
    rintro c ⟨Y, h1, h2, rfl⟩
    refine ⟨_, ?_, ?_, claim1 Y⟩
    · simp [hφX x hx, h1]
    · simp [hφX y hy, h2]
  -- least element of SG lies in SC
  obtain ⟨m, hm⟩ : ∃ m, IsLeast SG m := by
    obtain ⟨w0, hw0⟩ := g70fn2_exists G x y hxy
    exact ⟨w0, (g70fn2_A G x y hxy w0).1 hw0⟩
  have hpre : ∀ Z : Finset N, (Z ⊆ X ∨ Xᶜ ⊆ Z) →
      Finset.univ.filter (fun n => φ n ∈ Z.image φ) = Z := by
    intro Z hZ
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨n', hn', he⟩
      by_cases hn : n ∈ X
      · by_cases hn2 : n' ∈ X
        · rw [hφX n hn, hφX n' hn2] at he
          cases he; exact hn'
        · rw [hφX n hn, hφn n' hn2] at he; cases he
      · rcases hZ with hZ | hZ
        · have hn2 : n' ∉ X := by
            intro hn2; rw [hφX n' hn2, hφn n hn] at he; cases he
          exact absurd (hZ hn') hn2
        · exact hZ (Finset.mem_compl.2 hn)
    · intro h; exact ⟨n, h, rfl⟩
  have hmSC : m ∈ SC := by
    obtain ⟨⟨Y, hxY, hyY, hmY⟩, hmin⟩ := hm
    obtain ⟨hsX, htX, hXmin⟩ := hX
    have hXm : ∀ Z : Finset N, s ∈ Z → t ∉ Z → g70fn2_cD G X ≤ g70fn2_cD G Z := by
      intro Z h1 h2; rw [← g70fn2_cutCap_eq, ← g70fn2_cutCap_eq]; exact hXmin Z h1 h2
    obtain ⟨Z, hZ, hxZ, hyZ, hcZ⟩ : ∃ Z : Finset N, (Z ⊆ X ∨ Xᶜ ⊆ Z) ∧ x ∈ Z ∧ y ∉ Z ∧
        g70fn2_cD G Z ≤ m := by
      by_cases htY : t ∈ Y
      · refine ⟨(X ∩ Yᶜ)ᶜ, Or.inr ?_, ?_, ?_, ?_⟩
        · exact Finset.compl_subset_compl.2 Finset.inter_subset_left
        · simp [hxY]
        · simp [hy, hyY]
        · rw [g70fn2_cD_compl]
          have h1 := g70fn2_cD_submod G X Yᶜ
          have h2 := hXm (X ∪ Yᶜ) (Finset.mem_union_left _ hsX) (by simp [htX, htY])
          have h3 := g70fn2_cD_compl G Y
          linarith
      · refine ⟨X ∩ Y, Or.inl Finset.inter_subset_left, ?_, ?_, ?_⟩
        · simp [hx, hxY]
        · simp [hyY]
        · have h1 := g70fn2_cD_submod G X Y
          have h2 := hXm (X ∪ Y) (Finset.mem_union_left _ hsX) (by simp [htX, htY])
          linarith
    have hZm : g70fn2_cD G Z = m := le_antisymm hcZ (hmin ⟨Z, hxZ, hyZ, rfl⟩)
    refine ⟨Z.image φ, ?_, ?_, ?_⟩
    · rw [← hφX x hx]; exact Finset.mem_image_of_mem φ hxZ
    · rw [← hφX y hy]
      intro hmem
      have : y ∈ Finset.univ.filter (fun n => φ n ∈ Z.image φ) := by simpa using hmem
      rw [hpre Z hZ] at this
      exact hyZ this
    · rw [claim1, hpre Z hZ, hZm]
  rw [g70fn2_A (condense G X) _ _ (by simpa using hxy) w, g70fn2_A G x y hxy w]
  constructor
  · intro hw
    have hwm : w = m := le_antisymm (hw.2 hmSC) (hm.2 (hsub hw.1))
    rw [hwm]; exact hm
  · intro hw
    have hwm : w = m := hw.unique hm
    rw [hwm]
    exact ⟨hmSC, fun c hc => hm.2 (hsub hc)⟩
