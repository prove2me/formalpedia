-- Prove2me | solution 1 for FlowsNetworks.TwoArcs.corollary_13_2_sign_of_p
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:24:51.403089+00:00
-- url     : https://prove2.me/submissions/ee4601bc-ab59-49ac-a34e-58fb5624f53a

import Mathlib
import Definitions.Def_FlowsNetworks_TwoArcs_Network
import Definitions.Def_FlowsNetworks_TwoArcs_TwoArcValue
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

section g70fn2T
open g70fn2_MF
variable {N : Type} [Fintype N] [DecidableEq N]

/-- multi-terminal flows on an MF network -/
def g70fn2_MS (G : Network N) (S T : Finset N) (g : N → N → ℝ) : Prop :=
  SupportedOnArcs G g ∧ (∀ p ∈ G.arcs, 0 ≤ g p.1 p.2) ∧ (∀ p ∈ G.arcs, g p.1 p.2 ≤ G.cap p.1 p.2) ∧
    ∀ x, x ∉ S → x ∉ T → netFlowOut G g x = 0

def g70fn2_val (G : Network N) (S : Finset N) (g : N → N → ℝ) : ℝ := ∑ x ∈ S, netFlowOut G g x

theorem g70fn2_ms_cut (G : Network N) (S T : Finset N) (g : N → N → ℝ) (hg : g70fn2_MS G S T g)
    (X : Finset N) (hS : S ⊆ X) (hT : Disjoint X T) :
    g70fn2_val G S g = arcSum G g X Xᶜ - arcSum G g Xᶜ X := by
  rw [← g70fn2_sum_netFlowOut, g70fn2_val, ← Finset.sum_sdiff hS]
  have : ∑ x ∈ X \ S, netFlowOut G g x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_sdiff] at hx
    exact hg.2.2.2 x hx.2 (Finset.disjoint_left.1 hT hx.1)
  rw [this, zero_add]

theorem g70fn2_ms_weak (G : Network N) (S T : Finset N) (g : N → N → ℝ) (hg : g70fn2_MS G S T g)
    (X : Finset N) (hS : S ⊆ X) (hT : Disjoint X T) :
    g70fn2_val G S g ≤ cutCapacity G X := by
  rw [g70fn2_ms_cut G S T g hg X hS hT]
  have e1 : arcSum G g X Xᶜ ≤ cutCapacity G X := Finset.sum_le_sum fun p hp =>
      hg.2.2.1 p (Finset.mem_filter.1 hp).1
  have e2 : 0 ≤ arcSum G g Xᶜ X := Finset.sum_nonneg fun p hp => hg.2.1 p (Finset.mem_filter.1 hp).1
  linarith

theorem g70fn2_ms_exists (G : Network N) (S T : Finset N) :
    ∃ g, g70fn2_MS G S T g ∧ ∀ g', g70fn2_MS G S T g' → g70fn2_val G S g' ≤ g70fn2_val G S g := by
  set F : Set (N → N → ℝ) := {g | g70fn2_MS G S T g} with hF
  have hcont : ∀ x, Continuous (fun f : N → N → ℝ => netFlowOut G f x) := by
    intro x; unfold netFlowOut; fun_prop
  have hev : ∀ x y, Continuous (fun f : N → N → ℝ => f x y) := by
    intro x y; fun_prop
  have hvc : Continuous (fun f : N → N → ℝ => g70fn2_val G S f) := by
    unfold g70fn2_val; exact continuous_finsetSum _ fun x _ => hcont x
  have hclosed : IsClosed F := by
    simp only [hF, g70fn2_MS, SupportedOnArcs, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_eq (hev x y) continuous_const) (IsClosed.inter (isClosed_iInter fun p =>
      isClosed_iInter fun _ => isClosed_le continuous_const (hev _ _)) (IsClosed.inter
      (isClosed_iInter fun p => isClosed_iInter fun _ => isClosed_le (hev _ _) continuous_const)
      (isClosed_iInter fun x =>
        isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (hcont x) continuous_const)))
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
  have hne : F.Nonempty := ⟨0, fun _ _ _ => rfl, fun p _ => le_rfl,
    fun p hp => G.cap_nonneg p hp, fun x _ _ => by simp [netFlowOut]⟩
  obtain ⟨f0, hf0, hmax⟩ := hcpt.exists_isMaxOn hne hvc.continuousOn
  exact ⟨f0, hf0, fun g hg => hmax hg⟩

theorem g70fn2_ms_mfmc (G : Network N) (S T : Finset N) (hST : Disjoint S T) :
    ∃ g X, g70fn2_MS G S T g ∧ S ⊆ X ∧ Disjoint X T ∧ g70fn2_val G S g = cutCapacity G X := by
  classical
  obtain ⟨g, hg, hmax⟩ := g70fn2_ms_exists G S T
  let Y : Finset N := Finset.univ.filter (fun n => ∃ s ∈ S, Relation.ReflTransGen (AugStep G g) s n)
  have hSY : S ⊆ Y := fun s hs => by
    simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨s, hs, Relation.ReflTransGen.refl⟩
  have hcl : ∀ u w, u ∈ Y → AugStep G g u w → w ∈ Y := by
    intro u w hu huw
    simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨s, hs, hr⟩ := hu
    exact ⟨s, hs, hr.tail huw⟩
  have hYT : Disjoint Y T := by
    rw [Finset.disjoint_left]
    intro t htY htT
    simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at htY
    obtain ⟨s, hs, hr⟩ := htY
    obtain ⟨l, hl⟩ := g70fn2_simple hr
    obtain ⟨ε, hε, hl'⟩ := g70fn2_res_exists G g s hl
    obtain ⟨h, -, hhs, hhf, hhn, -⟩ := g70fn2_augment G g s hg.2.1 hg.2.2.1 ε hε hl'
    have hst : s ≠ t := fun e => Finset.disjoint_left.1 hST hs (e ▸ htT)
    have hnew : g70fn2_MS G S T (g + h) := by
      refine ⟨fun a b hab => by simp [hg.1 a b hab, hhs a b hab], fun p hp => (hhf p hp).1,
        fun p hp => (hhf p hp).2, fun x hxS hxT => ?_⟩
      rw [g70fn2_netFlowOut_add, hg.2.2.2 x hxS hxT, hhn]
      have h1 : x ≠ s := fun e => hxS (e ▸ hs)
      have h2 : x ≠ t := fun e => hxT (e ▸ htT)
      simp [h1, h2]
    have := hmax _ hnew
    unfold g70fn2_val at this
    simp only [g70fn2_netFlowOut_add, hhn, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', hs, if_true] at this
    have htS : t ∉ S := fun h => Finset.disjoint_left.1 hST h htT
    simp only [htS, if_false] at this
    linarith
  refine ⟨g, Y, hg, hSY, hYT, ?_⟩
  rw [g70fn2_ms_cut G S T g hg Y hSY hYT]
  have a1 : arcSum G g Y Yᶜ = cutCapacity G Y := by
    unfold cutCapacity arcSum
    apply Finset.sum_congr rfl
    intro p hp
    simp only [arcsBetween, Finset.mem_filter, Finset.mem_compl] at hp
    by_contra hne
    have : g p.1 p.2 < G.cap p.1 p.2 := lt_of_le_of_ne (hg.2.2.1 p hp.1) hne
    exact hp.2.2 (hcl p.1 p.2 hp.2.1 (Or.inl ⟨hp.1, this⟩))
  have a2 : arcSum G g Yᶜ Y = 0 := by
    unfold arcSum
    apply Finset.sum_eq_zero
    intro p hp
    simp only [arcsBetween, Finset.mem_filter, Finset.mem_compl] at hp
    by_contra hne
    have : 0 < g p.1 p.2 := lt_of_le_of_ne (hg.2.1 p hp.1) (Ne.symm hne)
    exact hp.2.1 (hcl p.2 p.1 hp.2.2 (Or.inr ⟨hp.1, this⟩))
  rw [a1, a2, sub_zero]

end g70fn2T

section g70fn2G
open FlowsNetworks.TwoArcs
open scoped ENNReal NNReal
variable {N : Type} [Fintype N] [DecidableEq N]

def g70fn2_G' (G : Network N) (c : N × N → ℝ≥0) : g70fn2_MF.Network N :=
  ⟨G.arcs, G.no_loops, fun a b => (c (a, b) : ℝ), fun _ _ => NNReal.coe_nonneg _⟩

theorem g70fn2_sum1 (A : Finset (N × N)) (f : N × N → ℝ) (hf : ∀ a, a ∉ A → f a = 0) (x : N) :
    ∑ p ∈ A.filter (fun p => p.1 = x), f p = ∑ y, f (x, y) := by
  have e : ∑ y, f (x, y) = ∑ p ∈ Finset.univ.filter (fun p : N × N => p.1 = x), f p := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    symm
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [e]
  apply Finset.sum_subset
  · intro p hp; simp only [Finset.mem_filter] at hp ⊢; exact ⟨Finset.mem_univ _, hp.2⟩
  · intro p hp hpn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hpn
    exact hf p (fun h => hpn ⟨h, hp⟩)

theorem g70fn2_sum2 (A : Finset (N × N)) (f : N × N → ℝ) (hf : ∀ a, a ∉ A → f a = 0) (x : N) :
    ∑ p ∈ A.filter (fun p => p.2 = x), f p = ∑ y, f (y, x) := by
  have e : ∑ y, f (y, x) = ∑ p ∈ Finset.univ.filter (fun p : N × N => p.2 = x), f p := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [Finset.sum_ite_eq']
  rw [e]
  apply Finset.sum_subset
  · intro p hp; simp only [Finset.mem_filter] at hp ⊢; exact ⟨Finset.mem_univ _, hp.2⟩
  · intro p hp hpn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hpn
    exact hf p (fun h => hpn ⟨h, hp⟩)

theorem g70fn2_net_eq (G : Network N) (c : N × N → ℝ≥0) (f : N × N → ℝ)
    (hf : ∀ a, a ∉ G.arcs → f a = 0) (x : N) :
    outflow f x - inflow f x = g70fn2_MF.netFlowOut (g70fn2_G' G c) (fun a b => f (a, b)) x := by
  unfold g70fn2_MF.netFlowOut outflow inflow
  simp only [g70fn2_G']
  rw [g70fn2_sum1 G.arcs f hf, g70fn2_sum2 G.arcs f hf]

theorem g70fn2_toMS (G : Network N) (c : N × N → ℝ≥0) (f : N × N → ℝ)
    (hf : IsFlow G (fun a => (c a : ℝ≥0∞)) f) :
    g70fn2_MS (g70fn2_G' G c) G.sources G.sinks (fun a b => f (a, b)) ∧
      g70fn2_val (g70fn2_G' G c) G.sources (fun a b => f (a, b)) = flowValue G f := by
  obtain ⟨h0, hb, hc⟩ := hf
  refine ⟨⟨fun a b hab => h0 _ hab, fun p hp => (hb p hp).1, fun p hp => ?_,
    fun x hxS hxT => ?_⟩, ?_⟩
  · have := (hb p hp).2
    rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top] at this
    simpa [g70fn2_G'] using this
  · rw [← g70fn2_net_eq G c f h0]; exact hc x hxS hxT
  · unfold g70fn2_val flowValue
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => (g70fn2_net_eq G c f h0 x).symm

theorem g70fn2_ofMS (G : Network N) (c : N × N → ℝ≥0) (g : N → N → ℝ)
    (hg : g70fn2_MS (g70fn2_G' G c) G.sources G.sinks g) :
    IsFlow G (fun a => (c a : ℝ≥0∞)) (fun a => g a.1 a.2) ∧
      flowValue G (fun a => g a.1 a.2) = g70fn2_val (g70fn2_G' G c) G.sources g := by
  obtain ⟨h0, hn, hc, hcons⟩ := hg
  have h0' : ∀ a, a ∉ G.arcs → (fun a : N × N => g a.1 a.2) a = 0 := fun a ha => h0 a.1 a.2 ha
  refine ⟨⟨h0', fun a ha => ⟨hn a ha, ?_⟩, fun x hxS hxT => ?_⟩, ?_⟩
  · apply ENNReal.ofReal_le_of_le_toReal
    simpa [g70fn2_G'] using hc a ha
  · rw [g70fn2_net_eq G c _ h0']; exact hcons x hxS hxT
  · unfold g70fn2_val flowValue
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => g70fn2_net_eq G c _ h0' x

theorem g70fn2_tcut_eq (G : Network N) (c : N × N → ℝ≥0) (X : Finset N) :
    cutCapacity G (fun a => (c a : ℝ≥0∞)) X =
      ENNReal.ofReal (g70fn2_MF.cutCapacity (g70fn2_G' G c) X) := by
  unfold cutCapacity g70fn2_MF.cutCapacity g70fn2_MF.arcSum g70fn2_MF.arcsBetween
  simp only [g70fn2_G', Finset.mem_compl]
  rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => NNReal.coe_nonneg _)]
  simp only [ENNReal.ofReal_coe_nnreal]

theorem g70fn2_fin (G : Network N) (c : N × N → ℝ≥0) :
    IsLeast {r : ℝ≥0∞ | ∃ X : Finset N, IsSeparating G X ∧
        r = cutCapacity G (fun a => (c a : ℝ≥0∞)) X}
      (maxFlowValue G (fun a => (c a : ℝ≥0∞))) := by
  obtain ⟨g, Y, hg, hSY, hYT, hval⟩ :=
    g70fn2_ms_mfmc (g70fn2_G' G c) G.sources G.sinks G.sources_sinks_disjoint
  have hmax : maxFlowValue G (fun a => (c a : ℝ≥0∞)) =
      ENNReal.ofReal (g70fn2_val (g70fn2_G' G c) G.sources g) := by
    apply le_antisymm
    · apply iSup₂_le
      intro f hf
      obtain ⟨h1, h2⟩ := g70fn2_toMS G c f hf
      rw [← h2]
      apply ENNReal.ofReal_le_ofReal
      rw [hval]
      exact g70fn2_ms_weak _ _ _ _ h1 Y hSY hYT
    · obtain ⟨h1, h2⟩ := g70fn2_ofMS G c g hg
      exact le_iSup₂_of_le (fun a => g a.1 a.2) h1 (le_of_eq (by rw [h2]))
  refine ⟨⟨Y, ⟨hSY, hYT⟩, by rw [hmax, g70fn2_tcut_eq, hval]⟩, ?_⟩
  rintro r ⟨X, ⟨hS, hT⟩, rfl⟩
  rw [hmax, g70fn2_tcut_eq]
  exact ENNReal.ofReal_le_ofReal (g70fn2_ms_weak _ _ _ _ hg X hS hT)

end g70fn2G

section g70fn2Gen
open FlowsNetworks.TwoArcs
open scoped ENNReal NNReal
variable {N : Type} [Fintype N] [DecidableEq N]

theorem g70fn2_mono (G : Network N) (c c' : N × N → ℝ≥0∞) (h : ∀ a, c a ≤ c' a) :
    maxFlowValue G c ≤ maxFlowValue G c' := by
  apply iSup₂_le
  intro f hf
  exact le_iSup₂_of_le f ⟨hf.1, fun a ha => ⟨(hf.2.1 a ha).1, (hf.2.1 a ha).2.trans (h a)⟩, hf.2.2⟩
    le_rfl

theorem g70fn2_gen (G : Network N) (c : N × N → ℝ≥0∞) :
    (∀ X, IsSeparating G X → maxFlowValue G c ≤ cutCapacity G c X) ∧
      ∃ X, IsSeparating G X ∧ maxFlowValue G c = cutCapacity G c X := by
  classical
  have weak : ∀ X, IsSeparating G X → maxFlowValue G c ≤ cutCapacity G c X := by
    intro X hX
    apply iSup₂_le
    intro f hf
    let cf : N × N → ℝ≥0 := fun a => Real.toNNReal (f a)
    have hf' : IsFlow G (fun a => (cf a : ℝ≥0∞)) f :=
      ⟨hf.1, fun a ha => ⟨(hf.2.1 a ha).1, le_rfl⟩, hf.2.2⟩
    have h1 : ENNReal.ofReal (flowValue G f) ≤ maxFlowValue G (fun a => (cf a : ℝ≥0∞)) :=
      le_iSup₂_of_le f hf' le_rfl
    refine h1.trans ((g70fn2_fin G cf).2 ⟨X, hX, rfl⟩ |>.trans ?_)
    unfold cutCapacity
    refine Finset.sum_le_sum fun a ha => ?_
    exact (hf.2.1 a (Finset.mem_filter.1 ha).1).2
  refine ⟨weak, ?_⟩
  let cuts : Finset (Finset N) := Finset.univ.filter (fun X => IsSeparating G X)
  have hne : cuts.Nonempty := ⟨G.sources, Finset.mem_filter.2 ⟨Finset.mem_univ _,
    ⟨subset_refl _, G.sources_sinks_disjoint⟩⟩⟩
  obtain ⟨X, hX, hmin⟩ := Finset.exists_min_image cuts (cutCapacity G c) hne
  have hXs : IsSeparating G X := (Finset.mem_filter.1 hX).2
  refine ⟨X, hXs, le_antisymm (weak X hXs) ?_⟩
  -- truncation
  have key : ∀ K : ℝ≥0, min (cutCapacity G c X) K ≤ maxFlowValue G c := by
    intro K
    let cK : N × N → ℝ≥0 := fun a => if c a = ⊤ then K else (c a).toNNReal
    have hle : ∀ a, (cK a : ℝ≥0∞) ≤ c a := by
      intro a; simp only [cK]; split_ifs with h
      · rw [h]; exact le_top
      · rw [ENNReal.coe_toNNReal h]
    obtain ⟨⟨Y, hY, hYe⟩, -⟩ := g70fn2_fin G cK
    refine le_trans ?_ ((le_of_eq hYe.symm).trans (g70fn2_mono G _ _ hle))
    have hYc : cutCapacity G c X ≤ cutCapacity G c Y :=
      hmin Y (Finset.mem_filter.2 ⟨Finset.mem_univ _, hY⟩)
    unfold cutCapacity at hYc ⊢
    by_cases htop : ∃ a ∈ G.arcs.filter (fun a => a.1 ∈ Y ∧ a.2 ∉ Y), c a = ⊤
    · obtain ⟨a, ha, hca⟩ := htop
      refine (min_le_right _ _).trans ?_
      have : (K : ℝ≥0∞) = (cK a : ℝ≥0∞) := by simp [cK, hca]
      rw [this]
      exact Finset.single_le_sum (f := fun a => (cK a : ℝ≥0∞)) (fun _ _ => bot_le) ha
    · push_neg at htop
      refine (min_le_left _ _).trans (hYc.trans (le_of_eq ?_))
      refine Finset.sum_congr rfl fun a ha => ?_
      simp [cK, htop a ha, ENNReal.coe_toNNReal (htop a ha)]
  by_cases hm : cutCapacity G c X = ⊤
  · rw [hm]
    rw [top_le_iff]
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    have := key r
    rwa [hm, min_eq_right le_top] at this
  · have := key (cutCapacity G c X).toNNReal
    rwa [ENNReal.coe_toNNReal hm, min_self] at this

theorem g70fn2_split (s : Finset (N × N)) (g : N × N → ℝ≥0∞) (A : N × N) :
    ∑ a ∈ s, g a = (if A ∈ s then g A else 0) + ∑ a ∈ s.erase A, g a := by
  split_ifs with h
  · rw [Finset.add_sum_erase s g h]
  · rw [Finset.erase_eq_of_notMem h, zero_add]

theorem g70fn2_ite_le (p : Prop) [Decidable p] (x : ℝ≥0∞) : (if p then x else 0) ≤ x := by
  split_ifs <;> simp

end g70fn2Gen

section g70fn2Two
open FlowsNetworks.TwoArcs
open scoped ENNReal NNReal
variable {N : Type} [Fintype N] [DecidableEq N]

noncomputable def g70fn2_B2 (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N) (X : Finset N) :
    ℝ≥0∞ :=
  ∑ a ∈ ((G.arcs.filter (fun a => a.1 ∈ X ∧ a.2 ∉ X)).erase Ai).erase Aj, (c a : ℝ≥0∞)

theorem g70fn2_capTwo_cut (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N)
    (hAi : Ai ∈ G.arcs) (hAj : Aj ∈ G.arcs) (hij : Ai ≠ Aj) (ξ η : ℝ≥0∞) (X : Finset N) :
    cutCapacity G (capTwo c Ai Aj ξ η) X =
      g70fn2_B2 G c Ai Aj X + (if Ai.1 ∈ X ∧ Ai.2 ∉ X then ξ else 0) +
        (if Aj.1 ∈ X ∧ Aj.2 ∉ X then η else 0) := by
  unfold cutCapacity g70fn2_B2
  rw [g70fn2_split _ _ Ai, g70fn2_split _ _ Aj]
  have e1 : Ai ∈ G.arcs.filter (fun a => a.1 ∈ X ∧ a.2 ∉ X) ↔ (Ai.1 ∈ X ∧ Ai.2 ∉ X) := by
    simp [hAi]
  have e2 : Aj ∈ (G.arcs.filter (fun a => a.1 ∈ X ∧ a.2 ∉ X)).erase Ai ↔
      (Aj.1 ∈ X ∧ Aj.2 ∉ X) := by
    simp [hAj, Ne.symm hij]
  have e3 : ∑ a ∈ ((G.arcs.filter (fun a => a.1 ∈ X ∧ a.2 ∉ X)).erase Ai).erase Aj,
      capTwo c Ai Aj ξ η a =
      ∑ a ∈ ((G.arcs.filter (fun a => a.1 ∈ X ∧ a.2 ∉ X)).erase Ai).erase Aj, (c a : ℝ≥0∞) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have h1 := Finset.ne_of_mem_erase ha
    have h2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ha)
    simp [capTwo, h1, h2]
  rw [e3]
  simp only [e1, e2]
  have hA : capTwo c Ai Aj ξ η Ai = ξ := by simp [capTwo]
  have hB : capTwo c Ai Aj ξ η Aj = η := by simp [capTwo, Ne.symm hij]
  rw [hA, hB]
  split_ifs <;> (try simp only [add_zero, zero_add]) <;> (try ring)

theorem g70fn2_134 {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N)
    (hAi : Ai ∈ G.arcs) (hAj : Aj ∈ G.arcs) (hij : Ai ≠ Aj) (ξ η : ℝ≥0∞) :
    vbarTwo G c Ai Aj ξ η =
      min (min (min (vbarTwo G c Ai Aj 0 0 + ξ + η) (vbarTwo G c Ai Aj 0 ⊤ + ξ))
        (vbarTwo G c Ai Aj ⊤ 0 + η)) (vbarTwo G c Ai Aj ⊤ ⊤) := by
  classical
  have H := fun ξ η => g70fn2_gen G (capTwo c Ai Aj ξ η)
  have hcut := g70fn2_capTwo_cut G c Ai Aj hAi hAj hij
  unfold vbarTwo
  set F := fun ξ η => maxFlowValue G (capTwo c Ai Aj ξ η) with hF
  change F ξ η = min (min (min (F 0 0 + ξ + η) (F 0 ⊤ + ξ)) (F ⊤ 0 + η)) (F ⊤ ⊤)
  apply le_antisymm
  · refine le_min (le_min (le_min ?_ ?_) ?_) ?_
    · obtain ⟨X, hX, hXe⟩ := (H 0 0).2
      have h1 := (H ξ η).1 X hX
      change F 0 0 = _ at hXe
      change F ξ η ≤ _ at h1
      rw [hXe, hcut]; rw [hcut] at h1
      refine h1.trans ?_
      simp only [ite_self, add_zero]
      gcongr <;> exact g70fn2_ite_le _ _
    · obtain ⟨X, hX, hXe⟩ := (H 0 ⊤).2
      have h1 := (H ξ η).1 X hX
      change F 0 ⊤ = _ at hXe
      change F ξ η ≤ _ at h1
      rw [hXe, hcut]; rw [hcut] at h1
      refine h1.trans ?_
      by_cases hj : Aj.1 ∈ X ∧ Aj.2 ∉ X
      · simp [hj]
      · simp only [hj, if_false, ite_self, add_zero]
        gcongr; exact g70fn2_ite_le _ _
    · obtain ⟨X, hX, hXe⟩ := (H ⊤ 0).2
      have h1 := (H ξ η).1 X hX
      change F ⊤ 0 = _ at hXe
      change F ξ η ≤ _ at h1
      rw [hXe, hcut]; rw [hcut] at h1
      refine h1.trans ?_
      by_cases hi : Ai.1 ∈ X ∧ Ai.2 ∉ X
      · simp [hi]
      · simp only [hi, if_false, ite_self, add_zero]
        gcongr; exact g70fn2_ite_le _ _
    · obtain ⟨X, hX, hXe⟩ := (H ⊤ ⊤).2
      have h1 := (H ξ η).1 X hX
      change F ⊤ ⊤ = _ at hXe
      change F ξ η ≤ _ at h1
      rw [hXe, hcut]; rw [hcut] at h1
      refine h1.trans ?_
      by_cases hi : Ai.1 ∈ X ∧ Ai.2 ∉ X
      · simp [hi]
      · by_cases hj : Aj.1 ∈ X ∧ Aj.2 ∉ X
        · simp [hj]
        · simp [hi, hj]
  · obtain ⟨X, hX, hXe⟩ := (H ξ η).2
    change F ξ η = _ at hXe
    rw [hXe, hcut]
    by_cases hi : Ai.1 ∈ X ∧ Ai.2 ∉ X <;> by_cases hj : Aj.1 ∈ X ∧ Aj.2 ∉ X
    · refine min_le_of_left_le (min_le_of_left_le (min_le_of_left_le ?_))
      have := (H 0 0).1 X hX
      change F 0 0 ≤ _ at this
      rw [hcut, if_pos hi, if_pos hj] at this
      rw [if_pos hi, if_pos hj]
      rw [add_zero, add_zero] at this
      try simp only [add_zero]
      gcongr
    · refine min_le_of_left_le (min_le_of_left_le (min_le_of_right_le ?_))
      have := (H 0 ⊤).1 X hX
      change F 0 ⊤ ≤ _ at this
      rw [hcut, if_pos hi, if_neg hj] at this
      rw [if_pos hi, if_neg hj]
      rw [add_zero, add_zero] at this
      try simp only [add_zero]
      gcongr
    · refine min_le_of_left_le (min_le_of_right_le ?_)
      have := (H ⊤ 0).1 X hX
      change F ⊤ 0 ≤ _ at this
      rw [hcut, if_neg hi, if_pos hj] at this
      rw [if_neg hi, if_pos hj]
      rw [add_zero, add_zero] at this
      try simp only [add_zero]
      gcongr
    · refine min_le_of_right_le ?_
      have := (H ⊤ ⊤).1 X hX
      change F ⊤ ⊤ ≤ _ at this
      rw [hcut, if_neg hi, if_neg hj] at this
      rw [if_neg hi, if_neg hj]
      simpa using this

end g70fn2Two

section g70fn2Sign
open FlowsNetworks.TwoArcs
open scoped ENNReal NNReal

theorem g70fn2_super {α : Type} (sep : α → Prop) (Di Dj : α → Prop) [DecidablePred Di]
    [DecidablePred Dj] (b : α → ℝ) (f : ℝ → ℝ → ℝ)
    (hle : ∀ ξ η, 0 ≤ ξ → 0 ≤ η → ∀ X, sep X →
      f ξ η ≤ b X + (if Di X then ξ else 0) + (if Dj X then η else 0))
    (hex : ∀ ξ η, 0 ≤ ξ → 0 ≤ η → ∃ X, sep X ∧
      f ξ η = b X + (if Di X then ξ else 0) + (if Dj X then η else 0))
    (H : ∀ X Y, sep X → sep Y → ¬ Di X → ¬ Dj X → Di Y → Dj Y → ∃ R S, sep R ∧ sep S ∧
      ¬ Di R ∧ Dj R ∧ Di S ∧ ¬ Dj S ∧ b R + b S ≤ b X + b Y)
    (ξ ξ' η η' : ℝ) (h0 : 0 ≤ ξ) (h1 : ξ ≤ ξ') (h2 : 0 ≤ η) (h3 : η ≤ η') :
    f ξ' η + f ξ η' ≤ f ξ' η' + f ξ η := by
  have p1 : 0 ≤ ξ' := h0.trans h1
  have p2 : 0 ≤ η' := h2.trans h3
  obtain ⟨X, hX, eX⟩ := hex ξ' η' p1 p2
  obtain ⟨Y, hY, eY⟩ := hex ξ η h0 h2
  have a1 := hle ξ' η p1 h2 X hX
  have a2 := hle ξ η' h0 p2 Y hY
  have a3 := hle ξ' η p1 h2 Y hY
  have a4 := hle ξ η' h0 p2 X hX
  by_cases iX : Di X <;> by_cases jX : Dj X <;> by_cases iY : Di Y <;> by_cases jY : Dj Y <;>
    simp only [iX, jX, iY, jY, if_true, if_false] at eX eY a1 a2 a3 a4 <;> try linarith
  obtain ⟨R, S, hR, hS, iR, jR, iS, jS, hb⟩ := H X Y hX hY iX jX iY jY
  have a5 := hle ξ' η p1 h2 R hR
  have a6 := hle ξ η' h0 p2 S hS
  simp only [iR, jR, iS, jS, if_true, if_false] at a5 a6
  linarith

theorem g70fn2_sub {α : Type} (sep : α → Prop) (Di Dj : α → Prop) [DecidablePred Di]
    [DecidablePred Dj] (b : α → ℝ) (f : ℝ → ℝ → ℝ)
    (hle : ∀ ξ η, 0 ≤ ξ → 0 ≤ η → ∀ X, sep X →
      f ξ η ≤ b X + (if Di X then ξ else 0) + (if Dj X then η else 0))
    (hex : ∀ ξ η, 0 ≤ ξ → 0 ≤ η → ∃ X, sep X ∧
      f ξ η = b X + (if Di X then ξ else 0) + (if Dj X then η else 0))
    (H : ∀ X Y, sep X → sep Y → ¬ Di X → Dj X → Di Y → ¬ Dj Y → ∃ R S, sep R ∧ sep S ∧
      ¬ Di R ∧ ¬ Dj R ∧ Di S ∧ Dj S ∧ b R + b S ≤ b X + b Y)
    (ξ ξ' η η' : ℝ) (h0 : 0 ≤ ξ) (h1 : ξ ≤ ξ') (h2 : 0 ≤ η) (h3 : η ≤ η') :
    f ξ' η' + f ξ η ≤ f ξ' η + f ξ η' := by
  have p1 : 0 ≤ ξ' := h0.trans h1
  have p2 : 0 ≤ η' := h2.trans h3
  obtain ⟨X, hX, eX⟩ := hex ξ' η p1 h2
  obtain ⟨Y, hY, eY⟩ := hex ξ η' h0 p2
  have a1 := hle ξ' η' p1 p2 X hX
  have a2 := hle ξ η h0 h2 Y hY
  have a3 := hle ξ' η' p1 p2 Y hY
  have a4 := hle ξ η h0 h2 X hX
  by_cases iX : Di X <;> by_cases jX : Dj X <;> by_cases iY : Di Y <;> by_cases jY : Dj Y <;>
    simp only [iX, jX, iY, jY, if_true, if_false] at eX eY a1 a2 a3 a4 <;> try linarith
  obtain ⟨R, S, hR, hS, iR, jR, iS, jS, hb⟩ := H X Y hX hY iX jX iY jY
  have a5 := hle ξ' η' p1 p2 R hR
  have a6 := hle ξ η h0 h2 S hS
  simp only [iR, jR, iS, jS, if_true, if_false] at a5 a6
  linarith

/-- sign of the difference quotient from super/submodularity -/
theorem g70fn2_q_nonneg (f : ℝ → ℝ → ℝ)
    (hs : ∀ ξ ξ' η η' : ℝ, 0 ≤ ξ → ξ ≤ ξ' → 0 ≤ η → η ≤ η' →
      f ξ' η + f ξ η' ≤ f ξ' η' + f ξ η)
    (ξ η h k : ℝ) (hA : IsAdmissible ξ η h k) :
    0 ≤ (f (ξ + h) (η + k) - f (ξ + h) η - f ξ (η + k) + f ξ η) / (h * k) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hA
  have hh : h ≠ 0 := fun e => a5 (by rw [e, zero_mul])
  have hk : k ≠ 0 := fun e => a5 (by rw [e, mul_zero])
  rcases lt_or_gt_of_ne hh with h1 | h1 <;> rcases lt_or_gt_of_ne hk with k1 | k1
  · have := hs (ξ + h) ξ (η + k) η a3 (by linarith) a4 (by linarith)
    exact div_nonneg (by linarith) (le_of_lt (mul_pos_of_neg_of_neg h1 k1))
  · have := hs (ξ + h) ξ η (η + k) a3 (by linarith) a2 (by linarith)
    exact div_nonneg_of_nonpos (by linarith) (le_of_lt (mul_neg_of_neg_of_pos h1 k1))
  · have := hs ξ (ξ + h) (η + k) η a1 (by linarith) a4 (by linarith)
    exact div_nonneg_of_nonpos (by linarith) (le_of_lt (mul_neg_of_pos_of_neg h1 k1))
  · have := hs ξ (ξ + h) η (η + k) a1 (by linarith) a2 (by linarith)
    exact div_nonneg (by linarith) (le_of_lt (mul_pos h1 k1))

theorem g70fn2_q_nonpos (f : ℝ → ℝ → ℝ)
    (hs : ∀ ξ ξ' η η' : ℝ, 0 ≤ ξ → ξ ≤ ξ' → 0 ≤ η → η ≤ η' →
      f ξ' η' + f ξ η ≤ f ξ' η + f ξ η')
    (ξ η h k : ℝ) (hA : IsAdmissible ξ η h k) :
    (f (ξ + h) (η + k) - f (ξ + h) η - f ξ (η + k) + f ξ η) / (h * k) ≤ 0 := by
  have := g70fn2_q_nonneg (fun a b => - f a b) (fun ξ ξ' η η' a b c d => by
    have := hs ξ ξ' η η' a b c d; linarith) ξ η h k hA
  have e : (-f (ξ + h) (η + k) - -f (ξ + h) η - -f ξ (η + k) + -f ξ η) / (h * k) =
      -((f (ξ + h) (η + k) - f (ξ + h) η - f ξ (η + k) + f ξ η) / (h * k)) := by ring
  rw [e] at this
  linarith

variable {N : Type} [Fintype N] [DecidableEq N]

theorem g70fn2_tsub (G : Network N) (cap : N × N → ℝ≥0∞) (X Y : Finset N) :
    cutCapacity G cap (X ∪ Y) + cutCapacity G cap (X ∩ Y) ≤
      cutCapacity G cap X + cutCapacity G cap Y := by
  unfold cutCapacity
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  simp only [Finset.mem_union, Finset.mem_inter]
  by_cases a1 : a.1 ∈ X <;> by_cases a2 : a.1 ∈ Y <;> by_cases b1 : a.2 ∈ X <;>
    by_cases b2 : a.2 ∈ Y <;> simp [a1, a2, b1, b2]

/-- the real-valued data for the two-arc problem -/
theorem g70fn2_real (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N)
    (hAi : Ai ∈ G.arcs) (hAj : Aj ∈ G.arcs) (hij : Ai ≠ Aj) :
    (∀ ξ η, 0 ≤ ξ → 0 ≤ η → ∀ X, IsSeparating G X →
      vbarTwoReal G c Ai Aj ξ η ≤ (g70fn2_B2 G c Ai Aj X).toReal +
        (if Ai.1 ∈ X ∧ Ai.2 ∉ X then ξ else 0) + (if Aj.1 ∈ X ∧ Aj.2 ∉ X then η else 0)) ∧
    (∀ ξ η, 0 ≤ ξ → 0 ≤ η → ∃ X, IsSeparating G X ∧
      vbarTwoReal G c Ai Aj ξ η = (g70fn2_B2 G c Ai Aj X).toReal +
        (if Ai.1 ∈ X ∧ Ai.2 ∉ X then ξ else 0) + (if Aj.1 ∈ X ∧ Aj.2 ∉ X then η else 0)) ∧
    (∀ X Y R S : Finset N, R = X ∪ Y ∨ R = X ∩ Y → S = X ∪ Y ∨ S = X ∩ Y → R ≠ S →
      (g70fn2_B2 G c Ai Aj R).toReal + (g70fn2_B2 G c Ai Aj S).toReal ≤
        (g70fn2_B2 G c Ai Aj X).toReal + (g70fn2_B2 G c Ai Aj Y).toReal) := by
  classical
  have hBfin : ∀ X, g70fn2_B2 G c Ai Aj X ≠ ⊤ := fun X =>
    ENNReal.sum_ne_top.2 fun a _ => ENNReal.coe_ne_top
  have hcut := g70fn2_capTwo_cut G c Ai Aj hAi hAj hij
  have hconv : ∀ ξ η : ℝ, 0 ≤ ξ → 0 ≤ η → ∀ X,
      (cutCapacity G (capTwo c Ai Aj (ENNReal.ofReal ξ) (ENNReal.ofReal η)) X) ≠ ⊤ ∧
      (cutCapacity G (capTwo c Ai Aj (ENNReal.ofReal ξ) (ENNReal.ofReal η)) X).toReal =
        (g70fn2_B2 G c Ai Aj X).toReal +
        (if Ai.1 ∈ X ∧ Ai.2 ∉ X then ξ else 0) + (if Aj.1 ∈ X ∧ Aj.2 ∉ X then η else 0) := by
    intro ξ η hξ hη X
    rw [hcut]
    have t1 : (if Ai.1 ∈ X ∧ Ai.2 ∉ X then ENNReal.ofReal ξ else 0) ≠ ⊤ := by
      split_ifs <;> simp
    have t2 : (if Aj.1 ∈ X ∧ Aj.2 ∉ X then ENNReal.ofReal η else 0) ≠ ⊤ := by
      split_ifs <;> simp
    refine ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hBfin X, t1⟩, t2⟩, ?_⟩
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hBfin X, t1⟩) t2,
      ENNReal.toReal_add (hBfin X) t1]
    congr 1; congr 1
    · split_ifs <;> simp [ENNReal.toReal_ofReal hξ]
    · split_ifs <;> simp [ENNReal.toReal_ofReal hη]
  refine ⟨?_, ?_, ?_⟩
  · intro ξ η hξ hη X hX
    have h1 := (g70fn2_gen G (capTwo c Ai Aj (ENNReal.ofReal ξ) (ENNReal.ofReal η))).1 X hX
    obtain ⟨hne, he⟩ := hconv ξ η hξ hη X
    unfold vbarTwoReal vbarTwo
    rw [← he]
    exact ENNReal.toReal_mono hne h1
  · intro ξ η hξ hη
    obtain ⟨X, hX, hXe⟩ := (g70fn2_gen G (capTwo c Ai Aj (ENNReal.ofReal ξ) (ENNReal.ofReal η))).2
    refine ⟨X, hX, ?_⟩
    unfold vbarTwoReal vbarTwo
    rw [hXe, (hconv ξ η hξ hη X).2]
  · intro X Y R S hR hS hRS
    have e0 : ∀ Z, cutCapacity G (capTwo c Ai Aj 0 0) Z = g70fn2_B2 G c Ai Aj Z := by
      intro Z; rw [hcut]; simp
    have hsub := g70fn2_tsub G (capTwo c Ai Aj 0 0) X Y
    simp only [e0] at hsub
    have key : g70fn2_B2 G c Ai Aj R + g70fn2_B2 G c Ai Aj S ≤
        g70fn2_B2 G c Ai Aj X + g70fn2_B2 G c Ai Aj Y := by
      rcases hR with rfl | rfl <;> rcases hS with rfl | rfl
      · exact absurd rfl hRS
      · exact hsub
      · rw [add_comm]; exact hsub
      · exact absurd rfl hRS
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hBfin X, hBfin Y⟩) key
    rwa [ENNReal.toReal_add (hBfin R) (hBfin S), ENNReal.toReal_add (hBfin X) (hBfin Y)] at this

end g70fn2Sign

open FlowsNetworks.TwoArcs
open scoped ENNReal NNReal

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N)
    (hAi : Ai ∈ G.arcs) (hAj : Aj ∈ G.arcs) (hij : Ai ≠ Aj) :
    ((pValue G c Ai Aj = ExtValue.posInf ∨
          ∃ r : ℝ, 0 < r ∧ pValue G c Ai Aj = ExtValue.real r) →
        (∃ ξ η h k : ℝ, IsAdmissible ξ η h k ∧ 0 < diffQuotient G c Ai Aj ξ η h k) ∧
          ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → ¬ diffQuotient G c Ai Aj ξ η h k < 0) ∧
      ((pValue G c Ai Aj = ExtValue.indeterminate ∨ pValue G c Ai Aj = ExtValue.real 0) →
        ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → diffQuotient G c Ai Aj ξ η h k = 0) ∧
      ((pValue G c Ai Aj = ExtValue.negInf ∨
          ∃ r : ℝ, r < 0 ∧ pValue G c Ai Aj = ExtValue.real r) →
        (∃ ξ η h k : ℝ, IsAdmissible ξ η h k ∧ diffQuotient G c Ai Aj ξ η h k < 0) ∧
          ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → ¬ 0 < diffQuotient G c Ai Aj ξ η h k) := by
  classical
  set F := fun x y => vbarTwo G c Ai Aj x y with hF
  have h134 : ∀ x y, F x y = min (min (min (F 0 0 + x + y) (F 0 ⊤ + x)) (F ⊤ 0 + y)) (F ⊤ ⊤) :=
    fun x y => g70fn2_134 G c Ai Aj hAi hAj hij x y
  set A := F 0 0
  set B := F 0 ⊤
  set C := F ⊤ 0
  set D := F ⊤ ⊤
  have hmono : ∀ x y x' y', x ≤ x' → y ≤ y' → F x y ≤ F x' y' := by
    intro x y x' y' hx hy
    apply g70fn2_mono
    intro a; unfold capTwo; split_ifs
    · exact hx
    · exact hy
    · exact le_rfl
  have hBD : B ≤ D := hmono _ _ _ _ bot_le le_rfl
  have hCD : C ≤ D := hmono _ _ _ _ le_rfl bot_le
  have hAfin : A ≠ ⊤ := by
    have h1 := (g70fn2_gen G (capTwo c Ai Aj 0 0)).1 G.sources
      ⟨subset_refl _, G.sources_sinks_disjoint⟩
    rw [g70fn2_capTwo_cut G c Ai Aj hAi hAj hij] at h1
    refine ne_top_of_le_ne_top ?_ h1
    have : g70fn2_B2 G c Ai Aj G.sources ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun a _ => ENNReal.coe_ne_top
    simp [this]
  set f := vbarTwoReal G c Ai Aj with hf
  have hfF : ∀ ξ η, f ξ η = (F (ENNReal.ofReal ξ) (ENNReal.ofReal η)).toReal := fun _ _ => rfl
  set a := A.toReal
  set b := B.toReal
  set cc := C.toReal
  set d := D.toReal
  have L : ∀ ξ η : ℝ, 0 ≤ ξ → 0 ≤ η → (f ξ η ≤ a + ξ + η) ∧ (B ≠ ⊤ → f ξ η ≤ b + ξ) ∧
      (C ≠ ⊤ → f ξ η ≤ cc + η) ∧ (D ≠ ⊤ → f ξ η ≤ d) ∧
      (f ξ η = a + ξ + η ∨ (B ≠ ⊤ ∧ f ξ η = b + ξ) ∨ (C ≠ ⊤ ∧ f ξ η = cc + η) ∨
        (D ≠ ⊤ ∧ f ξ η = d)) := by
    intro ξ η hξ hη
    have e := h134 (ENNReal.ofReal ξ) (ENNReal.ofReal η)
    have hA1 : A + ENNReal.ofReal ξ + ENNReal.ofReal η ≠ ⊤ := by simp [hAfin]
    have hFne : F (ENNReal.ofReal ξ) (ENNReal.ofReal η) ≠ ⊤ := by
      rw [e]; exact ne_top_of_le_ne_top hA1 (min_le_of_left_le (min_le_of_left_le (min_le_left _ _)))
    have r1 : (A + ENNReal.ofReal ξ + ENNReal.ofReal η).toReal = a + ξ + η := by
      rw [ENNReal.toReal_add (by simp [hAfin]) ENNReal.ofReal_ne_top,
        ENNReal.toReal_add hAfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hξ,
        ENNReal.toReal_ofReal hη]
    have r2 : B ≠ ⊤ → (B + ENNReal.ofReal ξ).toReal = b + ξ := fun hB => by
      rw [ENNReal.toReal_add hB ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hξ]
    have r3 : C ≠ ⊤ → (C + ENNReal.ofReal η).toReal = cc + η := fun hC => by
      rw [ENNReal.toReal_add hC ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hη]
    refine ⟨?_, fun hB => ?_, fun hC => ?_, fun hD => ?_, ?_⟩
    · rw [hfF, ← r1]; refine ENNReal.toReal_mono hA1 ?_
      rw [e]; exact min_le_of_left_le (min_le_of_left_le (min_le_left _ _))
    · rw [hfF, ← r2 hB]; refine ENNReal.toReal_mono (by simp [hB]) ?_
      rw [e]; exact min_le_of_left_le (min_le_of_left_le (min_le_right _ _))
    · rw [hfF, ← r3 hC]; refine ENNReal.toReal_mono (by simp [hC]) ?_
      rw [e]; exact min_le_of_left_le (min_le_right _ _)
    · rw [hfF]; refine ENNReal.toReal_mono hD ?_
      rw [e]; exact min_le_right _ _
    · rw [hfF]
      rcases min_choice (min (min (A + ENNReal.ofReal ξ + ENNReal.ofReal η) (B + ENNReal.ofReal ξ))
          (C + ENNReal.ofReal η)) D with h4 | h4 <;> rw [e, h4] <;> rw [e, h4] at hFne
      · rcases min_choice (min (A + ENNReal.ofReal ξ + ENNReal.ofReal η) (B + ENNReal.ofReal ξ))
            (C + ENNReal.ofReal η) with h3 | h3 <;> rw [h3] <;> rw [h3] at hFne
        · rcases min_choice (A + ENNReal.ofReal ξ + ENNReal.ofReal η) (B + ENNReal.ofReal ξ)
            with h2 | h2 <;> rw [h2] <;> rw [h2] at hFne
          · exact Or.inl r1
          · have hB : B ≠ ⊤ := fun h => hFne (by simp [h])
            exact Or.inr (Or.inl ⟨hB, r2 hB⟩)
        · have hC : C ≠ ⊤ := fun h => hFne (by simp [h])
          exact Or.inr (Or.inr (Or.inl ⟨hC, r3 hC⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hFne, rfl⟩))
  have hBfin : D ≠ ⊤ → B ≠ ⊤ := fun h => ne_top_of_le_ne_top h hBD
  have hCfin : D ≠ ⊤ → C ≠ ⊤ := fun h => ne_top_of_le_ne_top h hCD
  have hbd : D ≠ ⊤ → b ≤ d := fun h => ENNReal.toReal_mono h hBD
  have hcd : D ≠ ⊤ → cc ≤ d := fun h => ENNReal.toReal_mono h hCD
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ cc := ENNReal.toReal_nonneg
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  -- supermodularity
  have SUP : (D ≠ ⊤ → b + cc ≤ d + a) → ∀ ξ ξ' η η' : ℝ, 0 ≤ ξ → ξ ≤ ξ' → 0 ≤ η → η ≤ η' →
      f ξ' η + f ξ η' ≤ f ξ' η' + f ξ η := by
    intro hyp ξ ξ' η η' h0 h1 h2 h3
    have p1 : 0 ≤ ξ' := h0.trans h1
    have p2 : 0 ≤ η' := h2.trans h3
    obtain ⟨u1, u2, u3, u4, -⟩ := L ξ' η p1 h2
    obtain ⟨w1, w2, w3, w4, -⟩ := L ξ η' h0 p2
    obtain ⟨-, -, -, -, E1⟩ := L ξ' η' p1 p2
    obtain ⟨-, -, -, -, E2⟩ := L ξ η h0 h2
    rcases E1 with e1 | ⟨hB1, e1⟩ | ⟨hC1, e1⟩ | ⟨hD1, e1⟩ <;>
    rcases E2 with e2 | ⟨hB2, e2⟩ | ⟨hC2, e2⟩ | ⟨hD2, e2⟩ <;>
    first
    | linarith
    | linarith [u2 hB1, w2 hB1]
    | linarith [u2 hB2, w2 hB2]
    | linarith [u3 hC1, w3 hC1]
    | linarith [u3 hC2, w3 hC2]
    | linarith [u4 hD1, w4 hD1]
    | linarith [u4 hD2, w4 hD2]
    | linarith [u2 hB1, w3 hC2]
    | linarith [u3 hC1, w2 hB2]
    | linarith [u2 hB2, w3 hC1]
    | linarith [u3 hC2, w2 hB1]
    | linarith [u3 (hCfin hD1), w2 (hBfin hD1), hyp hD1]
    | linarith [u3 hC1, w2 hB2, u2 hB2, w3 hC1]
    | linarith [u2 hB1, w3 hC2, u3 hC2, w2 hB1]
    | linarith [u2 hB1, w2 hB1, u4 hD2, w4 hD2]
    | linarith [u3 hC1, w3 hC1, u4 hD2, w4 hD2]
    | linarith [u2 hB2, w2 hB2, u4 hD1, w4 hD1]
    | linarith [u3 hC2, w3 hC2, u4 hD1, w4 hD1]
  have SUB : (B ≠ ⊤ → C ≠ ⊤ → D ≠ ⊤ ∧ d + a ≤ b + cc) → ∀ ξ ξ' η η' : ℝ, 0 ≤ ξ → ξ ≤ ξ' →
      0 ≤ η → η ≤ η' → f ξ' η' + f ξ η ≤ f ξ' η + f ξ η' := by
    intro hyp ξ ξ' η η' h0 h1 h2 h3
    have p1 : 0 ≤ ξ' := h0.trans h1
    have p2 : 0 ≤ η' := h2.trans h3
    obtain ⟨u1, u2, u3, u4, -⟩ := L ξ' η' p1 p2
    obtain ⟨w1, w2, w3, w4, -⟩ := L ξ η h0 h2
    obtain ⟨-, -, -, -, E1⟩ := L ξ' η p1 h2
    obtain ⟨-, -, -, -, E2⟩ := L ξ η' h0 p2
    rcases E1 with e1 | ⟨hB1, e1⟩ | ⟨hC1, e1⟩ | ⟨hD1, e1⟩ <;>
    rcases E2 with e2 | ⟨hB2, e2⟩ | ⟨hC2, e2⟩ | ⟨hD2, e2⟩ <;>
    first
    | linarith
    | linarith [u2 hB1, w2 hB1]
    | linarith [u2 hB2, w2 hB2]
    | linarith [u3 hC1, w3 hC1]
    | linarith [u3 hC2, w3 hC2]
    | linarith [u4 hD1, w4 hD1]
    | linarith [u4 hD2, w4 hD2]
    | linarith [u4 (hyp hB2 hC1).1, (hyp hB2 hC1).2]
    | linarith [u2 hB1, w3 hC2]
    | linarith [u3 hC1, w2 hB2]
    | linarith [u2 hB2, w3 hC1]
    | linarith [u3 hC2, w2 hB1]
    | linarith [u2 hB1, w2 hB1, u4 hD2, w4 hD2]
    | linarith [u3 hC1, w3 hC1, u4 hD2, w4 hD2]
    | linarith [u2 hB2, w2 hB2, u4 hD1, w4 hD1]
    | linarith [u3 hC2, w3 hC2, u4 hD1, w4 hD1]
  have hpv : pValue G c Ai Aj = if D + A = ⊤ ∧ B + C = ⊤ then ExtValue.indeterminate
      else if D + A = ⊤ then ExtValue.posInf else if B + C = ⊤ then ExtValue.negInf
      else ExtValue.real ((D + A).toReal - (B + C).toReal) := rfl
  have hDA : D + A = ⊤ ↔ D = ⊤ := by simp [ENNReal.add_eq_top, hAfin]
  have hBC : B + C = ⊤ ↔ B = ⊤ ∨ C = ⊤ := ENNReal.add_eq_top
  have tDA : D ≠ ⊤ → (D + A).toReal = d + a := fun h => ENNReal.toReal_add h hAfin
  have tBC : B ≠ ⊤ → C ≠ ⊤ → (B + C).toReal = b + cc := fun h1 h2 => ENNReal.toReal_add h1 h2
  have f00 : f 0 0 = a := by rw [hfF, ENNReal.ofReal_zero]
  have hq : ∀ H : ℝ, diffQuotient G c Ai Aj 0 0 H H = (f H H - f H 0 - f 0 H + f 0 0) / (H * H) := by
    intro H; unfold diffQuotient; simp only [zero_add]; rfl
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
  · have key : (D ≠ ⊤ → b + cc < d + a) ∧ B ≠ ⊤ ∧ C ≠ ⊤ := by
      rw [hpv] at hp
      split_ifs at hp with h1 h2 h3
      · simp at hp
      · rw [hDA] at h2
        have : ¬ (B = ⊤ ∨ C = ⊤) := fun h => h1 ⟨hDA.2 h2, hBC.2 h⟩
        push_neg at this
        exact ⟨fun h => absurd h2 h, this⟩
      · simp at hp
      · rw [hDA] at h2; rw [hBC] at h3; push_neg at h3
        obtain ⟨r, hr, he⟩ := hp.resolve_left (by simp)
        simp only [ExtValue.real.injEq] at he
        rw [tDA h2, tBC h3.1 h3.2] at he
        exact ⟨fun _ => by linarith, h3⟩
    obtain ⟨k1, kB, kC⟩ := key
    refine ⟨?_, fun ξ η h k hA => not_lt.2 (g70fn2_q_nonneg f
      (SUP fun hD => le_of_lt (k1 hD)) ξ η h k hA)⟩
    set H := b + cc + d + 1 with hH
    have hH0 : 0 < H := by linarith
    refine ⟨0, 0, H, H, ⟨le_rfl, le_rfl, by linarith, by linarith, by positivity⟩, ?_⟩
    rw [hq]
    apply div_pos _ (by positivity)
    have l1 := (L H 0 hH0.le le_rfl).2.2.1 kC
    have l2 := (L 0 H le_rfl hH0.le).2.1 kB
    obtain ⟨-, -, -, -, E⟩ := L H H hH0.le hH0.le
    rcases E with e | ⟨-, e⟩ | ⟨-, e⟩ | ⟨hD, e⟩
    · linarith
    · linarith
    · linarith
    · have := k1 hD; linarith
  · have key : (D ≠ ⊤ → b + cc ≤ d + a) ∧ (B ≠ ⊤ → C ≠ ⊤ → D ≠ ⊤ ∧ d + a ≤ b + cc) := by
      rw [hpv] at hp
      split_ifs at hp with h1 h2 h3
      · rw [hDA, hBC] at h1
        refine ⟨fun h => absurd h1.1 h, fun hB hC => ?_⟩
        rcases h1.2 with h | h
        · exact absurd h hB
        · exact absurd h hC
      · simp at hp
      · simp at hp
      · rw [hDA] at h2; rw [hBC] at h3; push_neg at h3
        have he := hp.resolve_left (by simp)
        simp only [ExtValue.real.injEq] at he
        rw [tDA h2, tBC h3.1 h3.2] at he
        exact ⟨fun _ => by linarith, fun _ _ => ⟨h2, by linarith⟩⟩
    intro ξ η h k hA
    exact le_antisymm (g70fn2_q_nonpos f (SUB key.2) ξ η h k hA)
      (g70fn2_q_nonneg f (SUP key.1) ξ η h k hA)
  · have key : D ≠ ⊤ ∧ B ≠ ⊤ ∧ C ≠ ⊤ ∧ d + a < b + cc := by
      rw [hpv] at hp
      split_ifs at hp with h1 h2 h3
      · simp at hp
      · simp at hp
      · rw [hDA] at h2
        exact absurd (hBC.1 h3) (by push_neg; exact ⟨hBfin h2, hCfin h2⟩)
      · rw [hDA] at h2; rw [hBC] at h3; push_neg at h3
        obtain ⟨r, hr, he⟩ := hp.resolve_left (by simp)
        simp only [ExtValue.real.injEq] at he
        rw [tDA h2, tBC h3.1 h3.2] at he
        exact ⟨h2, h3.1, h3.2, by linarith⟩
    obtain ⟨kD, kB, kC, k1⟩ := key
    refine ⟨?_, fun ξ η h k hA => not_lt.2 (g70fn2_q_nonpos f
      (SUB fun _ _ => ⟨kD, le_of_lt k1⟩) ξ η h k hA)⟩
    set H := b + cc + d + 1 with hH
    have hH0 : 0 < H := by linarith
    refine ⟨0, 0, H, H, ⟨le_rfl, le_rfl, by linarith, by linarith, by positivity⟩, ?_⟩
    rw [hq]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have l1 := (L H H hH0.le hH0.le).2.2.2.1 kD
    have hcd' := hcd kD
    have hbd' := hbd kD
    obtain ⟨-, -, -, -, E1⟩ := L H 0 hH0.le le_rfl
    obtain ⟨-, -, -, -, E2⟩ := L 0 H le_rfl hH0.le
    have g1 : cc ≤ f H 0 := by
      rcases E1 with e | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> linarith
    have g2 : b ≤ f 0 H := by
      rcases E2 with e | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> linarith
    linarith
