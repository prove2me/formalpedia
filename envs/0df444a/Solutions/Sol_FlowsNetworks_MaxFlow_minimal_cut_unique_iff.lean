-- Prove2me | solution 1 for FlowsNetworks.MaxFlow.minimal_cut_unique_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:30:48.34982+00:00
-- url     : https://prove2.me/submissions/8e97c41d-550d-4b8c-99c4-3a9b6ad4df74

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network
import Definitions.Def_FlowsNetworks_MaxFlow_AugmentingPath
open FlowsNetworks.MaxFlow


section g69e
variable {N : Type} [Fintype N] [DecidableEq N]
set_option linter.unusedSectionVars false

def g69e_Res (G : Network N) (f : N → N → ℝ) (ε : ℝ) (u w : N) : Prop :=
  ((u, w) ∈ G.arcs ∧ f u w + ε ≤ G.cap u w) ∨ ((w, u) ∈ G.arcs ∧ ε ≤ f w u)

def g69e_Step (R : N → N → Prop) (a b : N × List N) : Prop :=
  R a.1 b.1 ∧ b.1 ∉ a.2 ∧ b.2 = b.1 :: a.2

def g69e_e (a b : N) : N → N → ℝ := fun u w => if u = a ∧ w = b then 1 else 0

theorem g69e_netFlowOut_add (G : Network N) (f g : N → N → ℝ) (z : N) :
    netFlowOut G (f + g) z = netFlowOut G f z + netFlowOut G g z := by
  unfold netFlowOut; simp only [Pi.add_apply, Finset.sum_add_distrib]; ring

theorem g69e_netFlowOut_smul (G : Network N) (f : N → N → ℝ) (c : ℝ) (z : N) :
    netFlowOut G (c • f) z = c * netFlowOut G f z := by
  unfold netFlowOut; simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring

theorem g69e_netFlowOut_e (G : Network N) (a b : N) (hab : (a, b) ∈ G.arcs) (z : N) :
    netFlowOut G (g69e_e a b) z = (if z = a then 1 else 0) - (if z = b then 1 else 0) := by
  unfold netFlowOut g69e_e
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

theorem g69e_step_mem {R : N → N → Prop} {s : N} {x : N} {l : List N}
    (h : Relation.ReflTransGen (g69e_Step R) (s, [s]) (x, l)) : x ∈ l ∧ s ∈ l := by
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

theorem g69e_step_prefix {R : N → N → Prop} {s : N} {x : N} {l : List N}
    (h : Relation.ReflTransGen (g69e_Step R) (s, [s]) (x, l)) :
    ∀ z ∈ l, ∃ l', Relation.ReflTransGen (g69e_Step R) (s, [s]) (z, l') := by
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

theorem g69e_simple {R : N → N → Prop} {s x : N} (h : Relation.ReflTransGen R s x) :
    ∃ l, Relation.ReflTransGen (g69e_Step R) (s, [s]) (x, l) := by
  induction h with
  | refl => exact ⟨_, Relation.ReflTransGen.refl⟩
  | @tail y x _ hyx ih =>
    obtain ⟨l, hl⟩ := ih
    by_cases hx : x ∈ l
    · exact g69e_step_prefix hl x hx
    · exact ⟨x :: l, hl.tail ⟨hyx, hx, rfl⟩⟩

/-- augmentation along a simple residual path -/
theorem g69e_augment (G : Network N) (f : N → N → ℝ) (s : N)
    (hnn : ∀ p ∈ G.arcs, 0 ≤ f p.1 p.2) (hcap : ∀ p ∈ G.arcs, f p.1 p.2 ≤ G.cap p.1 p.2)
    (ε : ℝ) (hε : 0 < ε) {x : N} {l : List N}
    (h : Relation.ReflTransGen (g69e_Step (g69e_Res G f ε)) (s, [s]) (x, l)) :
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
    have hyl : y ∈ l0 := (g69e_step_mem h1).1
    have hxy : x ≠ y := fun e => hx (e ▸ hyl)
    rcases hR with ⟨harc, hres⟩ | ⟨harc, hres⟩
    · refine ⟨g + ε • g69e_e y x, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab
        by_cases he : a = y ∧ b = x
        · obtain ⟨rfl, rfl⟩ := he; simp [hyl]
        · have : g a b ≠ 0 := by simpa [g69e_e, he] using hab
          have := hgl a b this
          exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩
      · intro a b hab
        have : ¬ (a = y ∧ b = x) := by rintro ⟨rfl, rfl⟩; exact hab harc
        simp [g69e_e, this, hgs a b hab]
      · intro p hp
        obtain ⟨p1, p2⟩ := p
        by_cases he : p1 = y ∧ p2 = x
        · obtain ⟨rfl, rfl⟩ := he
          have hg0 : g p1 p2 = 0 := by
            by_contra hne; exact hx (hgl _ _ hne).2
          have hfp := hnn _ hp
          simp only [Pi.add_apply, Pi.smul_apply, g69e_e, and_self, if_true, smul_eq_mul,
            mul_one, hg0] at hfp ⊢
          constructor <;> linarith
        · simpa [g69e_e, he] using hgf _ hp
      · intro z
        rw [g69e_netFlowOut_add, g69e_netFlowOut_smul, g69e_netFlowOut_e G y x harc, hgn]
        clear ih h1 hgf hgk hgl hgs hgn
        by_cases hzs : z = s <;> by_cases hzy : z = y <;> by_cases hzx : z = x <;>
          simp_all
      · intro a b
        obtain ⟨k, hk⟩ := hgk a b
        by_cases he : a = y ∧ b = x
        · refine ⟨k + 1, ?_⟩
          have hk' := hk
          rw [he.1, he.2] at hk' ⊢
          simp only [Pi.add_apply, Pi.smul_apply, g69e_e, and_self, if_true,
            smul_eq_mul, mul_one, hk']
          push_cast; ring
        · exact ⟨k, by simp [g69e_e, he, hk]⟩
    · refine ⟨g - ε • g69e_e x y, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab
        by_cases he : a = x ∧ b = y
        · obtain ⟨rfl, rfl⟩ := he; simp [hyl]
        · have : g a b ≠ 0 := by simpa [g69e_e, he] using hab
          have := hgl a b this
          exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩
      · intro a b hab
        have : ¬ (a = x ∧ b = y) := by rintro ⟨rfl, rfl⟩; exact hab harc
        simp [g69e_e, this, hgs a b hab]
      · intro p hp
        obtain ⟨p1, p2⟩ := p
        by_cases he : p1 = x ∧ p2 = y
        · obtain ⟨rfl, rfl⟩ := he
          have hg0 : g p1 p2 = 0 := by
            by_contra hne; exact hx (hgl _ _ hne).1
          have hfp := hcap _ hp
          simp only [Pi.sub_apply, Pi.smul_apply, g69e_e, and_self, if_true, smul_eq_mul,
            mul_one, hg0] at hfp ⊢
          constructor <;> linarith
        · simpa [g69e_e, he] using hgf _ hp
      · intro z
        rw [sub_eq_add_neg, g69e_netFlowOut_add, ← neg_smul, g69e_netFlowOut_smul,
          g69e_netFlowOut_e G x y harc, hgn]
        clear ih h1 hgf hgk hgl hgs hgn
        by_cases hzs : z = s <;> by_cases hzy : z = y <;> by_cases hzx : z = x <;>
          simp_all
      · intro a b
        obtain ⟨k, hk⟩ := hgk a b
        by_cases he : a = x ∧ b = y
        · refine ⟨k - 1, ?_⟩
          have hk' := hk
          rw [he.1, he.2] at hk' ⊢
          simp only [Pi.sub_apply, Pi.smul_apply, g69e_e, and_self, if_true,
            smul_eq_mul, mul_one, hk']
          push_cast; ring
        · exact ⟨k, by simp [g69e_e, he, hk]⟩

theorem g69e_arcSum_eq {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (g : N → N → ℝ)
    (X Y : Finset N) :
    arcSum G g X Y = ∑ p ∈ G.arcs, if p.1 ∈ X ∧ p.2 ∈ Y then g p.1 p.2 else 0 := by
  unfold arcSum arcsBetween; rw [Finset.sum_filter]

theorem g69e_cut_submod {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (X Y : Finset N) :
    cutCapacity G (X ∪ Y) + cutCapacity G (X ∩ Y) ≤ cutCapacity G X + cutCapacity G Y := by
  unfold cutCapacity
  simp only [g69e_arcSum_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have h := G.cap_nonneg p hp
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
  by_cases a1 : p.1 ∈ X <;> by_cases a2 : p.1 ∈ Y <;> by_cases b1 : p.2 ∈ X <;> by_cases b2 : p.2 ∈ Y <;>
    simp [a1, a2, b1, b2, h]

theorem g69e_sum_netFlowOut {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ)
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
  rw [Finset.sum_sub_distrib, key (fun p => p.1), key (fun p => p.2), g69e_arcSum_eq, g69e_arcSum_eq,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Finset.mem_compl]
  by_cases a : p.1 ∈ X <;> by_cases b : p.2 ∈ X <;> simp [a, b]


theorem g69e_flow41 {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) (hf : IsFlow G s t f v)
    (X : Finset N) (hs : s ∈ X) (ht : t ∉ X) :
    v = arcSum G f X Xᶜ - arcSum G f Xᶜ X ∧
      arcSum G f X Xᶜ - arcSum G f Xᶜ X ≤ cutCapacity G X := by
  obtain ⟨hsupp, hnn, hcap, h1, h2, h3⟩ := hf
  constructor
  · rw [← g69e_sum_netFlowOut, ← Finset.add_sum_erase X _ hs, h1, Finset.sum_eq_zero]
    · ring
    intro x hx
    exact h3 x (Finset.ne_of_mem_erase hx) (fun h => ht (h ▸ Finset.mem_of_mem_erase hx))
  · have e1 : arcSum G f X Xᶜ ≤ cutCapacity G X := Finset.sum_le_sum fun p hp =>
      hcap p (Finset.mem_filter.1 hp).1
    have e2 : 0 ≤ arcSum G f Xᶜ X := Finset.sum_nonneg fun p hp => hnn p (Finset.mem_filter.1 hp).1
    linarith

theorem g69e_sourceSet_s (G : Network N) (f : N → N → ℝ) (s : N) : s ∈ sourceSet G f s := by
  unfold sourceSet; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro Z hs _; exact hs

theorem g69e_sourceSet_closed (G : Network N) (f : N → N → ℝ) (s : N) {x y : N}
    (hx : x ∈ sourceSet G f s) (hxy : AugStep G f x y) : y ∈ sourceSet G f s := by
  unfold sourceSet at *; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  intro Z hs hZ; exact hZ x y (hx Z hs hZ) hxy

theorem g69e_sourceSet_min (G : Network N) (f : N → N → ℝ) (s : N) (Z : Finset N) (hs : s ∈ Z)
    (hZ : ∀ u w, u ∈ Z → AugStep G f u w → w ∈ Z) : sourceSet G f s ⊆ Z := by
  intro x hx; unfold sourceSet at hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx Z hs hZ

theorem g69e_sourceSet_reach (G : Network N) (f : N → N → ℝ) (s : N) {x : N}
    (hx : x ∈ sourceSet G f s) : Relation.ReflTransGen (AugStep G f) s x := by
  classical
  have := g69e_sourceSet_min G f s (Finset.univ.filter (fun y => Relation.ReflTransGen (AugStep G f) s y))
    (by simpa using Relation.ReflTransGen.refl) (by
      intro u w hu huw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact hu.tail huw)
  simpa using this hx

theorem g69e_res_mono (G : Network N) (f : N → N → ℝ) {ε ε' : ℝ} (h : ε' ≤ ε) {u w : N}
    (hr : g69e_Res G f ε u w) : g69e_Res G f ε' u w := by
  rcases hr with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨a, by linarith⟩
  · exact Or.inr ⟨a, by linarith⟩

theorem g69e_res_exists (G : Network N) (f : N → N → ℝ) (s : N) {x : N} {l : List N}
    (h : Relation.ReflTransGen (g69e_Step (AugStep G f)) (s, [s]) (x, l)) :
    ∃ ε > 0, Relation.ReflTransGen (g69e_Step (g69e_Res G f ε)) (s, [s]) (x, l) := by
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
    have : ∃ δ > 0, g69e_Res G f δ y x := by
      rcases hR with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨G.cap y x - f y x, by linarith, Or.inl ⟨a, by linarith⟩⟩
      · exact ⟨f x y, b, Or.inr ⟨a, le_rfl⟩⟩
    obtain ⟨δ, hδ, hr⟩ := this
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩
    refine Relation.ReflTransGen.tail (Relation.ReflTransGen.mono (fun a b (hab : g69e_Step (g69e_Res G f ε) a b) => (⟨g69e_res_mono G f (min_le_left _ _) hab.1, hab.2⟩ : g69e_Step (g69e_Res G f (min ε δ)) a b)) _ _ hrt) ?_
    refine ⟨g69e_res_mono G f (min_le_right _ _) hr, hx, ?_⟩
    simpa using h3

theorem g69e_res_one (G : Network N) (f : N → N → ℝ)
    (hfi : ∀ p ∈ G.arcs, ∃ n : ℤ, f p.1 p.2 = n) (hci : ∀ p ∈ G.arcs, ∃ n : ℤ, G.cap p.1 p.2 = n)
    {u w : N} (h : AugStep G f u w) : g69e_Res G f 1 u w := by
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

theorem g69e_augment_flow (G : Network N) (s t : N) (hst : s ≠ t) (f : N → N → ℝ) (v : ℝ)
    (hf : IsFlow G s t f v) (ε : ℝ) (hε : 0 < ε) {l : List N}
    (h : Relation.ReflTransGen (g69e_Step (g69e_Res G f ε)) (s, [s]) (t, l)) :
    ∃ g : N → N → ℝ, IsFlow G s t (f + g) (v + ε) ∧ ∀ a b, ∃ k : ℤ, g a b = k * ε := by
  obtain ⟨hsupp, hnn, hcap, h1, h2, h3⟩ := hf
  obtain ⟨g, -, hgs, hgf, hgn, hgk⟩ := g69e_augment G f s hnn hcap ε hε h
  refine ⟨g, ⟨?_, fun p hp => (hgf p hp).1, fun p hp => (hgf p hp).2, ?_, ?_, ?_⟩, hgk⟩
  · intro a b hab; simp [hsupp a b hab, hgs a b hab]
  · rw [g69e_netFlowOut_add, h1, hgn]; simp [hst]
  · rw [g69e_netFlowOut_add, h2, hgn]; simp [Ne.symm hst]; ring
  · intro x hxs hxt; rw [g69e_netFlowOut_add, h3 x hxs hxt, hgn]; simp [hxs, hxt]

theorem g69e_max_not_mem (G : Network N) (s t : N) (hst : s ≠ t) (f : N → N → ℝ) (v : ℝ)
    (hf : IsFlow G s t f v) (hmax : ∀ g w, IsFlow G s t g w → w ≤ v) : t ∉ sourceSet G f s := by
  intro ht
  obtain ⟨l, hl⟩ := g69e_simple (g69e_sourceSet_reach G f s ht)
  obtain ⟨ε, hε, hl'⟩ := g69e_res_exists G f s hl
  obtain ⟨g, hg, -⟩ := g69e_augment_flow G s t hst f v hf ε hε hl'
  have := hmax _ _ hg
  linarith

theorem g69e_tight (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) (hf : IsFlow G s t f v)
    (Y : Finset N) (hs : s ∈ Y) (ht : t ∉ Y) (hv : cutCapacity G Y ≤ v) :
    (∀ p ∈ arcsBetween G Y Yᶜ, f p.1 p.2 = G.cap p.1 p.2) ∧
      (∀ p ∈ arcsBetween G Yᶜ Y, f p.1 p.2 = 0) := by
  have h41 := (g69e_flow41 G s t f v hf Y hs ht).1
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

theorem g69e_cut_eq (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) (hf : IsFlow G s t f v)
    (X : Finset N) (hs : s ∈ X) (ht : t ∉ X) (hX : ∀ u w, u ∈ X → AugStep G f u w → w ∈ X) :
    v = cutCapacity G X := by
  rw [(g69e_flow41 G s t f v hf X hs ht).1]
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

theorem g69e_max_cut (G : Network N) (s t : N) (hst : s ≠ t) (f : N → N → ℝ) (v : ℝ)
    (hf : IsFlow G s t f v) (hmax : ∀ g w, IsFlow G s t g w → w ≤ v) :
    t ∉ sourceSet G f s ∧ v = cutCapacity G (sourceSet G f s) := by
  have ht := g69e_max_not_mem G s t hst f v hf hmax
  exact ⟨ht, g69e_cut_eq G s t f v hf _ (g69e_sourceSet_s G f s) ht
    (fun u w hu huw => g69e_sourceSet_closed G f s hu huw)⟩

end g69e

theorem g69e_sinkSet_t {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ) (t : N) :
    t ∈ sinkSet G f t := by
  unfold sinkSet; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro Z ht _; exact ht

theorem g69e_sinkSet_closed {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ)
    (t : N) {x y : N} (hy : y ∈ sinkSet G f t) (hxy : AugStep G f x y) : x ∈ sinkSet G f t := by
  unfold sinkSet at *; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  intro Z ht hZ; exact hZ x y (hy Z ht hZ) hxy

theorem g69e_sinkSet_min {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ)
    (t : N) (Z : Finset N) (ht : t ∈ Z)
    (hZ : ∀ u w, w ∈ Z → AugStep G f u w → u ∈ Z) : sinkSet G f t ⊆ Z := by
  intro x hx; unfold sinkSet at hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx Z ht hZ

theorem g69e_sinkSet_reach {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ)
    (t : N) {x : N} (hx : x ∈ sinkSet G f t) : Relation.ReflTransGen (AugStep G f) x t := by
  classical
  have := g69e_sinkSet_min G f t (Finset.univ.filter (fun y => Relation.ReflTransGen (AugStep G f) y t))
    (by simpa using Relation.ReflTransGen.refl) (by
      intro u w hw huw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact Relation.ReflTransGen.head huw hw)
  simpa using this hx

theorem g69e_reach_contra {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (s t : N)
    (hst : s ≠ t) (f : N → N → ℝ) (v : ℝ)
    (hf : IsFlow G s t f v) (hmax : ∀ g w, IsFlow G s t g w → w ≤ v)
    (hr : Relation.ReflTransGen (AugStep G f) s t) : False := by
  obtain ⟨l, hl⟩ := g69e_simple hr
  obtain ⟨ε, hε, hl'⟩ := g69e_res_exists G f s hl
  obtain ⟨g, hg, -⟩ := g69e_augment_flow G s t hst f v hf ε hε hl'
  have := hmax _ _ hg
  linarith


/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Theorem 5.6 (p. 25): let `f` be a maximal
flow, `X = sourceSet G f s` the set of nodes defined in the proof of Theorem 5.1, `Ȳ = sinkSet G f t`
the set defined on p. 24 (so `Y` is its complement), and assume that `c` is strictly positive.
The minimal cut `(X, X̄)` is unique (every minimal cut has the same arc set) if and only if the
arc sets `(X, X̄)` and `(Y, Ȳ)` are equal. -/
theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t)
    (hc : ∀ p ∈ G.arcs, 0 < G.cap p.1 p.2)
    (f : N → N → ℝ) (hf : IsMaxFlow G s t f) :
    (∀ Z : Finset N, IsMinCut G s t Z →
        arcsBetween G Z Zᶜ = arcsBetween G (sourceSet G f s) (sourceSet G f s)ᶜ) ↔
      arcsBetween G (sourceSet G f s) (sourceSet G f s)ᶜ =
        arcsBetween G (sinkSet G f t)ᶜ (sinkSet G f t) := by
  obtain ⟨v, hfv, hmax⟩ := hf
  obtain ⟨htX, hvX⟩ := g69e_max_cut G s t hst f v hfv hmax
  set X := sourceSet G f s with hXdef
  set S' := sinkSet G f t with hS'def
  have hsS' : s ∉ S' := fun h => g69e_reach_contra G s t hst f v hfv hmax (g69e_sinkSet_reach G f t h)
  have hvY : v = cutCapacity G S'ᶜ := g69e_cut_eq G s t f v hfv S'ᶜ (by simpa using hsS')
    (by simpa using g69e_sinkSet_t G f t) (by
      intro u w hu huw
      simp only [Finset.mem_compl] at hu ⊢
      exact fun hw => hu (g69e_sinkSet_closed G f t hw huw))
  have hlow : ∀ Y : Finset N, s ∈ Y → t ∉ Y → v ≤ cutCapacity G Y := fun Y hs ht =>
    (g69e_flow41 G s t f v hfv Y hs ht).1 ▸ (g69e_flow41 G s t f v hfv Y hs ht).2
  constructor
  · intro h
    have hmin : IsMinCut G s t S'ᶜ := ⟨by simpa using hsS', by simpa using g69e_sinkSet_t G f t,
      fun Y hs ht => hvY ▸ hlow Y hs ht⟩
    have := h _ hmin
    rw [compl_compl] at this
    exact this.symm
  · intro hA Z hZ
    obtain ⟨hsZ, htZ, hZm⟩ := hZ
    have c1 := hZm _ (g69e_sourceSet_s G f s) htX
    obtain ⟨hsat, hfl⟩ := g69e_tight G s t f v hfv Z hsZ htZ (by linarith)
    have hZcl : ∀ u w, u ∈ Z → AugStep G f u w → w ∈ Z := by
      intro u w hu huw
      by_contra hw
      rcases huw with ⟨a, b⟩ | ⟨a, b⟩
      · have := hsat (u, w) (by simp [arcsBetween, a, hu, hw]); simp only at this; linarith
      · have := hfl (w, u) (by simp [arcsBetween, a, hu, hw]); simp only at this; linarith
    have hXZ : X ⊆ Z := g69e_sourceSet_min G f s Z hsZ hZcl
    have hS'Z : S' ⊆ Zᶜ := g69e_sinkSet_min G f t Zᶜ (by simpa using htZ) (by
      intro u w hw huw
      simp only [Finset.mem_compl] at hw ⊢
      exact fun hu => hw (hZcl u w hu huw))
    ext p
    simp only [arcsBetween, Finset.mem_filter, Finset.mem_compl]
    constructor
    · rintro ⟨hp, h1, h2⟩
      have h2X : p.2 ∉ X := fun h => h2 (hXZ h)
      refine ⟨hp, ?_, h2X⟩
      by_contra h1X
      have h1S : p.1 ∉ S' := fun h => by have := hS'Z h; simp at this; exact this h1
      by_cases h2S : p.2 ∈ S'
      · have : p ∈ arcsBetween G S'ᶜ S' := by simp [arcsBetween, hp, h1S, h2S]
        rw [← hA] at this
        simp [arcsBetween] at this
        exact h1X this.2.1
      · -- U = Z \ X \ S'
        set U := Z.filter (fun x => x ∉ X ∧ x ∉ S') with hU
        have hsum := g69e_sum_netFlowOut G f U
        have hzero : ∑ x ∈ U, netFlowOut G f x = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          simp only [hU, Finset.mem_filter] at hx
          exact hfv.2.2.2.2.2 x (fun e => hx.2.1 (e ▸ g69e_sourceSet_s G f s))
            (fun e => hx.2.2 (e ▸ g69e_sinkSet_t G f t))
        have hin : arcSum G f Uᶜ U = 0 := by
          apply Finset.sum_eq_zero
          intro q hq
          simp only [arcsBetween, Finset.mem_filter, Finset.mem_compl, hU] at hq
          obtain ⟨hq, hq1, ⟨hq2Z, hq2X, hq2S⟩⟩ := hq
          by_contra hne
          have hpos : 0 < f q.1 q.2 := lt_of_le_of_ne (hfv.2.1 q hq) (Ne.symm hne)
          by_cases hq1X : q.1 ∈ X
          · have : q ∈ arcsBetween G X Xᶜ := by simp [arcsBetween, hq, hq1X, hq2X]
            rw [hA] at this
            simp [arcsBetween] at this
            exact hq2S this.2.2
          by_cases hq1S : q.1 ∈ S'
          · exact hq2S (g69e_sinkSet_closed G f t hq1S (Or.inr ⟨hq, hpos⟩))
          have hq1Z : q.1 ∉ Z := fun h => hq1 ⟨h, hq1X, hq1S⟩
          exact hq1Z (hZcl q.2 q.1 hq2Z (Or.inr ⟨hq, hpos⟩))
        have hout : arcSum G f U Uᶜ = 0 := by linarith
        unfold arcSum at hout
        have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun q hq => hfv.2.1 q
          (Finset.mem_filter.1 hq).1)).1 hout p (by
            simp [arcsBetween, hp, hU, h1, h1X, h1S, h2])
        have hfc : f p.1 p.2 = G.cap p.1 p.2 := hsat p (by simp [arcsBetween, hp, h1, h2])
        have := hc p hp
        linarith
    · rintro ⟨hp, h1, h2⟩
      refine ⟨hp, hXZ h1, ?_⟩
      have : p ∈ arcsBetween G X Xᶜ := by simp [arcsBetween, hp, h1, h2]
      rw [hA] at this
      simp [arcsBetween] at this
      have := hS'Z this.2.2
      simpa using this

