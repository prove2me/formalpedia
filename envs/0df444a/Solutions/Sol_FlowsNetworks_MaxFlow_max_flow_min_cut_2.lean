-- Prove2me | solution 2 for FlowsNetworks.MaxFlow.max_flow_min_cut
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:28:34.440994+00:00
-- url     : https://prove2.me/submissions/bc42ac42-3a69-44cd-adcb-426c62f2e27f

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network
import Theorems.Thm_FlowsNetworks_MaxFlow_flow_value_eq_net_flow_across_cut

-- carved verbatim out of submission 06929ca8-3dd4-46ef-acfe-ab08ed7de6b8, lines 448-461

section
open FlowsNetworks.MaxFlow

def g69e_AugStep {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ) (x y : N) : Prop :=
  ((x, y) ∈ G.arcs ∧ f x y < G.cap x y) ∨ ((y, x) ∈ G.arcs ∧ 0 < f y x)

noncomputable def g69e_sourceSet {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ) (s : N) : Finset N := by
  classical
  exact Finset.univ.filter (fun x => ∀ Z : Finset N, s ∈ Z →
    (∀ u w, u ∈ Z → g69e_AugStep G f u w → w ∈ Z) → x ∈ Z)

end

section
open FlowsNetworks.MaxFlow
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

theorem g69e_sourceSet_s (G : Network N) (f : N → N → ℝ) (s : N) : s ∈ g69e_sourceSet G f s := by
  unfold g69e_sourceSet; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro Z hs _; exact hs

theorem g69e_sourceSet_closed (G : Network N) (f : N → N → ℝ) (s : N) {x y : N}
    (hx : x ∈ g69e_sourceSet G f s) (hxy : g69e_AugStep G f x y) : y ∈ g69e_sourceSet G f s := by
  unfold g69e_sourceSet at *; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  intro Z hs hZ; exact hZ x y (hx Z hs hZ) hxy

theorem g69e_sourceSet_min (G : Network N) (f : N → N → ℝ) (s : N) (Z : Finset N) (hs : s ∈ Z)
    (hZ : ∀ u w, u ∈ Z → g69e_AugStep G f u w → w ∈ Z) : g69e_sourceSet G f s ⊆ Z := by
  intro x hx; unfold g69e_sourceSet at hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx Z hs hZ

theorem g69e_sourceSet_reach (G : Network N) (f : N → N → ℝ) (s : N) {x : N}
    (hx : x ∈ g69e_sourceSet G f s) : Relation.ReflTransGen (g69e_AugStep G f) s x := by
  classical
  have := g69e_sourceSet_min G f s (Finset.univ.filter (fun y => Relation.ReflTransGen (g69e_AugStep G f) s y))
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
    (h : Relation.ReflTransGen (g69e_Step (g69e_AugStep G f)) (s, [s]) (x, l)) :
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
    (hf : IsFlow G s t f v) (hmax : ∀ g w, IsFlow G s t g w → w ≤ v) : t ∉ g69e_sourceSet G f s := by
  intro ht
  obtain ⟨l, hl⟩ := g69e_simple (g69e_sourceSet_reach G f s ht)
  obtain ⟨ε, hε, hl'⟩ := g69e_res_exists G f s hl
  obtain ⟨g, hg, -⟩ := g69e_augment_flow G s t hst f v hf ε hε hl'
  have := hmax _ _ hg
  linarith

theorem g69e_cut_eq (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) (hf : IsFlow G s t f v)
    (X : Finset N) (hs : s ∈ X) (ht : t ∉ X) (hX : ∀ u w, u ∈ X → g69e_AugStep G f u w → w ∈ X) :
    v = cutCapacity G X := by
  rw [(FlowsNetworks.MaxFlow.flow_value_eq_net_flow_across_cut G s t f v hf X hs ht).1]
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
    t ∉ g69e_sourceSet G f s ∧ v = cutCapacity G (g69e_sourceSet G f s) := by
  have ht := g69e_max_not_mem G s t hst f v hf hmax
  exact ⟨ht, g69e_cut_eq G s t f v hf _ (g69e_sourceSet_s G f s) ht
    (fun u w hu huw => g69e_sourceSet_closed G f s hu huw)⟩

end

section
open FlowsNetworks.MaxFlow

theorem g69e_zero_flow {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (s t : N) :
    IsFlow G s t 0 0 := by
  refine ⟨fun _ _ _ => rfl, fun p _ => le_rfl, fun p hp => G.cap_nonneg p hp, ?_, ?_, ?_⟩ <;>
    simp [netFlowOut]

theorem g69e_exists_max {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (s t : N) :
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
    simp only [hF, Set.ofPred_and, Set.ofPred_forall]
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
  have hne : F.Nonempty := ⟨0, (hmem 0 0 (g69e_zero_flow G s t)).1⟩
  obtain ⟨f0, hf0, hmax⟩ := hcpt.exists_isMaxOn hne (hcont s).continuousOn
  refine ⟨f0, _, hmem' f0 hf0, fun g w hg => ?_⟩
  obtain ⟨hgF, rfl⟩ := hmem g w hg
  exact hmax hgF

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) :
    ∃ v : ℝ,
      IsGreatest {w : ℝ | ∃ f : N → N → ℝ, IsFlow G s t f w} v ∧
      IsLeast {κ : ℝ | ∃ X : Finset N, s ∈ X ∧ t ∉ X ∧ κ = cutCapacity G X} v := by
  obtain ⟨f, v, hf, hmax⟩ := g69e_exists_max G s t
  obtain ⟨ht, hv⟩ := g69e_max_cut G s t hst f v hf hmax
  refine ⟨v, ⟨⟨f, hf⟩, fun w ⟨g, hg⟩ => hmax g w hg⟩,
    ⟨⟨g69e_sourceSet G f s, g69e_sourceSet_s G f s, ht, hv⟩, ?_⟩⟩
  rintro κ ⟨X, hs, htX, rfl⟩
  have := FlowsNetworks.MaxFlow.flow_value_eq_net_flow_across_cut G s t f v hf X hs htX
  linarith [this.1, this.2]

end
