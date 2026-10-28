-- Prove2me | solution 2 for FlowsNetworks.MultiTerminal.realizability_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:37.623827+00:00
-- url     : https://prove2.me/submissions/dc11a094-e755-4f3d-891c-d76ab07e0b4e

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_UndirectedNetwork
import Theorems.Thm_FlowsNetworks_MultiTerminal_flow_function_triangle

-- carved verbatim out of submission 3382cc00-d810-4672-bd8c-0f97a3d9227e, lines 1024-1039

section

namespace g70fn2_MF

structure Network (N : Type) [Fintype N] [DecidableEq N] where
  arcs : Finset (N × N)
  loopless : ∀ p ∈ arcs, p.1 ≠ p.2
  cap : N → N → ℝ
  cap_nonneg : ∀ p ∈ arcs, 0 ≤ cap p.1 p.2

end g70fn2_MF

end

section
variable {N : Type} [Fintype N] [DecidableEq N]

namespace g70fn2_MF

def netFlowOut (G : Network N) (f : N → N → ℝ) (x : N) : ℝ :=
  (∑ p ∈ G.arcs.filter (fun p => p.1 = x), f p.1 p.2) -
    ∑ p ∈ G.arcs.filter (fun p => p.2 = x), f p.1 p.2

end g70fn2_MF

namespace g70fn2_MF

def Conservation (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) : Prop :=
  netFlowOut G f s = v ∧ netFlowOut G f t = -v ∧
    ∀ x, x ≠ s → x ≠ t → netFlowOut G f x = 0

end g70fn2_MF

namespace g70fn2_MF

def SupportedOnArcs (G : Network N) (f : N → N → ℝ) : Prop :=
  ∀ x y, (x, y) ∉ G.arcs → f x y = 0

end g70fn2_MF

namespace g70fn2_MF

def IsFlow (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) : Prop :=
  SupportedOnArcs G f ∧ (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2) ∧
    (∀ p ∈ G.arcs, f p.1 p.2 ≤ G.cap p.1 p.2) ∧ Conservation G s t f v

end g70fn2_MF

end

section
open FlowsNetworks.MultiTerminal
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

end

section
open FlowsNetworks.MultiTerminal
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

end

section
open FlowsNetworks.MultiTerminal
set_option linter.unusedSectionVars false
variable {N : Type} [Fintype N] [DecidableEq N]

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
    fun ⟨G, hG⟩ x y z h1 h2 h3 => FlowsNetworks.MultiTerminal.flow_function_triangle G v hG x y z h1 h2 h3
  exact ⟨⟨fwd, fun h => (back h).imp fun T hT => hT.2⟩, fun h => back (fwd h)⟩

end
