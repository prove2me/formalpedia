-- Prove2me | solution 1 for CombOpt.HeldKarp.subtourFeasible_iff_insideFeasible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T16:33:23.123957+00:00
-- url     : https://prove2.me/submissions/fb2a9651-b7dd-4913-b829-d11c188f9f7a

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_SubtourFeasible
import Definitions.Def_CombOpt_HeldKarp_Graph_InsideFeasible

set_option autoImplicit false

namespace CombOpt.HeldKarp.E2

open CombOpt.HeldKarp

theorem ends_eq {V E : Type*} (G : CombOpt.HeldKarp.Graph V E) (e : E) :
    ∃ a b, G.ends e = s(a, b) :=
  Sym2.ind (f := fun z => ∃ a b, z = s(a, b)) (fun a b => ⟨a, b, rfl⟩) (G.ends e)

theorem mem_cut_iff {V E : Type*} [Fintype E] (G : CombOpt.HeldKarp.Graph V E) (A : Finset V)
    (e : E) (a b : V) (hab : G.ends e = s(a, b)) :
    e ∈ G.cut A ↔ (a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A) := by
  classical
  simp only [Graph.cut, Finset.mem_filter, Finset.mem_univ, true_and, hab, Sym2.mem_iff]
  constructor
  · rintro ⟨⟨c, hc, hcA⟩, ⟨d, hd, hdA⟩⟩
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> tauto
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨⟨a, Or.inl rfl, h1⟩, ⟨b, Or.inr rfl, h2⟩⟩
    · exact ⟨⟨b, Or.inr rfl, h2⟩, ⟨a, Or.inl rfl, h1⟩⟩

theorem mem_gamma_iff {V E : Type*} [Fintype E] (G : CombOpt.HeldKarp.Graph V E) (S : Finset V)
    (e : E) (a b : V) (hab : G.ends e = s(a, b)) :
    e ∈ G.gamma S ↔ a ∈ S ∧ b ∈ S := by
  classical
  simp only [Graph.gamma, Finset.mem_filter, Finset.mem_univ, true_and, hab, Sym2.mem_iff]
  constructor
  · intro h; exact ⟨h a (Or.inl rfl), h b (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ c (rfl | rfl) <;> assumption

theorem cut_compl {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (G : CombOpt.HeldKarp.Graph V E) (A : Finset V) :
    G.cut (Finset.univ \ A) = G.cut A := by
  ext e
  obtain ⟨a, b, hab⟩ := ends_eq G e
  rw [mem_cut_iff G _ e a b hab, mem_cut_iff G _ e a b hab]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
  tauto

open Classical in
theorem edge_count {V E : Type*} [Fintype E] [DecidableEq V] (G : CombOpt.HeldKarp.Graph V E)
    (S : Finset V) (e : E) (hl : ∀ u, G.ends e = s(u, u) → u ∉ S) (c : ℝ) :
    (∑ v ∈ S, if e ∈ G.cut {v} then c else 0) =
      2 * (if e ∈ G.gamma S then c else 0) + (if e ∈ G.cut S then c else 0) := by
  classical
  obtain ⟨a, b, hab⟩ := ends_eq G e
  have h1 : ∀ v, e ∈ G.cut {v} ↔ (a = v ∨ b = v) ∧ a ≠ b := by
    intro v
    rw [mem_cut_iff G _ e a b hab]
    simp only [Finset.mem_singleton]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · subst h1; exact ⟨Or.inl rfl, fun h => h2 h.symm⟩
      · subst h2; exact ⟨Or.inr rfl, h1⟩
    · rintro ⟨h | h, hne⟩
      · subst h; exact Or.inl ⟨rfl, fun h => hne h.symm⟩
      · subst h; exact Or.inr ⟨hne, rfl⟩
  simp only [h1, mem_gamma_iff G S e a b hab, mem_cut_iff G S e a b hab]
  by_cases hab' : a = b
  · subst hab'
    have ha : a ∉ S := hl a hab
    simp [ha]
  · have hsum : ∀ v ∈ S, (if (a = v ∨ b = v) ∧ a ≠ b then c else 0) =
        (if a = v then c else 0) + (if b = v then c else 0) := by
      intro v _
      by_cases hv : a = v
      · subst hv; simp [hab', Ne.symm hab']
      · by_cases hw : b = v
        · subst hw; simp [hv, hab']
        · simp [hv, hw]
    rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb] <;> ring

open Classical in
/-- Σ_{v ∈ S} x(δ(v)) = 2 x(γ(S)) + x(δ(S)) when no loop sits at a node of `S`. -/
theorem degree_sum {V E : Type*} [Fintype E] [DecidableEq V] (G : CombOpt.HeldKarp.Graph V E)
    (S : Finset V) (hl : ∀ e u, G.ends e = s(u, u) → u ∉ S) (x : E → ℝ) :
    ∑ v ∈ S, ∑ e ∈ G.cut {v}, x e = 2 * ∑ e ∈ G.gamma S, x e + ∑ e ∈ G.cut S, x e := by
  classical
  have hf : ∀ (A : Finset E), ∑ e ∈ A, x e = ∑ e, if e ∈ A then x e else 0 := by
    intro A
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [hf]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun e _ => edge_count G S e (hl e) (x e))

theorem no_loop {V E : Type*} (G : CombOpt.HeldKarp.Graph V E) (v₁ : V)
    (hG : ∀ (e : E) (u : V), G.ends e = s(u, u) → u = v₁) (S : Finset V) (h1 : v₁ ∉ S) :
    ∀ e u, G.ends e = s(u, u) → u ∉ S := by
  intro e u h hu
  exact h1 (hG e u h ▸ hu)

end CombOpt.HeldKarp.E2

open CombOpt.HeldKarp in
theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : CombOpt.HeldKarp.Graph V E) (v₁ : V) (hG : ∀ (e : E) (u : V), G.ends e = s(u, u) → u = v₁) (x : E → ℝ) :
    G.SubtourFeasible x ↔ G.InsideFeasible v₁ x := by
  classical
  constructor
  · rintro ⟨hdeg, hsub, hbd⟩
    -- inside form for any nonempty `S` avoiding `v₁`
    have key : ∀ S : Finset V, v₁ ∉ S →
        2 * (S.card : ℝ) = 2 * ∑ e ∈ G.gamma S, x e + ∑ e ∈ G.cut S, x e := by
      intro S hS
      rw [← CombOpt.HeldKarp.E2.degree_sum G S (CombOpt.HeldKarp.E2.no_loop G v₁ hG S hS) x]
      simp [hdeg, mul_comm]
    refine ⟨hdeg, ?_, ?_, hbd⟩
    · intro S hne hS
      have hS' : S ≠ Finset.univ := fun h => hS (h ▸ Finset.mem_univ v₁)
      have := hsub S hne hS'
      have := key S hS
      linarith
    · have hS : v₁ ∉ Finset.univ.erase v₁ := Finset.notMem_erase v₁ _
      have hk := key _ hS
      have hc : G.cut (Finset.univ.erase v₁) = G.cut {v₁} := by
        rw [← CombOpt.HeldKarp.E2.cut_compl G {v₁}]
        congr 1
        ext v; simp
      rw [hc, hdeg v₁, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hk
      have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v₁⟩
      push_cast [Nat.cast_sub hpos] at hk
      linarith
  · rintro ⟨hdeg, hin, _, hbd⟩
    have key : ∀ S : Finset V, S.Nonempty → v₁ ∉ S → 2 ≤ ∑ e ∈ G.cut S, x e := by
      intro S hne hS
      have h := CombOpt.HeldKarp.E2.degree_sum G S (CombOpt.HeldKarp.E2.no_loop G v₁ hG S hS) x
      have h2 := hin S hne hS
      simp only [hdeg, Finset.sum_const, nsmul_eq_mul] at h
      linarith
    refine ⟨hdeg, ?_, hbd⟩
    intro S hne hSu
    by_cases hS : v₁ ∈ S
    · have hT : (Finset.univ \ S).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
        exact fun h => hSu (Finset.eq_univ_of_forall fun v => h (Finset.mem_univ v))
      have := key _ hT (fun h => (Finset.mem_sdiff.mp h).2 hS)
      rwa [CombOpt.HeldKarp.E2.cut_compl] at this
    · exact key S hne hS
