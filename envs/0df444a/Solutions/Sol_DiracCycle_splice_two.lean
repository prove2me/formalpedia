-- Prove2me | solution 1 for DiracCycle.splice_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:55:13.88661+00:00
-- url     : https://prove2.me/submissions/f6cc003b-237f-449e-a53b-c115218d000e

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Theorems.Thm_DiracCycle_splice
public import Theorems.Thm_DiracCycle_isPath_reverse_append
public import Theorems.Thm_Hamiltonicity_CycArr_rotate
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}
namespace DiracCycle
theorem _root_.solution {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) {x : V} (hx : ∀ i, f i ≠ x)
    {a b : ℕ} (hab : a < b) (hbm : b < m) (P₁ : G.Walk x (f a)) (P₂ : G.Walk x (f b))
    (h₁ : P₁.IsPath) (h₂ : P₂.IsPath)
    (hC₁ : ∀ y ∈ P₁.support, ∀ i, f i = y → y = f a)
    (hC₂ : ∀ y ∈ P₂.support, ∀ i, f i = y → y = f b)
    (hdisj : ∀ y ∈ P₁.support, y ∈ P₂.support → y = x) :
    ∃ m' g, CycArr G m' g ∧ (∃ i, g i = x) ∧
      ∀ p < m, (p = 0 ∨ p ≤ a ∨ b ≤ p) → ∃ i, g i = f p := by
  have hR := hC.rotate a
  have hl₁ : 1 ≤ P₁.length := by
    rcases Nat.eq_zero_or_pos P₁.length with h | h
    · exact absurd (Walk.eq_of_length_eq_zero h).symm (hx a)
    · exact h
  have hl₂ : 1 ≤ P₂.length := by
    rcases Nat.eq_zero_or_pos P₂.length with h | h
    · exact absurd (Walk.eq_of_length_eq_zero h).symm (hx b)
    · exact h
  have e₀ : f a = f (a + 0) := rfl
  have e₁ : f b = f (a + (b - a)) := by rw [show a + (b - a) = b by omega]
  set Q := (P₁.reverse.append P₂).copy e₀ e₁ with hQ
  have hQs : ∀ y, y ∈ Q.support ↔ y ∈ P₁.support ∨ y ∈ P₂.support := by
    intro y
    rw [hQ, Walk.support_copy, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse]
  obtain ⟨m', g, hg, hgQ, hgarc⟩ := splice hR (d := b - a) (by omega) (by omega) Q
    (by rw [hQ, Walk.isPath_copy]; exact isPath_reverse_append P₁ P₂ h₁ h₂ hdisj)
    (by rw [hQ, Walk.length_copy, Walk.length_append, Walk.length_reverse]; omega)
    (by
      intro y hy i hi
      rcases (hQs y).1 hy with hy | hy
      · exact Or.inl (hC₁ y hy (a + i) hi)
      · exact Or.inr ((hC₂ y hy (a + i) hi).trans e₁))
  refine ⟨m', g, hg, hgQ x ((hQs x).2 (Or.inl P₁.start_mem_support)), ?_⟩
  intro p hp hcase
  rcases hcase with h0 | hpa | hbp
  · obtain ⟨j, hj⟩ := hgarc (m - a) (by omega) (by omega)
    refine ⟨j, hj.trans ?_⟩
    rw [h0, show a + (m - a) = 0 + m by omega, hC.periodic]
  · obtain ⟨j, hj⟩ := hgarc (p + m - a) (by omega) (by omega)
    refine ⟨j, hj.trans ?_⟩
    rw [show a + (p + m - a) = p + m by omega, hC.periodic]
  · obtain ⟨j, hj⟩ := hgarc (p - a) (by omega) (by omega)
    refine ⟨j, hj.trans ?_⟩
    rw [show a + (p - a) = p by omega]
end DiracCycle
