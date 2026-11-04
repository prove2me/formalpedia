-- Prove2me | solution 1 for ContJRP.Align.lemma_2_5_misaligned_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:14:06.008707+00:00
-- url     : https://prove2.me/submissions/c875f16a-7bec-4de8-8af3-6210fe2a8162

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

open ContJRP.Align
open Classical

/-- For commensurable positive `x, y`, `alignMult x y · x = alignMult y x · y` (both sides are the
least common multiple). -/
theorem jrp25_alignMult (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℝ) * x = b * y) :
    (alignMult x y : ℝ) * x = (alignMult y x : ℝ) * y := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have hne1 : {a : ℕ | 0 < a ∧ ∃ b : ℕ, 0 < b ∧ (a : ℝ) * x = b * y}.Nonempty :=
    ⟨a, ha, b, hb, hab⟩
  have hne2 : {b : ℕ | 0 < b ∧ ∃ a : ℕ, 0 < a ∧ (b : ℝ) * y = a * x}.Nonempty :=
    ⟨b, hb, a, ha, hab.symm⟩
  have h1 := Nat.sInf_mem hne1
  have h2 := Nat.sInf_mem hne2
  unfold alignMult
  set a0 := sInf {a : ℕ | 0 < a ∧ ∃ b : ℕ, 0 < b ∧ (a : ℝ) * x = b * y}
  set b0 := sInf {b : ℕ | 0 < b ∧ ∃ a : ℕ, 0 < a ∧ (b : ℝ) * y = a * x}
  obtain ⟨-, b1, hb1, e1⟩ := h1
  obtain ⟨-, a1, ha1, e2⟩ := h2
  have hle1 : a0 ≤ a1 := Nat.sInf_le ⟨ha1, b0, Nat.pos_of_ne_zero (by
    intro hz; rw [hz] at e2; simp at e2; rcases e2 with e2 | e2 <;> [omega; linarith]), e2.symm⟩
  have hle2 : b0 ≤ b1 := Nat.sInf_le ⟨hb1, a0, Nat.pos_of_ne_zero (by
    intro hz; rw [hz] at e1; simp at e1; rcases e1 with e1 | e1 <;> [omega; linarith]), e1.symm⟩
  have i1 : (a0 : ℝ) * x ≤ (b0 : ℝ) * y := by
    rw [e2]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle1) hx.le
  have i2 : (b0 : ℝ) * y ≤ (a0 : ℝ) * x := by
    rw [e1]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle2) hy.le
  linarith

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar) :
    ∃ R : ℕ → ℝ, IsLPFeasible ε Tt Tstar Rstar R ∧ CrossMisaligned ε Tt Tstar Rstar R := by
  have hpos : ∀ ℓ ∈ active ε Tt Tstar, 0 < Rstar ℓ := by
    intro ℓ hℓ
    obtain ⟨i, hi, -⟩ := hR ℓ hℓ
    rw [hi]; exact hTstar i
  refine ⟨Rstar, ⟨?_, ?_⟩, ?_⟩
  · -- constraint (A)
    intro ℓ hℓ
    obtain ⟨i, hi, hseg⟩ := hR ℓ hℓ
    rw [hi]
    exact Set.Ico_subset_Icc_self hseg
  · -- constraint (B)
    intro ℓ₁ h1 ℓ₂ h2 hadj
    unfold alignGraph at hadj
    rw [SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, hr | hr⟩ := hadj
    · obtain ⟨-, -, a, b, ha, -, hb, -, hab⟩ := hr
      exact jrp25_alignMult _ _ (hpos ℓ₁ h1) (hpos ℓ₂ h2) ⟨a, b, ha, hb, hab⟩
    · obtain ⟨-, -, a, b, ha, -, hb, -, hab⟩ := hr
      exact jrp25_alignMult _ _ (hpos ℓ₁ h1) (hpos ℓ₂ h2) ⟨b, a, hb, ha, hab.symm⟩
  · -- cross-component misalignment
    intro ℓ₁ h1 ℓ₂ h2 hnr a b ha haΨ hb hbΨ hab
    apply hnr
    have hne : ℓ₁ ≠ ℓ₂ := by
      intro e; rw [e] at hnr; exact hnr (SimpleGraph.Reachable.refl _)
    apply SimpleGraph.Adj.reachable
    unfold alignGraph
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl ⟨h1, h2, a, b, ha, haΨ, hb, hbΨ, hab⟩⟩
