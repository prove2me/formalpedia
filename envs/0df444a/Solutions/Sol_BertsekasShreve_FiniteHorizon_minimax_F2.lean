-- Prove2me | solution 1 for BertsekasShreve.FiniteHorizon.minimax_F2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T22:23:40.290985+00:00
-- url     : https://prove2.me/submissions/54dbdc68-f4ae-41d1-a415-af6b9d09bda0

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels



namespace BertsekasShreve.FiniteHorizon

open Model

namespace MMAux

theorem mul_add_coe (α r : ℝ) (hα : 0 < α) (J : EReal) :
    (α : EReal) * (J + (r : EReal)) = (α : EReal) * J + ((α * r : ℝ) : EReal) := by
  induction J using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hα]
  | top => rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hα, EReal.top_add_coe]
  | coe a =>
    rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1; ring

theorem badd_mono (a : EReal) {b b' : EReal} (h : b ≤ b') : badd a b ≤ badd a b' := by
  unfold badd
  by_cases h1 : a = ⊤ ∨ b' = ⊤
  · rw [if_pos h1]; exact le_top
  · rw [if_neg h1]
    have h2 : ¬ (a = ⊤ ∨ b = ⊤) := by
      rintro (h3 | h3)
      · exact h1 (Or.inl h3)
      · exact h1 (Or.inr (top_le_iff.1 (h3 ▸ h)))
    rw [if_neg h2]
    exact add_le_add le_rfl h

theorem badd_add (a b : EReal) (c : ℝ) : badd a (b + (c : EReal)) ≤ badd a b + (c : EReal) := by
  unfold badd
  by_cases h1 : a = ⊤ ∨ b = ⊤
  · rw [if_pos h1]
    rcases h1 with h | h
    · rw [if_pos (Or.inl h)]; simp
    · subst h; simp
  · rw [if_neg h1]
    by_cases h2 : a = ⊤ ∨ b + (c : EReal) = ⊤
    · rw [if_pos h2]
      exfalso
      rcases h2 with h | h
      · exact h1 (Or.inl h)
      · apply h1; right
        induction b using EReal.rec with
        | bot => simp at h
        | top => rfl
        | coe x => exact absurd h (by rw [← EReal.coe_add]; exact EReal.coe_ne_top _)
    · rw [if_neg h2, add_assoc]

end MMAux

theorem minimax_F2_core {S C W : Type*} (m : Model S C) (Wset : S → C → Set W)
    (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α)
    (hH : m.H = minimaxH Wset g f α) :
    m.F2With α := by
  intro r hr J x u _
  rw [hH]
  simp only [minimaxH]
  constructor
  · refine iSup₂_mono fun w _ => MMAux.badd_mono _ ?_
    rw [MMAux.mul_add_coe α r hα]
    exact le_add_of_nonneg_right (EReal.coe_nonneg.2 (by positivity))
  · refine iSup₂_le fun w hw => ?_
    rw [MMAux.mul_add_coe α r hα]
    refine (MMAux.badd_add _ _ _).trans ?_
    exact add_le_add (le_iSup₂ (f := fun w _ => badd (g x u w) ((α : EReal) * J (f x u w))) w hw) le_rfl

end BertsekasShreve.FiniteHorizon

open BertsekasShreve.FiniteHorizon
open Model

theorem solution {S C W : Type*} (m : Model S C) (Wset : S → C → Set W)
    (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α)
    (hW : ∀ x, ∀ u ∈ m.U x, (Wset x u).Nonempty)
    (hH : m.H = minimaxH Wset g f α) :
    m.F2With α := by
  exact minimax_F2_core m Wset g f α hα hH
