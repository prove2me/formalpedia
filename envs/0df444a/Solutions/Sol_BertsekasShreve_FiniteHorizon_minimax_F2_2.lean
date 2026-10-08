-- Prove2me | solution 2 for BertsekasShreve.FiniteHorizon.minimax_F2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:29:29.216987+00:00
-- url     : https://prove2.me/submissions/a5c2be47-5fc6-4aea-a62d-9382d3b519b7

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace MinimaxF2Aux

open BertsekasShreve.FiniteHorizon

theorem mul_add_real (α r : ℝ) (hα : 0 < α) (b : EReal) :
    (α : EReal) * (b + (r : EReal)) = (α : EReal) * b + ((α * r : ℝ) : EReal) := by
  induction b using EReal.rec with
  | bot =>
    rw [EReal.bot_add, EReal.coe_mul_bot_of_pos hα, EReal.bot_add]
  | top =>
    rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hα, EReal.top_add_coe]
  | coe b =>
    rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1; ring

theorem badd_add_le (a x : EReal) (c : ℝ) :
    badd a (x + (c : EReal)) ≤ badd a x + (c : EReal) := by
  unfold badd
  by_cases ha : a = ⊤
  · simp [ha]
  by_cases hx : x = ⊤
  · simp [hx]
  have hxc : x + (c : EReal) ≠ ⊤ := by
    induction x using EReal.rec with
    | bot => simp
    | top => exact absurd rfl hx
    | coe x => exact (EReal.coe_add x c ▸ EReal.coe_ne_top _)
  simp only [ha, hx, hxc, or_self, if_false]
  rw [add_assoc]

end MinimaxF2Aux

open BertsekasShreve.FiniteHorizon BertsekasShreve.FiniteHorizon.Model in
theorem solution {S C W : Type*} (m : Model S C) (Wset : S → C → Set W)
    (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α)
    (hW : ∀ x, ∀ u ∈ m.U x, (Wset x u).Nonempty)
    (hH : m.H = minimaxH Wset g f α) :
    m.F2With α := by
  intro r hr J x u hu
  refine ⟨m.mono x u hu _ _ ?_, ?_⟩
  · intro y
    exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr hr.le)
  · rw [hH]
    unfold minimaxH
    refine iSup₂_le fun w hw => ?_
    rw [MinimaxF2Aux.mul_add_real α r hα]
    refine (MinimaxF2Aux.badd_add_le _ _ _).trans ?_
    gcongr
    exact le_iSup₂ (f := fun w (_ : w ∈ Wset x u) => badd (g x u w) ((α : EReal) * J (f x u w))) w hw
