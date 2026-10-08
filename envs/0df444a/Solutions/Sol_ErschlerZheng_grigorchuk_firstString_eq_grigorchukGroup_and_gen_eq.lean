-- Prove2me | solution 1 for ErschlerZheng.grigorchuk_firstString_eq_grigorchukGroup_and_gen_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T00:28:19.726979+00:00
-- url     : https://prove2.me/submissions/c144a99d-c4da-4f78-b51d-686f7d7eb1e4

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-! ### `a` and the generators -/

theorem shiftSeq_shiftSeq (ω : ℕ → Fin 3) (m k : ℕ) :
    shiftSeq (shiftSeq ω m) k = shiftSeq ω (k + m) := by
  funext j
  simp only [shiftSeq]
  congr 1
  omega

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# A1: `G_{(012)^∞}` is Garrido's Grigorchuk group, with (2.5)

`b = b_ω = c_{𝔰²ω} = d_{𝔰ω}`, `c = b_{𝔰ω} = c_ω = d_{𝔰²ω}`, `d = b_{𝔰²ω} = c_{𝔰ω} = d_ω` for
`ω = (012)^∞`, by induction on words (the string has period 3).
-/

open Garrido

namespace ErschlerZheng

namespace BridgeDev

open GrigBasic

theorem shift_three : shiftSeq firstString 3 = firstString := by
  funext n; apply Fin.ext; simp [shiftSeq, firstString]

theorem shift_one_one : shiftSeq (shiftSeq firstString 1) 1 = shiftSeq firstString 2 := by
  rw [shiftSeq_shiftSeq]

theorem shift_two_one : shiftSeq (shiftSeq firstString 2) 1 = firstString := by
  rw [shiftSeq_shiftSeq, shift_three]

theorem fs0 : firstString 0 = 0 := rfl
theorem fs1 : shiftSeq firstString 1 0 = 1 := rfl
theorem fs2 : shiftSeq firstString 2 0 = 2 := rfl

theorem funs_eq (w : List Bool) :
    (grigBFun w = genFun firstString .b w ∧ grigBFun w = genFun (shiftSeq firstString 2) .c w ∧
      grigBFun w = genFun (shiftSeq firstString 1) .d w) ∧
    (grigCFun w = genFun (shiftSeq firstString 1) .b w ∧ grigCFun w = genFun firstString .c w ∧
      grigCFun w = genFun (shiftSeq firstString 2) .d w) ∧
    (grigDFun w = genFun (shiftSeq firstString 2) .b w ∧
      grigDFun w = genFun (shiftSeq firstString 1) .c w ∧ grigDFun w = genFun firstString .d w) := by
  induction w with
  | nil => simp [grigBFun, grigCFun, grigDFun, genFun]
  | cons x w ih =>
    obtain ⟨⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩⟩ := ih
    cases x
    · simp [grigBFun, grigCFun, grigDFun, genFun, fs0, fs1, fs2, letterValue, BCD.killedBy]
    · simp only [grigBFun, grigCFun, grigDFun, genFun, shift_one_one, shift_two_one]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> congr 1

end BridgeDev

end ErschlerZheng
end

section
open Garrido
open ErschlerZheng
open BridgeDev in
theorem solution :
    grigorchuk firstString = Garrido.GrigorchukGroup ∧
      (Garrido.grigB = gen firstString .b ∧ Garrido.grigB = gen (shiftSeq firstString 2) .c ∧
        Garrido.grigB = gen (shiftSeq firstString 1) .d) ∧
      (Garrido.grigC = gen (shiftSeq firstString 1) .b ∧ Garrido.grigC = gen firstString .c ∧
        Garrido.grigC = gen (shiftSeq firstString 2) .d) ∧
      (Garrido.grigD = gen (shiftSeq firstString 2) .b ∧ Garrido.grigD = gen (shiftSeq firstString 1) .c ∧
        Garrido.grigD = gen firstString .d) := by
  have e : ∀ (σ : BinaryTreeAut) (τ : BinaryTreeAut), (∀ w, (σ : Equiv.Perm (List Bool)) w =
      (τ : Equiv.Perm (List Bool)) w) → σ = τ := fun σ τ h => Subtype.ext (Equiv.ext h)
  have hB1 : grigB = gen firstString .b := e _ _ fun w => (funs_eq w).1.1
  have hB2 : grigB = gen (shiftSeq firstString 2) .c := e _ _ fun w => (funs_eq w).1.2.1
  have hB3 : grigB = gen (shiftSeq firstString 1) .d := e _ _ fun w => (funs_eq w).1.2.2
  have hC1 : grigC = gen (shiftSeq firstString 1) .b := e _ _ fun w => (funs_eq w).2.1.1
  have hC2 : grigC = gen firstString .c := e _ _ fun w => (funs_eq w).2.1.2.1
  have hC3 : grigC = gen (shiftSeq firstString 2) .d := e _ _ fun w => (funs_eq w).2.1.2.2
  have hD1 : grigD = gen (shiftSeq firstString 2) .b := e _ _ fun w => (funs_eq w).2.2.1
  have hD2 : grigD = gen (shiftSeq firstString 1) .c := e _ _ fun w => (funs_eq w).2.2.2.1
  have hD3 : grigD = gen firstString .d := e _ _ fun w => (funs_eq w).2.2.2.2
  refine ⟨?_, ⟨hB1, hB2, hB3⟩, ⟨hC1, hC2, hC3⟩, ⟨hD1, hD2, hD3⟩⟩
  unfold grigorchuk GrigorchukGroup gens
  rw [← hB1, ← hC2, ← hD3]
end
