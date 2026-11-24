-- Prove2me | solution 1 for DetANN.Thm11.outer_det
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-23T21:58:44.926024+00:00
-- url     : https://prove2.me/submissions/10f6f7f2-fd49-4342-bcf1-b594049b09a9

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_Thm11_OuterProg
import Theorems.Thm_DetANN_reloc_detProgram

/-! The outer programs of Theorem 1.1 are deterministic programs (`outer_det`). Every instruction of the
outer main programs, of `pre`, `ev` and `zeroRegs` is checked to be admissible; the inner programs are
deterministic by hypothesis and stay so under relocation. -/

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.Supplement

/-- One admissible deterministic instruction. -/
def GoodI (op : Instr) : Prop :=
  (match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True) ∧ (∀ r, op ≠ .coin r) ∧ (∀ r a e, op ≠ .rpow r a e)

lemma det_of_goodI {P : Program} (h : ∀ op ∈ P, GoodI op) : DetProgram P :=
  ⟨fun op hop => (h op hop).1, fun op hop => (h op hop).2⟩

lemma det_app {A B : Program} (hA : DetProgram A) (hB : DetProgram B) : DetProgram (A ++ B) := by
  refine ⟨fun op hop => ?_, fun op hop => ?_⟩
  · rcases List.mem_append.1 hop with h | h
    · exact hA.1 op h
    · exact hB.1 op h
  · rcases List.mem_append.1 hop with h | h
    · exact hA.2 op h
    · exact hB.2 op h

lemma det_fw (off : ℕ) : DetProgram (fw off) := by
  apply det_of_goodI
  intro op hop
  unfold fw at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals trivial

lemma det_evA (off : ℕ) : DetProgram (evA off) := by
  apply det_of_goodI
  intro op hop
  unfold evA at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨1, ?_⟩; norm_num; done)

lemma det_evB (off : ℕ) : DetProgram (evB off) := by
  apply det_of_goodI
  intro op hop
  unfold evB at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals trivial

lemma det_ev (off : ℕ) : DetProgram (ev off) := by
  unfold ev; exact det_app (det_app (det_evA off) (det_fw _)) (det_evB off)

section PreDet

variable (q : ℚ) (off : ℕ)

lemma det_preA : DetProgram (preA q off) := by
  apply det_of_goodI; intro op hop; unfold preA at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨q, rfl⟩
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨-1, ?_⟩; norm_num; done)

lemma det_preB0 : DetProgram (preB0 q off) := by
  apply det_of_goodI; intro op hop; unfold preB0 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨q, rfl⟩
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨-1, ?_⟩; norm_num; done)

lemma det_preB1 : DetProgram (preB1 q off) := by
  apply det_of_goodI; intro op hop; unfold preB1 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨q, rfl⟩
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨-1, ?_⟩; norm_num; done)

lemma det_preB2 : DetProgram (preB2 q off) := by
  apply det_of_goodI; intro op hop; unfold preB2 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨q, rfl⟩
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨-1, ?_⟩; norm_num; done)

lemma det_preB3 : DetProgram (preB3 q off) := by
  apply det_of_goodI; intro op hop; unfold preB3 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨q, rfl⟩
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨-1, ?_⟩; norm_num; done)

lemma det_preB4 : DetProgram (preB4 q off) := by
  apply det_of_goodI; intro op hop; unfold preB4 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨q, rfl⟩
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨-1, ?_⟩; norm_num; done)

lemma det_preB5 : DetProgram (preB5 q off) := by
  apply det_of_goodI; intro op hop; unfold preB5 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨q, rfl⟩
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨-1, ?_⟩; norm_num; done)

lemma det_preB6 : DetProgram (preB6 q off) := by
  apply det_of_goodI; intro op hop; unfold preB6 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨q, rfl⟩
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨-1, ?_⟩; norm_num; done)

lemma det_pre : DetProgram (pre q off) := by
  unfold pre
  exact det_app (det_app (det_preA q off) (det_fw _))
    (det_app (det_app (det_app (det_app (det_app (det_app (det_preB0 q off) (det_preB1 q off))
      (det_preB2 q off)) (det_preB3 q off)) (det_preB4 q off)) (det_preB5 q off)) (det_preB6 q off))

end PreDet

end DetANN.Supplement.Thm32

namespace DetANN.Thm11

open PNormReg PNormRegLib DetANN DetANN.Supplement.Thm32

lemma det_zeroRegs (r q a b : ℕ) : DetProgram (zeroRegs r q a b) := by
  apply det_of_goodI; intro op hop
  simp only [zeroRegs, List.mem_append, List.mem_map, List.mem_range] at hop
  rcases hop with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩
  · exact ⟨⟨0, by norm_num⟩, (fun r h => by cases h), (fun r a e h => by cases h)⟩
  · exact ⟨trivial, (fun r h => by cases h), (fun r a e h => by cases h)⟩

lemma det_opre0 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre0 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre0, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre1 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre1 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre1, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre2 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre2 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre2, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre3 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre3 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre3, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre4 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre4 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre4, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre5 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre5 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre5, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre6 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre6 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre6, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre7 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre7 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre7, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre8 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre8 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre8, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre9 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre9 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre9, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre10 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre10 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre10, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre11 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre11 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre11, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_opre12 (c0 Cb K Cp X3 : ℕ) : DetProgram (opre12 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [opre12, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_outerPreMain (c0 Cb K Cp X3 : ℕ) : DetProgram (outerPreMain c0 Cb K Cp X3) := by
  unfold outerPreMain
  exact det_app (det_app (det_app (det_app (det_app (det_app (det_app (det_app (det_app (det_app (det_app (det_app (det_app (det_app ((det_opre0 c0 Cb K Cp X3)) (det_opre1 c0 Cb K Cp X3)) (det_opre2 c0 Cb K Cp X3)) (det_opre3 c0 Cb K Cp X3)) (det_opre4 c0 Cb K Cp X3)) (det_opre5 c0 Cb K Cp X3)) (det_opre6 c0 Cb K Cp X3)) (det_opre7 c0 Cb K Cp X3)) (det_opre8 c0 Cb K Cp X3)) (reloc_detProgram _ _ (det_pre (c0 : ℚ) 0))) (det_opre9 c0 Cb K Cp X3)) (det_opre10 c0 Cb K Cp X3)) (reloc_detProgram _ _ (det_ev 0))) (det_opre11 c0 Cb K Cp X3)) (det_opre12 c0 Cb K Cp X3)

lemma det_oqry0 (c0 Cb K Cp X3 : ℕ) : DetProgram (oqry0 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [oqry0, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_oqry1 (c0 Cb K Cp X3 : ℕ) : DetProgram (oqry1 c0 Cb K Cp X3) := by
  apply det_of_goodI; intro op hop
  simp only [oqry1, List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | exact ⟨_, (Rat.cast_natCast _).symm⟩
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨1 / 8, ?_⟩; norm_num; done) | (refine ⟨1 / 100, ?_⟩; norm_num; done)
    | (refine ⟨1 / 200, ?_⟩; norm_num; done) | (refine ⟨1 / 1000000, ?_⟩; norm_num; done)

lemma det_outerQryMain (c0 Cb K Cp X3 : ℕ) : DetProgram (outerQryMain c0 Cb K Cp X3) := by
  unfold outerQryMain
  exact det_app (det_app ((det_oqry0 c0 Cb K Cp X3)) (reloc_detProgram _ _ (det_ev 0))) (det_oqry1 c0 Cb K Cp X3)

theorem outer_det_pf :
    ∀ (Pre₃ Qry₃ : Program) (n3 c0 Cb K Cp X3 : ℕ), DetProgram Pre₃ → DetProgram Qry₃ →
      DetProgram (outerPre Pre₃ n3 c0 Cb K Cp X3) ∧ DetProgram (outerQry Qry₃ n3 c0 Cb K Cp X3) := by
  intro Pre₃ Qry₃ n3 c0 Cb K Cp X3 h1 h2
  exact ⟨det_app (det_outerPreMain c0 Cb K Cp X3) (det_app (det_zeroRegs _ _ _ _) (reloc_detProgram _ _ h1)),
    det_app (det_outerQryMain c0 Cb K Cp X3) (det_app (det_zeroRegs _ _ _ _) (reloc_detProgram _ _ h2))⟩

end DetANN.Thm11

open PNormReg PNormRegLib DetANN in
theorem solution :
    ∀ (Pre₃ Qry₃ : Program) (n3 c0 Cb K Cp X3 : ℕ), DetProgram Pre₃ → DetProgram Qry₃ →
      DetProgram (DetANN.Thm11.outerPre Pre₃ n3 c0 Cb K Cp X3) ∧
        DetProgram (DetANN.Thm11.outerQry Qry₃ n3 c0 Cb K Cp X3) :=
  DetANN.Thm11.outer_det_pf
