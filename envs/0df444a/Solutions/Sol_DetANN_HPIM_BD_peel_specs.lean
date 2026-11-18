-- Prove2me | solution 1 for DetANN.HPIM.BD.peel_specs
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T21:41:28.79521+00:00
-- url     : https://prove2.me/submissions/2613b95a-fee8-4009-b11e-b6ae6b4870ea

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMBSP
import Definitions.Def_DetANN_HPIMBalProg
import Definitions.Def_DetANN_HPIMBuildProg
import Definitions.Def_DetANN_HPIMBuild
import Theorems.Thm_DetANN_HPIM_BD_split_steps
import Theorems.Thm_DetANN_HPIM_BD_carve_steps
import Theorems.Thm_DetANN_HPIM_BD_loop_specs

namespace DetANN.HPIM.QP
end DetANN.HPIM.QP
namespace DetANN.HPIM
end DetANN.HPIM
namespace DetANN.HPIM.SegStep
end DetANN.HPIM.SegStep
namespace DetANN.HPIM.PP
end DetANN.HPIM.PP
namespace DetANN.HPIM.BS
end DetANN.HPIM.BS

-- ===== QP_Work =====
open PNormReg PNormRegLib SmaleNinth

namespace DetANN.HPIM.QP

lemma run_add (P : Program) (s : State) (ω : ℕ → Bool) (a b : ℕ) :
    run P s ω (a + b) = run P (run P s ω a) ω b := by
  simp only [run]; rw [add_comm, Function.iterate_add_apply]

end DetANN.HPIM.QP

-- ===== PP_Prog =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth

/-- The child blocks and their lengths. -/
structure Blocks where
  med : ℕ → Program
  comps : ℕ → Program
  build : ℕ → Program
  bal : ℕ → Program
  Lm : ℕ
  Lc : ℕ
  Lb : ℕ
  Lbal : ℕ

namespace Blocks

/-- Offset of piece 1. -/
def o1 (B : Blocks) : ℕ := 39

/-- Offset of piece 2. -/
def o2 (B : Blocks) : ℕ := 39 + 14

/-- Offset of piece 3. -/
def o3 (B : Blocks) : ℕ := 39 + 14 + 58

/-- Offset of piece 4. -/
def o4 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm

/-- Offset of piece 5. -/
def o5 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9

/-- Offset of piece 6. -/
def o6 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14

/-- Offset of piece 7. -/
def o7 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82

/-- Offset of piece 8. -/
def o8 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb

/-- Offset of piece 9. -/
def o9 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0

/-- Offset of piece 10. -/
def o10 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal

/-- Offset of piece 11. -/
def o11 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26

/-- Offset of piece 12. -/
def o12 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26 + B.Lc

end Blocks

end DetANN.HPIM.PP

-- ===== PP_Basic =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN

/-- `cellsWritten` over consecutive run segments. -/
lemma cellsWritten_add (P : Program) (s : State) (a b : ℕ) :
    cellsWritten P s (a + b) = cellsWritten P s a ∪ cellsWritten P (run P s detTape a) b := by
  ext c
  simp only [cellsWritten, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hc⟩
    by_cases hia : i < a
    · exact Or.inl ⟨i, hia, hc⟩
    · refine Or.inr ⟨i - a, by omega, ?_⟩
      rw [← run_add, Nat.add_sub_cancel' (by omega)]; exact hc
  · rintro (⟨i, hi, hc⟩ | ⟨i, hi, hc⟩)
    · exact ⟨i, by omega, hc⟩
    · exact ⟨a + i, by omega, by rw [run_add]; exact hc⟩

variable (B : Blocks)

end DetANN.HPIM.PP

-- ===== BD_SegB =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

lemma sgd_split (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 197) (hh : s.halted = false)
    (hb0 : ¬ ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 4).core.pc = off + 201 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 53 = 0 ∧
      (∀ x, x ≠ 53 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs 54 = ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ :=
  split_steps.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

/-- The split node; copy for the left half. -/
lemma seg_laf (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 210) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1)
    (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 44) :
    (run Q s detTape 16).core.pc = off + 258 ∧
      (run Q s detTape 16).halted = false ∧
      (run Q s detTape 16).core.ptrs 13 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 16).core.ptrs 50 = s.core.ptrs 43 ∧
      (run Q s detTape 16).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧
      (run Q s detTape 16).core.ptrs 52 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 16).core.ptrs 57 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 16).core.ptrs 58 = 0 ∧
      (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 16).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 16).core.regs 44 = ((s.core.regs 44 + s.core.regs 45) / s.core.regs 53) ∧
      (∀ x, x ≠ 44 → (run Q s detTape 16).core.regs x = s.core.regs x) ∧
      (run Q s detTape 16).core.mem = s.core.mem ∧
      (run Q s detTape 16).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧
      (run Q s detTape 16).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 43 ∧
      (run Q s detTape 16).integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 4 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 44 → (run Q s detTape 16).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 16).work = s.work + 16 ∧
      ∀ c ∈ cellsWritten Q s 16, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 44) :=
  split_steps.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hm1 hx0

/-- Push the left half; copy for the right half. -/
lemma seg_r0 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 226) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 17).core.pc = off + 258 ∧
      (run Q s detTape 17).halted = false ∧
      (run Q s detTape 17).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 17).core.ptrs 42 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 17).core.ptrs 50 = s.core.ptrs 43 ∧
      (run Q s detTape 17).core.ptrs 51 = s.core.ptrs 53 ∧
      (run Q s detTape 17).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 17).core.ptrs 58 = 1 ∧
      (run Q s detTape 17).core.ptrs 62 = s.core.ptrs 52 + 2 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 17).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 17).core.regs = s.core.regs ∧
      (run Q s detTape 17).core.mem = s.core.mem ∧
      (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧
      (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 2 ∧
      (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 17).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 17).work = s.work + 17 ∧
      ∀ c ∈ cellsWritten Q s 17, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) :=
  split_steps.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hm1

/-- Push the right half. -/
lemma seg_r1 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 243) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 15).core.pc = off + 34 ∧
      (run Q s detTape 15).halted = false ∧
      (run Q s detTape 15).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 15).core.ptrs 42 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 15).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 15).core.ptrs 62 = s.core.ptrs 52 + 3 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 57 → x ≠ 62 → (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 15).core.regs = s.core.regs ∧
      (run Q s detTape 15).core.mem = s.core.mem ∧
      (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧
      (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 3 ∧
      (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 15).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 15).work = s.work + 15 ∧
      ∀ c ∈ cellsWritten Q s 15, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) :=
  split_steps.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hm1

lemma cs_head (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 258) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 261 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 14 = s.core.ptrs 14 - s.core.ptrs 60 ∧
      (run Q s detTape 3).core.ptrs 46 = 0 ∧
      (run Q s detTape 3).core.ptrs 56 = s.core.ptrs 14 - s.core.ptrs 60 ∧
      (∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ :=
  split_steps.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hm1

lemma cd_0 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 58 ≤ s.core.ptrs 69)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 226 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 57 = s.core.ptrs 56 + s.core.ptrs 51 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 3).core.mem z = s.core.mem z) ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      ∀ c ∈ cellsWritten Q s 3, c = (true, s.core.ptrs 56 + s.core.ptrs 51) :=
  split_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

lemma cd_1 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 58)
    (hb1 : s.core.ptrs 58 ≤ 1)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 5).core.pc = off + 243 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 57 = 1 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 56 + s.core.ptrs 51) :=
  split_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hb1 hm1

lemma cd_2 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 58)
    (hb1 : 1 < s.core.ptrs 58)
    (hb2 : s.core.ptrs 58 ≤ 2)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 7).core.pc = off + 304 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 57 = 2 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs = s.core.regs ∧
      (run Q s detTape 7).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 56 + s.core.ptrs 51) :=
  split_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hb1 hb2 hm1

lemma cd_3 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 58)
    (hb1 : 1 < s.core.ptrs 58)
    (hb2 : 2 < s.core.ptrs 58)
    (hb3 : s.core.ptrs 58 ≤ 3)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 9).core.pc = off + 321 ∧
      (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 57 = 3 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs = s.core.regs ∧
      (run Q s detTape 9).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 9).core.mem z = s.core.mem z) ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧
      ∀ c ∈ cellsWritten Q s 9, c = (true, s.core.ptrs 56 + s.core.ptrs 51) :=
  split_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hb1 hb2 hb3 hm1

lemma cd_4 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 58)
    (hb1 : 1 < s.core.ptrs 58)
    (hb2 : 2 < s.core.ptrs 58)
    (hb3 : 3 < s.core.ptrs 58)
    (hb4 : s.core.ptrs 58 ≤ 4)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 11).core.pc = off + 348 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 57 = 4 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs = s.core.regs ∧
      (run Q s detTape 11).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 11).core.mem z = s.core.mem z) ∧
      (run Q s detTape 11).integerMemory = s.integerMemory ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      ∀ c ∈ cellsWritten Q s 11, c = (true, s.core.ptrs 56 + s.core.ptrs 51) :=
  split_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hb1 hb2 hb3 hb4 hm1

lemma cd_5 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 58)
    (hb1 : 1 < s.core.ptrs 58)
    (hb2 : 2 < s.core.ptrs 58)
    (hb3 : 3 < s.core.ptrs 58)
    (hb4 : 4 < s.core.ptrs 58)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 12).core.pc = off + 366 ∧
      (run Q s detTape 12).halted = false ∧
      (run Q s detTape 12).core.ptrs 57 = 4 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 12).core.regs = s.core.regs ∧
      (run Q s detTape 12).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 12).core.mem z = s.core.mem z) ∧
      (run Q s detTape 12).integerMemory = s.integerMemory ∧
      (run Q s detTape 12).work = s.work + 12 ∧
      ∀ c ∈ cellsWritten Q s 12, c = (true, s.core.ptrs 56 + s.core.ptrs 51) :=
  split_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 Q off hE s hpc hh hb0 hb1 hb2 hb3 hb4 hm1

end DetANN.HPIM.BD

-- ===== BD_SegC =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

lemma ck_low (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tl lo : ℝ) (s : State)
    (hpc : s.core.pc = off + 283) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53) = tl)
    (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53) = lo)
    (hb0 : s.core.ptrs 53 < s.core.ptrs 1)
    (hb1 : ¬ (tl - lo) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1)
    (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 55) :
    (run Q s detTape 21).core.pc = off + 258 ∧
      (run Q s detTape 21).halted = false ∧
      (run Q s detTape 21).core.ptrs 13 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 21).core.ptrs 50 = s.core.ptrs 54 ∧
      (run Q s detTape 21).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧
      (run Q s detTape 21).core.ptrs 52 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 21).core.ptrs 57 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 21).core.ptrs 58 = 2 ∧
      (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 21).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 21).core.regs 44 = tl ∧
      (run Q s detTape 21).core.regs 45 = lo ∧
      (run Q s detTape 21).core.regs 54 = (tl - lo) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 54 → (run Q s detTape 21).core.regs x = s.core.regs x) ∧
      (run Q s detTape 21).core.mem = s.core.mem ∧
      (run Q s detTape 21).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧
      (run Q s detTape 21).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧
      (run Q s detTape 21).integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 55 → (run Q s detTape 21).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 21).work = s.work + 21 ∧
      ∀ c ∈ cellsWritten Q s 21, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 55) :=
  carve_steps.2.2.2.1 Q off hE tl lo s hpc hh fr0 fr1 hb0 hb1 hm1 hx0

lemma seg_r2 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 304) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 17).core.pc = off + 258 ∧
      (run Q s detTape 17).halted = false ∧
      (run Q s detTape 17).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 17).core.ptrs 42 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 17).core.ptrs 50 = s.core.ptrs 54 ∧
      (run Q s detTape 17).core.ptrs 51 = s.core.ptrs 53 ∧
      (run Q s detTape 17).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 17).core.ptrs 58 = 3 ∧
      (run Q s detTape 17).core.ptrs 62 = s.core.ptrs 52 + 2 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 17).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 17).core.regs = s.core.regs ∧
      (run Q s detTape 17).core.mem = s.core.mem ∧
      (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧
      (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 2 ∧
      (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 17).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 17).work = s.work + 17 ∧
      ∀ c ∈ cellsWritten Q s 17, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) :=
  carve_steps.2.2.2.2.1 Q off hE s hpc hh hm1

lemma seg_r3 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 321) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 5).core.pc = off + 326 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 54 = s.core.ptrs 56 ∧
      (run Q s detTape 5).core.ptrs 55 = s.core.ptrs 52 + 3 ∧
      (∀ x, x ≠ 54 → x ≠ 55 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ :=
  carve_steps.2.2.2.2.2.1 Q off hE s hpc hh hm1

lemma ch_high (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (th hi : ℝ) (s : State)
    (hpc : s.core.pc = off + 326) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53 + s.core.ptrs 1) = th)
    (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1) = hi)
    (hb0 : ¬ (hi - th) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1)
    (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 55) :
    (run Q s detTape 22).core.pc = off + 258 ∧
      (run Q s detTape 22).halted = false ∧
      (run Q s detTape 22).core.ptrs 13 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 22).core.ptrs 50 = s.core.ptrs 54 ∧
      (run Q s detTape 22).core.ptrs 51 = s.core.ptrs 53 ∧
      (run Q s detTape 22).core.ptrs 52 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 22).core.ptrs 57 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 22).core.ptrs 58 = 4 ∧
      (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 22).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 22).core.regs 44 = th ∧
      (run Q s detTape 22).core.regs 46 = hi ∧
      (run Q s detTape 22).core.regs 54 = (hi - th) ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 54 → (run Q s detTape 22).core.regs x = s.core.regs x) ∧
      (run Q s detTape 22).core.mem = s.core.mem ∧
      (run Q s detTape 22).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧
      (run Q s detTape 22).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧
      (run Q s detTape 22).integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 55 → (run Q s detTape 22).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 22).work = s.work + 22 ∧
      ∀ c ∈ cellsWritten Q s 22, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 55) :=
  carve_steps.2.2.2.2.2.2.2.1 Q off hE th hi s hpc hh fr0 fr1 hb0 hm1 hx0

lemma seg_r4 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 348) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 18).core.pc = off + 258 ∧
      (run Q s detTape 18).halted = false ∧
      (run Q s detTape 18).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 18).core.ptrs 42 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 18).core.ptrs 50 = s.core.ptrs 54 ∧
      (run Q s detTape 18).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧
      (run Q s detTape 18).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 18).core.ptrs 58 = 5 ∧
      (run Q s detTape 18).core.ptrs 62 = s.core.ptrs 52 + 3 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 18).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 18).core.regs = s.core.regs ∧
      (run Q s detTape 18).core.mem = s.core.mem ∧
      (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧
      (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 3 ∧
      (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 18).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 18).work = s.work + 18 ∧
      ∀ c ∈ cellsWritten Q s 18, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) :=
  carve_steps.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hm1

lemma seg_r5 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 366) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 6).core.pc = off + 283 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 53 = s.core.ptrs 53 + 1 ∧
      (run Q s detTape 6).core.ptrs 54 = s.core.ptrs 56 ∧
      (run Q s detTape 6).core.ptrs 55 = s.core.ptrs 52 + 2 ∧
      (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 55 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ :=
  carve_steps.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hm1

end DetANN.HPIM.BD

-- ===== BS_Geo =====
namespace DetANN.HPIM.BS

open DetANN.HPIM

variable {m n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ)

lemma le_sigma (lo hi : Fin m → ℝ) (j : Fin m) : hi j - lo j ≤ sigma lo hi :=
  le_ciSup (f := fun j => hi j - lo j) (Finite.bddAbove_range _) j

lemma exists_sigma (hm : 0 < m) (lo hi : Fin m → ℝ) : ∃ j, hi j - lo j = sigma lo hi := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact exists_eq_ciSup_of_finite

lemma longestAxis_some (hm : 0 < m) (lo hi : Fin m → ℝ) :
    ∃ k, longestAxis lo hi = some k ∧ hi k - lo k = sigma lo hi := by
  classical
  obtain ⟨j, hj⟩ := exists_sigma hm lo hi
  have hne : (Finset.univ.filter fun j : Fin m => sigma lo hi ≤ hi j - lo j).Nonempty :=
    ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj.ge⟩⟩
  refine ⟨(Finset.univ.filter fun j : Fin m => sigma lo hi ≤ hi j - lo j).min' hne, ?_, ?_⟩
  · unfold longestAxis
    convert dif_pos hne
  · have := (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
    exact le_antisymm (le_sigma _ _ _) this

end DetANN.HPIM.BS

-- ===== BD_Math =====
namespace DetANN.HPIM.BD

open DetANN.HPIM DetANN.HPIM.BS

variable {m n : ℕ}

lemma longestAxis_first {lo hi : Fin m → ℝ} {k : ℕ} (hk : k < m)
    (h : sigma lo hi ≤ hi ⟨k, hk⟩ - lo ⟨k, hk⟩)
    (hlt : ∀ j : Fin m, (j : ℕ) < k → ¬ sigma lo hi ≤ hi j - lo j) :
    longestAxis lo hi = some ⟨k, hk⟩ := by
  classical
  have hne : (Finset.univ.filter fun j : Fin m => sigma lo hi ≤ hi j - lo j).Nonempty :=
    ⟨⟨k, hk⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  unfold longestAxis
  rw [dif_pos hne]
  congr 1
  apply le_antisymm (Finset.min'_le (Finset.univ.filter fun j : Fin m => sigma lo hi ≤ hi j - lo j)
    ⟨k, hk⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  apply Finset.le_min'
  intro y hy
  by_contra hlt'
  exact hlt y (not_le.1 hlt') (Finset.mem_filter.1 hy).2

variable (pts : Fin n → Fin m → ℝ) (r c : ℝ)

section Carve

variable (tlo thi : Fin m → ℝ) (bld : (Fin m → ℝ) → (Fin m → ℝ) → BSP m)

end Carve

end DetANN.HPIM.BD

-- ===== BD_Loops =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

lemma la_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (lo hi : Fin m → ℝ) (σ : ℝ)
    (ks : ℕ) (hks : ks < m) (hσ : σ ≤ hi ⟨ks, hks⟩ - lo ⟨ks, hks⟩) :
    ∀ (d k : ℕ) (s : State), k + d = ks → s.core.pc = off + 201 → s.halted = false →
      s.core.ptrs 1 = m → s.core.ptrs 53 = k → s.core.regs 52 = σ → BoxAt s (s.core.ptrs 43) lo hi →
      ∃ t k0, ∃ hk0 : k0 < m, k ≤ k0 ∧ k0 ≤ ks ∧ t ≤ 9 * d + 7 ∧ σ ≤ hi ⟨k0, hk0⟩ - lo ⟨k0, hk0⟩ ∧
        (∀ j (hj : j < m), k ≤ j → j < k0 → ¬ σ ≤ hi ⟨j, hj⟩ - lo ⟨j, hj⟩) ∧
        (run Q s detTape t).core.pc = off + 210 ∧ (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 53 = k0 ∧
        (run Q s detTape t).core.regs 44 = lo ⟨k0, hk0⟩ ∧ (run Q s detTape t).core.regs 45 = hi ⟨k0, hk0⟩ ∧
        (∀ x, x ≠ 53 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ :=
  loop_specs.2.2.2.2.2.1 Q off hE lo hi σ ks hks hσ

lemma cl_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (src : ℕ → ℝ) (L : ℕ) :
    ∀ (k j : ℕ) (s : State), j + k = L → s.core.pc = off + 261 → s.halted = false → 1 ≤ s.core.ptrs 1 →
      s.core.ptrs 60 = L → s.core.ptrs 46 = j → s.core.ptrs 56 + L ≤ s.core.ptrs 50 →
      (∀ z, z < L → s.core.mem (s.core.ptrs 50 + z) = src z) →
      (∀ z, z < j → s.core.mem (s.core.ptrs 56 + z) = src z) →
      ∃ t, t ≤ 7 * k + 1 ∧ (run Q s detTape t).core.pc = off + 268 ∧
        (run Q s detTape t).halted = false ∧
        (∀ z, z < L → (run Q s detTape t).core.mem (s.core.ptrs 56 + z) = src z) ∧
        (∀ z, (z < s.core.ptrs 56 ∨ s.core.ptrs 56 + L ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 55 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 56 ≤ c.2 ∧ c.2 < s.core.ptrs 56 + L :=
  loop_specs.2.2.2.2.2.2.1 Q off hE src L

end DetANN.HPIM.BD

-- ===== BD_Scan =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

lemma localPts_of {s s' : State} {pts : Fin n → Fin m → ℝ} (h : LocalPts s pts)
    (h1 : s'.core.ptrs 1 = s.core.ptrs 1) (h10 : s'.core.ptrs 10 = s.core.ptrs 10)
    (h11 : s'.core.ptrs 11 = s.core.ptrs 11) (h12 : s'.core.ptrs 12 = s.core.ptrs 12)
    (hI : ∀ z, 0 ≤ z → s'.integerMemory z = s.integerMemory z)
    (hM : ∀ z, 0 ≤ z → s'.core.mem z = s.core.mem z) : LocalPts s' pts := by
  obtain ⟨a1, a11, a10, a12, hp⟩ := h
  refine ⟨by rw [h1, a1], by rw [h11, a11], by rw [h10]; exact a10, by rw [h12]; exact a12, fun i => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hp i
  have e1 : s'.integerMemory (s'.core.ptrs 10 + i) = s.integerMemory (s.core.ptrs 10 + i) := by
    rw [h10]; exact hI _ (by positivity)
  have e2 : s'.integerMemory (s'.core.ptrs 12 + s'.integerMemory (s'.core.ptrs 10 + i)) =
      s.integerMemory (s.core.ptrs 12 + s.integerMemory (s.core.ptrs 10 + i)) := by
    rw [e1, h12]; exact hI _ (by omega)
  refine ⟨by rw [e1]; exact b1, by rw [e2]; exact b2, fun j => ?_⟩
  rw [e2, hM _ (by positivity)]; exact b3 j

end DetANN.HPIM.BD

-- ===== BD_Parts =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

/-- Where the copy returns, by its code. -/
def retPc : ℕ → ℕ
  | 0 => 226
  | 1 => 243
  | 2 => 304
  | 3 => 321
  | 4 => 348
  | _ => 366

/-- The copy-and-set subroutine: a new box below the real scratch top, a copy of the box at
pointer `50` with cell `ptr 51` replaced by real `44`; it returns by its code (pointer `58`). -/
lemma cs_part (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (code : ℕ) (hc : code ≤ 5)
    (s : State) (hpc : s.core.pc = off + 258) (hh : s.halted = false) (hm : 1 ≤ m)
    (h1 : s.core.ptrs 1 = m) (h60 : s.core.ptrs 60 = 2 * m) (h58 : s.core.ptrs 58 = code)
    (h69 : s.core.ptrs 69 = 0) (hsrc : s.core.ptrs 14 ≤ s.core.ptrs 50) :
    ∃ t, t ≤ 14 * m + 16 ∧ (run Q s detTape t).core.pc = off + retPc code ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 14 = s.core.ptrs 14 - 2 * m ∧
      (run Q s detTape t).core.ptrs 56 = s.core.ptrs 14 - 2 * m ∧
      (∀ z : ℕ, z < 2 * m → (z : ℤ) ≠ s.core.ptrs 51 →
        (run Q s detTape t).core.mem (s.core.ptrs 14 - 2 * m + z) = s.core.mem (s.core.ptrs 50 + z)) ∧
      (run Q s detTape t).core.mem (s.core.ptrs 14 - 2 * m + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, (z < s.core.ptrs 14 - 2 * m + min 0 (s.core.ptrs 51) ∨
          s.core.ptrs 14 + max 0 (s.core.ptrs 51 - 2 * m + 1) ≤ z) →
        (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 55 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ w ∈ cellsWritten Q s t, w.1 = true ∧
        ((s.core.ptrs 14 - 2 * m ≤ w.2 ∧ w.2 < s.core.ptrs 14) ∨ w.2 = s.core.ptrs 14 - 2 * m + s.core.ptrs 51) := by
  have hm1 : 1 ≤ s.core.ptrs 1 := by rw [h1]; exact_mod_cast hm
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := cs_head Q off hE s hpc hh hm1
  set s1 := run Q s detTape 3 with hs1
  rw [h60] at g3 g5
  obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
    cl_loop Q off hE (fun z => s.core.mem (s.core.ptrs 50 + z)) (2 * m) (2 * m) 0 s1 (by omega) g1 g2
      (by rw [g6 1 (by decide) (by decide) (by decide)]; exact hm1) (by rw [g6 60 (by decide) (by decide) (by decide), h60]; push_cast; ring)
      g4 (by rw [g5, g6 50 (by decide) (by decide) (by decide)]; push_cast; omega)
      (by intro z _; rw [g6 50 (by decide) (by decide) (by decide), g8])
      (fun z h => absurd h (by omega))
  set s2 := run Q s1 detTape t2 with hs2
  have P2 : ∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → x ≠ 57 → s2.core.ptrs x = s.core.ptrs x := fun x a b c d => by
    rw [q5 x b d, g6 x a b c]
  have hrun2 : run Q s detTape (3 + t2) = s2 := by rw [run_add, ← hs1]
  -- the return by code
  have key : ∀ (t3 : ℕ), t3 ≤ 12 → ∀ s3 : State, run Q s2 detTape t3 = s3 →
      s3.core.pc = off + retPc code → s3.halted = false →
      (∀ x, x ≠ 57 → s3.core.ptrs x = s2.core.ptrs x) → s3.core.regs = s2.core.regs →
      s3.core.mem (s2.core.ptrs 56 + s2.core.ptrs 51) = s2.core.regs 44 →
      (∀ z, z ≠ s2.core.ptrs 56 + s2.core.ptrs 51 → s3.core.mem z = s2.core.mem z) →
      s3.integerMemory = s2.integerMemory → s3.work = s2.work + t3 →
      (∀ w ∈ cellsWritten Q s2 t3, w = (true, s2.core.ptrs 56 + s2.core.ptrs 51)) →
      ∃ t, t ≤ 14 * m + 16 ∧ (run Q s detTape t).core.pc = off + retPc code ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 14 = s.core.ptrs 14 - 2 * m ∧
        (run Q s detTape t).core.ptrs 56 = s.core.ptrs 14 - 2 * m ∧
        (∀ z : ℕ, z < 2 * m → (z : ℤ) ≠ s.core.ptrs 51 →
          (run Q s detTape t).core.mem (s.core.ptrs 14 - 2 * m + z) = s.core.mem (s.core.ptrs 50 + z)) ∧
        (run Q s detTape t).core.mem (s.core.ptrs 14 - 2 * m + s.core.ptrs 51) = s.core.regs 44 ∧
        (∀ z, (z < s.core.ptrs 14 - 2 * m + min 0 (s.core.ptrs 51) ∨
            s.core.ptrs 14 + max 0 (s.core.ptrs 51 - 2 * m + 1) ≤ z) →
          (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 55 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ w ∈ cellsWritten Q s t, w.1 = true ∧
          ((s.core.ptrs 14 - 2 * m ≤ w.2 ∧ w.2 < s.core.ptrs 14) ∨
            w.2 = s.core.ptrs 14 - 2 * m + s.core.ptrs 51) := by
    intro t3 ht3 s3 hs3 c1 c2 c3 c4 c5 c6 c7 c8 c9
    have p56 : s2.core.ptrs 56 = s.core.ptrs 14 - 2 * m := by rw [q5 56 (by decide) (by decide), g5]
    have p51 : s2.core.ptrs 51 = s.core.ptrs 51 := P2 51 (by decide) (by decide) (by decide) (by decide)
    have r44 : s2.core.regs 44 = s.core.regs 44 := by rw [q6 44 (by decide), g7]
    rw [p56, p51, r44] at c5; rw [p56, p51] at c6 c9
    refine ⟨(3 + t2) + t3, by omega, ?_⟩
    have hrun3 : run Q s detTape (3 + t2 + t3) = s3 := by rw [run_add, hrun2, hs3]
    rw [hrun3, cellsWritten_add Q s (3 + t2) t3, cellsWritten_add Q s 3 t2, ← hs1, g11, hrun2]
    refine ⟨c1, c2, by rw [c3 14 (by decide), q5 14 (by decide) (by decide), g3], by rw [c3 56 (by decide), p56], ?_, c5, ?_,
      fun x a b c d => by rw [c3 x d, P2 x a b c d], fun x a => by rw [c4, q6 x a, g7], by rw [c7, q7, g9],
      by rw [c8, q8, g10]; ring, ?_⟩
    · intro z hz hz'
      rw [c6 _ (by omega)]
      have := q3 z hz; rw [g5] at this; exact this
    · intro z hz
      have hne : z ≠ s.core.ptrs 14 - 2 * m + s.core.ptrs 51 := by
        rcases hz with hz | hz
        · have := min_le_right (0 : ℤ) (s.core.ptrs 51); omega
        · have := le_max_right (0 : ℤ) (s.core.ptrs 51 - 2 * m + 1); omega
      have hz2 : z < s1.core.ptrs 56 ∨ s1.core.ptrs 56 + ↑(2 * m) ≤ z := by
        rw [g5]; push_cast
        rcases hz with hz | hz
        · have := min_le_left (0 : ℤ) (s.core.ptrs 51); left; omega
        · have := le_max_left (0 : ℤ) (s.core.ptrs 51 - 2 * m + 1); right; omega
      rw [c6 z hne, q4 z hz2, g8]
    · intro w hw
      simp only [Finset.empty_union, Finset.mem_union] at hw
      rcases hw with hw | hw
      · obtain ⟨e1, e2, e3⟩ := q9 w hw; rw [g5] at e2 e3; exact ⟨e1, Or.inl ⟨e2, by push_cast at e3; omega⟩⟩
      · rw [c9 w hw]; exact ⟨rfl, Or.inr rfl⟩
  have h58' : s2.core.ptrs 58 = code := by rw [P2 58 (by decide) (by decide) (by decide) (by decide), h58]
  have h69' : s2.core.ptrs 69 = 0 := by rw [P2 69 (by decide) (by decide) (by decide) (by decide), h69]
  have hm2 : 1 ≤ s2.core.ptrs 1 := by rw [P2 1 (by decide) (by decide) (by decide) (by decide)]; exact hm1
  interval_cases code
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ :=
      cd_0 Q off hE s2 q1 q2 (by rw [h58', h69']; norm_num) hm2
    exact key 3 (by decide) _ rfl d1 d2 (fun x hx => d4 x hx) d5 d6 d7 d8 d9 d10
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ :=
      cd_1 Q off hE s2 q1 q2 (by rw [h58', h69']; norm_num) (by rw [h58']; norm_num) hm2
    exact key 5 (by decide) _ rfl d1 d2 (fun x hx => d4 x hx) d5 d6 d7 d8 d9 d10
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ :=
      cd_2 Q off hE s2 q1 q2 (by rw [h58', h69']; norm_num) (by rw [h58']; norm_num) (by rw [h58']; norm_num) hm2
    exact key 7 (by decide) _ rfl d1 d2 (fun x hx => d4 x hx) d5 d6 d7 d8 d9 d10
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ :=
      cd_3 Q off hE s2 q1 q2 (by rw [h58', h69']; norm_num) (by rw [h58']; norm_num) (by rw [h58']; norm_num)
        (by rw [h58']; norm_num) hm2
    exact key 9 (by decide) _ rfl d1 d2 (fun x hx => d4 x hx) d5 d6 d7 d8 d9 d10
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ :=
      cd_4 Q off hE s2 q1 q2 (by rw [h58', h69']; norm_num) (by rw [h58']; norm_num) (by rw [h58']; norm_num)
        (by rw [h58']; norm_num) (by rw [h58']; norm_num) hm2
    exact key 11 (by decide) _ rfl d1 d2 (fun x hx => d4 x hx) d5 d6 d7 d8 d9 d10
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ :=
      cd_5 Q off hE s2 q1 q2 (by rw [h58', h69']; norm_num) (by rw [h58']; norm_num) (by rw [h58']; norm_num)
        (by rw [h58']; norm_num) (by rw [h58']; norm_num) hm2
    exact key 12 (by decide) _ rfl d1 d2 (fun x hx => d4 x hx) d5 d6 d7 d8 d9 d10

/-- The copy with a `lo` coordinate replaced. -/
lemma boxAt_set_lo {s s' : State} {p nb : ℤ} {lo hi : Fin m → ℝ} (hB : BoxAt s p lo hi) (k : ℕ) (hk : k < m)
    (v : ℝ) (hc : ∀ z : ℕ, z < 2 * m → (z : ℤ) ≠ k → s'.core.mem (nb + z) = s.core.mem (p + z))
    (hv : s'.core.mem (nb + k) = v) : BoxAt s' nb (setCoord lo k v) hi := by
  intro j
  have hj := j.isLt
  refine ⟨?_, ?_⟩
  · unfold setCoord
    by_cases h : (j : ℕ) = k
    · rw [if_pos h, show ((j : ℕ) : ℤ) = (k : ℤ) by rw [h]]; exact hv
    · rw [if_neg h, hc j (by omega) (by exact_mod_cast h)]; exact (hB j).1
  · have := hc (j + m) (by omega) (by push_cast; omega)
    push_cast at this; rw [← add_assoc, ← add_assoc] at this; rw [this]; exact (hB j).2

/-- The copy with a `hi` coordinate replaced. -/
lemma boxAt_set_hi {s s' : State} {p nb : ℤ} {lo hi : Fin m → ℝ} (hB : BoxAt s p lo hi) (k : ℕ) (hk : k < m)
    (v : ℝ) (hc : ∀ z : ℕ, z < 2 * m → (z : ℤ) ≠ m + k → s'.core.mem (nb + z) = s.core.mem (p + z))
    (hv : s'.core.mem (nb + (m + k)) = v) : BoxAt s' nb lo (setCoord hi k v) := by
  intro j
  have hj := j.isLt
  refine ⟨?_, ?_⟩
  · rw [hc j (by omega) (by omega)]; exact (hB j).1
  · unfold setCoord
    by_cases h : (j : ℕ) = k
    · rw [if_pos h, show nb + ((j : ℕ) : ℤ) + (m : ℤ) = nb + ((m : ℤ) + (k : ℤ)) by rw [h]; ring]; exact hv
    · rw [if_neg h]
      have := hc (j + m) (by omega) (by push_cast; omega)
      push_cast at this; rw [← add_assoc, ← add_assoc] at this; rw [this]; exact (hB j).2

end DetANN.HPIM.BD

-- ===== BD_Inv =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

lemma env_of {s s' : State} {pts : Fin n → Fin m → ℝ} {r c : ℝ} {Z0 : ℤ} (h : Env s pts r c Z0)
    (hP : ∀ x, (x < 40 ∨ x = 40 ∨ x = 60 ∨ x = 68 ∨ x = 69) → x ≠ 13 → x ≠ 14 → x ≠ 17 →
      s'.core.ptrs x = s.core.ptrs x)
    (hR : ∀ x, (x < 42 ∨ x = 49 ∨ x = 50 ∨ x = 53) → s'.core.regs x = s.core.regs x)
    (hI : ∀ z, 0 ≤ z → s'.integerMemory z = s.integerMemory z)
    (hM : ∀ z, 0 ≤ z → s'.core.mem z = s.core.mem z) : Env s' pts r c Z0 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  refine ⟨localPts_of a0 (hP 1 (by decide) (by decide) (by decide) (by decide))
      (hP 10 (by decide) (by decide) (by decide) (by decide)) (hP 11 (by decide) (by decide) (by decide) (by decide))
      (hP 12 (by decide) (by decide) (by decide) (by decide)) hI hM,
    by rw [hR 11 (by decide), a1], by rw [hR 12 (by decide), a2],
    by rw [hP 40 (by decide) (by decide) (by decide) (by decide), a3],
    by rw [hP 60 (by decide) (by decide) (by decide) (by decide), a4],
    by rw [hP 68 (by decide) (by decide) (by decide) (by decide), a5],
    by rw [hP 69 (by decide) (by decide) (by decide) (by decide), a6],
    by rw [hR 40 (by decide), a7], by rw [hR 41 (by decide), a8], by rw [hR 49 (by decide), a9],
    by rw [hR 50 (by decide), a10], by rw [hR 53 (by decide), a11]⟩

end DetANN.HPIM.BD

-- ===== BD_Split =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

lemma cs_frame {a b : ℤ} {M : ℕ} (h0 : 0 ≤ b) (h1 : b < 2 * M) {z : ℤ} (hz : z < a - 2 * M ∨ a ≤ z) :
    z < a - 2 * M + min 0 b ∨ a + max 0 (b - 2 * M + 1) ≤ z := by
  rw [min_eq_left h0, max_eq_left (by omega)]; omega

end DetANN.HPIM.BD

-- ===== BD_PrfP =====
namespace DetANN.HPIM.BD.SP

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

set_option maxHeartbeats 1000000 in
/-- From `SGD` without carving: the split node, both halves, and two pushed tasks. -/
lemma split_pre (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (lo hi : Fin m → ℝ) (s : State)
    (hpc : s.core.pc = off + 197) (hh : s.halted = false) (hEnv : Env s pts r c Z0)
    (h52 : s.core.regs 52 = sigma lo hi) (hc : ¬ (s.core.regs 51 + s.core.regs 51 - s.core.regs 52 ≤ 0))
    (hB : BoxAt s (s.core.ptrs 43) lo hi) (hsl : s.core.ptrs 13 ≤ s.core.ptrs 44)
    (hp : s.core.ptrs 14 ≤ s.core.ptrs 43) :
    ∃ (t : ℕ) (s' : State) (k : Fin m), run Q s detTape t = s' ∧ t ≤ 37 * m + 91 ∧ longestAxis lo hi = some k ∧
      s'.core.pc = off + 34 ∧ s'.halted = false ∧
      s'.core.ptrs 13 = s.core.ptrs 13 - 10 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧
      s'.core.ptrs 42 = s.core.ptrs 13 - 10 ∧
      s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧
      s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 43 ∧
      s'.integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 4 ∧
      s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧
      s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 ∧
      s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧
      s'.integerMemory (s.core.ptrs 13 - 10) = s.core.ptrs 14 - 4 * m ∧
      s'.integerMemory (s.core.ptrs 13 - 9) = s.core.ptrs 13 - 1 ∧
      s'.integerMemory (s.core.ptrs 13 - 8) = s.core.ptrs 13 - 7 ∧
      BoxAt s' (s.core.ptrs 14 - 2 * m) lo (setCoord hi k ((lo k + hi k) / 2)) ∧
      BoxAt s' (s.core.ptrs 14 - 4 * m) (setCoord lo k ((lo k + hi k) / 2)) hi ∧
      (∀ x, (x < 13 ∨ (14 < x ∧ x < 42) ∨ x = 40 ∨ x = 59 ∨ x = 60 ∨ x = 68 ∨ x = 69) →
        s'.core.ptrs x = s.core.ptrs x) ∧
      (∀ x, (x < 44 ∨ x = 49 ∨ x = 50 ∨ x = 53) → s'.core.regs x = s.core.regs x) ∧
      (∀ z, (z < s.core.ptrs 14 - 4 * m ∨ s.core.ptrs 14 ≤ z) → s'.core.mem z = s.core.mem z) ∧
      (∀ z, (z < s.core.ptrs 13 - 10 ∨ s.core.ptrs 13 ≤ z) → z ≠ s.core.ptrs 44 →
        s'.integerMemory z = s.integerMemory z) ∧
      s'.work = s.work + t ∧
      (∀ w ∈ cellsWritten Q s t,
        (w.1 = false ∧ ((s.core.ptrs 13 - 10 ≤ w.2 ∧ w.2 < s.core.ptrs 13) ∨ w.2 = s.core.ptrs 44)) ∨
        (w.1 = true ∧ s.core.ptrs 14 - 4 * m ≤ w.2 ∧ w.2 < s.core.ptrs 14)) := by
  obtain ⟨hL, e11, e12, e40, e60, e68, e69, e40', e41, e49, e50, e53⟩ := hEnv
  have a1 := hL.1
  have hm1 : 1 ≤ s.core.ptrs 1 := by rw [a1]; exact_mod_cast hm
  have hm0 : 0 < m := by omega
  -- the decision
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := sgd_split Q off hE s hpc hh hc hm1
  set s1 := run Q s detTape 4 with hs1
  -- the least longest axis
  obtain ⟨ks, hks, hside⟩ := longestAxis_some hm0 lo hi
  obtain ⟨t2, k0, hk0, -, -, ht2, hσk, hlt, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
    la_loop Q off hE lo hi (sigma lo hi) ks ks.isLt (by rw [hside]) ks 0 s1 (by omega) g1 g2
      (by rw [g4 1 (by decide), a1]) g3 (by rw [g6 52 (by decide), h52])
      (by rw [g4 43 (by decide)]; unfold BoxAt; rw [g7]; exact hB)
  have hLA : longestAxis lo hi = some ⟨k0, hk0⟩ :=
    longestAxis_first hk0 hσk (fun j hj => hlt j j.isLt (by omega) hj)
  set k : Fin m := ⟨k0, hk0⟩ with hkdef
  set s2 := run Q s1 detTape t2 with hs2
  have P2 : ∀ x, x ≠ 53 → x ≠ 57 → s2.core.ptrs x = s.core.ptrs x := fun x a b => by rw [q6 x a b, g4 x a]
  -- the node and the left half
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩ :=
    seg_laf Q off hE s2 q1 q2 (by rw [P2 1 (by decide) (by decide)]; exact hm1)
      (by rw [P2 13 (by decide) (by decide), P2 44 (by decide) (by decide)]; exact hsl)
  set s3 := run Q s2 detTape 16 with hs3
  simp only [P2 13 (by decide) (by decide), P2 43 (by decide) (by decide), P2 44 (by decide) (by decide),
    P2 1 (by decide) (by decide), P2 68 (by decide) (by decide), q3, a1, e68] at l3 l4 l5 l6 l7 l13 l14 l15 l16 l18
  have hmid : s3.core.regs 44 = (lo k + hi k) / 2 := by
    rw [l10, q4, q5, q7 53 (by decide) (by decide) (by decide) (by decide), g6 53 (by decide), e53]
  have P3 : ∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 53 → x ≠ 57 → x ≠ 58 →
      s3.core.ptrs x = s.core.ptrs x := fun x a b c d e f g => by rw [l9 x a b c d f g, P2 x e f]
  have s3p1 : s3.core.ptrs 1 = m := by rw [P3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a1]
  have s3p60 : s3.core.ptrs 60 = 2 * m := by rw [P3 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e60]
  have s3p69 : s3.core.ptrs 69 = 0 := by rw [P3 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e69]
  have p14 : s3.core.ptrs 14 = s.core.ptrs 14 := P3 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t4, ht4, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ :=
    cs_part Q off hE 0 (by decide) s3 l1 l2 hm s3p1 s3p60 l8 s3p69 (by rw [p14, l4]; exact hp)
  set s4 := run Q s3 detTape t4 with hs4
  simp only [p14, l4, l5, hmid] at c3 c4 c5 c6 c7 c12
  have hBL : BoxAt s4 (s.core.ptrs 14 - 2 * m) lo (setCoord hi k ((lo k + hi k) / 2)) := by
    apply boxAt_set_hi (s := s3) (p := s.core.ptrs 43) _ k0 hk0
    · intro z hz hz'; rw [c5 z hz (by omega)]
    · exact c6
    · intro jj; rw [l12, q8, g7]; exact hB jj
  have P4 : ∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → x ≠ 57 → s4.core.ptrs x = s3.core.ptrs x := c8
  have u4 : s4.core.ptrs 52 = s.core.ptrs 13 - 4 := by rw [P4 52 (by decide) (by decide) (by decide) (by decide), l6]
  have z4 : s4.core.ptrs 13 = s.core.ptrs 13 - 4 := by rw [P4 13 (by decide) (by decide) (by decide) (by decide), l3]
  have sp4 : s4.core.ptrs 42 = s.core.ptrs 42 := by
    rw [P4 42 (by decide) (by decide) (by decide) (by decide), P3 42 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  have s4p1 : 1 ≤ s4.core.ptrs 1 := by rw [P4 1 (by decide) (by decide) (by decide) (by decide), s3p1]; exact_mod_cast hm
  -- push the left half, copy for the right half
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩ :=
    seg_r0 Q off hE s4 (by rw [c1]; rfl) c2 s4p1
  set s5 := run Q s4 detTape 17 with hs5
  simp only [z4, u4, c4, sp4] at r3 r4 r9 r13 r14 r15 r16 r18
  have P5 : ∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 →
      s5.core.ptrs x = s4.core.ptrs x := r10
  have s5p1 : s5.core.ptrs 1 = m := by
    rw [P5 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      P4 1 (by decide) (by decide) (by decide) (by decide), s3p1]
  have s5p60 : s5.core.ptrs 60 = 2 * m := by
    rw [P5 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      P4 60 (by decide) (by decide) (by decide) (by decide), s3p60]
  have s5p69 : s5.core.ptrs 69 = 0 := by
    rw [P5 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      P4 69 (by decide) (by decide) (by decide) (by decide), s3p69]
  have s5p14 : s5.core.ptrs 14 = s.core.ptrs 14 - 2 * m := by
    rw [P5 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), c3]
  have s5p50 : s5.core.ptrs 50 = s.core.ptrs 43 := by
    rw [r5, P4 43 (by decide) (by decide) (by decide) (by decide), P3 43 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  have s5p51 : s5.core.ptrs 51 = k0 := by
    rw [r6, P4 53 (by decide) (by decide) (by decide) (by decide), l9 53 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), q3]
  have s5r44 : s5.core.regs 44 = (lo k + hi k) / 2 := by rw [r11, c9 44 (by decide), hmid]
  obtain ⟨t6, ht6, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩ :=
    cs_part Q off hE 1 (by decide) s5 r1 r2 hm s5p1 s5p60 r8 s5p69 (by rw [s5p14, s5p50]; omega)
  set s6 := run Q s5 detTape t6 with hs6
  simp only [s5p14, s5p50, s5p51, s5r44] at d3 d4 d5 d6 d7 d12
  have hBR : BoxAt s6 (s.core.ptrs 14 - 2 * m - 2 * m) (setCoord lo k ((lo k + hi k) / 2)) hi := by
    apply boxAt_set_lo (s := s5) (p := s.core.ptrs 43) _ k0 hk0
    · intro z hz hz'; rw [d5 z hz hz']
    · exact d6
    · intro jj; have := jj.isLt
      rw [r12, c7 (s.core.ptrs 43 + jj) (cs_frame (by clear * -; omega) (by clear * - hk0; omega)
          (Or.inr (by clear * - hp; omega))),
        c7 (s.core.ptrs 43 + jj + m) (cs_frame (by clear * -; omega) (by clear * - hk0; omega)
          (Or.inr (by clear * - hp; omega))), l12, q8, g7]
      exact hB jj
  have P6 : ∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → x ≠ 57 → s6.core.ptrs x = s5.core.ptrs x := d8
  have s6p1 : 1 ≤ s6.core.ptrs 1 := by rw [P6 1 (by decide) (by decide) (by decide) (by decide), s5p1]; exact_mod_cast hm
  -- push the right half
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
    seg_r1 Q off hE s6 (by rw [d1]; rfl) d2 s6p1
  set s7 := run Q s6 detTape 15 with hs7
  have z6 : s6.core.ptrs 13 = s.core.ptrs 13 - 7 := by rw [P6 13 (by decide) (by decide) (by decide) (by decide), r3]; ring
  have u6 : s6.core.ptrs 52 = s.core.ptrs 13 - 4 := by
    rw [P6 52 (by decide) (by decide) (by decide) (by decide), P5 52 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), u4]
  have sp6 : s6.core.ptrs 42 = s.core.ptrs 13 - 7 := by rw [P6 42 (by decide) (by decide) (by decide) (by decide), r4]; ring
  simp only [z6, u6, d4, sp6] at w3 w4 w6 w10 w11 w12 w13 w15
  -- the whole run
  have hr : run Q s detTape (4 + t2 + 16 + t4 + 17 + t6 + 15) = s7 := by
    rw [run_add, run_add, run_add, run_add, run_add, run_add, ← hs1, ← hs2, ← hs3, ← hs4, ← hs5, ← hs6]
  clear_value s1 s2 s3 s4 s5 s6 s7 k
  -- frames of the whole run
  have I7 : ∀ z, (z < s.core.ptrs 13 - 10 ∨ s.core.ptrs 13 - 4 ≤ z) → s7.integerMemory z = s3.integerMemory z := by
    intro z hz
    rw [w13 z (by clear * - hz; omega) (by clear * - hz; omega) (by clear * - hz; omega), d10,
      r16 z (by clear * - hz; omega) (by clear * - hz; omega) (by clear * - hz; omega), c10]
  have I3 : ∀ z, (z < s.core.ptrs 13 - 4 ∨ s.core.ptrs 13 ≤ z) → z ≠ s.core.ptrs 44 →
      s3.integerMemory z = s.integerMemory z := by
    intro z hz hne
    rw [l16 z (by clear * - hz; omega) (by clear * - hz; omega) hne, q9, g8]
  have M7 : ∀ z, (z < s.core.ptrs 14 - 4 * m ∨ s.core.ptrs 14 ≤ z) → s7.core.mem z = s.core.mem z := by
    intro z hz
    have hk1 : (k0 : ℤ) < 2 * m := by clear * - hk0; omega
    rw [w9, d7 z (cs_frame (by clear * -; omega) hk1 (by clear * - hz; omega)), r12,
      c7 z (cs_frame (by clear * -; omega) (by clear * - hk0; omega) (by clear * - hz; omega)), l12, q8, g7]
  have hk' : ks.1 < m := ks.isLt
  have htb : 4 + t2 + 16 + t4 + 17 + t6 + 15 ≤ 37 * m + 91 := by clear * - ht2 hk' ht4 ht6; omega
  have o1 : s7.core.ptrs 13 = s.core.ptrs 13 - 10 := by rw [w3]; ring
  have o2 : s7.core.ptrs 14 = s.core.ptrs 14 - 4 * m := by
    rw [w7 14 (by decide) (by decide) (by decide) (by decide), d3]; ring
  have o3 : s7.core.ptrs 42 = s.core.ptrs 13 - 10 := by rw [w4]; ring
  have o4 : s7.integerMemory (s.core.ptrs 13 - 4) = 1 := by
    rw [I7 (s.core.ptrs 13 - 4) (Or.inr le_rfl)]; exact l13
  have o5 : s7.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 43 := by
    rw [I7 (s.core.ptrs 13 - 3) (Or.inr (by clear * -; omega))]; exact l14
  have o6 : s7.integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 4 := by
    rw [I7 (s.core.ptrs 44) (Or.inr (by clear * - hsl; omega))]; exact l15
  have o7 : s7.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m := by
    rw [w13 (s.core.ptrs 13 - 7) (by clear * -; omega) (by clear * -; omega) (by clear * -; omega), d10]
    rw [show s.core.ptrs 13 - 7 = s.core.ptrs 13 - 4 - 3 by ring]; exact r13
  have o8 : s7.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 := by
    rw [w13 (s.core.ptrs 13 - 6) (by clear * -; omega) (by clear * -; omega) (by clear * -; omega), d10,
      show s.core.ptrs 13 - 6 = s.core.ptrs 13 - 4 - 2 by ring, r14]; ring
  have o9 : s7.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 := by
    rw [w13 (s.core.ptrs 13 - 5) (by clear * -; omega) (by clear * -; omega) (by clear * -; omega), d10]
    rw [show s.core.ptrs 13 - 5 = s.core.ptrs 13 - 4 - 1 by ring]; exact r15
  have o10 : s7.integerMemory (s.core.ptrs 13 - 10) = s.core.ptrs 14 - 4 * m := by
    rw [show s.core.ptrs 13 - 10 = s.core.ptrs 13 - 7 - 3 by ring, w10]; ring
  have o11 : s7.integerMemory (s.core.ptrs 13 - 9) = s.core.ptrs 13 - 1 := by
    rw [show s.core.ptrs 13 - 9 = s.core.ptrs 13 - 7 - 2 by ring, w11]; ring
  have o12 : s7.integerMemory (s.core.ptrs 13 - 8) = s.core.ptrs 13 - 7 := by rw [← w12]; ring_nf
  refine ⟨4 + t2 + 16 + t4 + 17 + t6 + 15, s7, k, hr, htb, hLA, w1, w2, o1, o2, o3, o4, o5, o6, o7, o8, o9,
    o10, o11, o12, ?_, ?_, ?_, ?_, M7, ?_, ?_, ?_⟩
  · intro jj; have := jj.isLt
    rw [w9, d7 (s.core.ptrs 14 - 2 * m + jj) (cs_frame (by clear * -; omega) (by clear * - hk0; omega)
        (Or.inr (by clear * -; omega))),
      d7 (s.core.ptrs 14 - 2 * m + jj + m) (cs_frame (by clear * -; omega) (by clear * - hk0; omega)
        (Or.inr (by clear * -; omega))), r12]
    exact hBL jj
  · rw [show s.core.ptrs 14 - 4 * m = s.core.ptrs 14 - 2 * m - 2 * m by ring]
    unfold BoxAt; rw [w9]; exact hBR
  · intro x hx
    rw [w7 x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega), P6 x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega),
      P5 x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega),
      P4 x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega),
      P3 x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)]
  · intro x hx
    rw [w8, d9 x (by clear * - hx; omega), r11, c9 x (by clear * - hx; omega), l11 x (by clear * - hx; omega),
      q7 x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega), g6 x (by clear * - hx; omega)]
  · intro z hz hne
    rw [I7 z (by clear * - hz; omega), I3 z (by clear * - hz; omega) hne]
  · rw [w14, d11, r17, c11, l17, q10, g9]; ring
  · intro w hw
    have e2 : run Q s detTape (4 + t2) = s2 := by rw [run_add, ← hs1, ← hs2]
    have e3 : run Q s detTape (4 + t2 + 16) = s3 := by rw [run_add, e2, ← hs3]
    have e4 : run Q s detTape (4 + t2 + 16 + t4) = s4 := by rw [run_add, e3, ← hs4]
    have e5 : run Q s detTape (4 + t2 + 16 + t4 + 17) = s5 := by rw [run_add, e4, ← hs5]
    have e6 : run Q s detTape (4 + t2 + 16 + t4 + 17 + t6) = s6 := by rw [run_add, e5, ← hs6]
    rw [cellsWritten_add Q s _ 15, e6, cellsWritten_add Q s _ t6, e5, cellsWritten_add Q s _ 17, e4,
      cellsWritten_add Q s _ t4, e3, cellsWritten_add Q s _ 16, e2, cellsWritten_add Q s 4 t2, ← hs1, g10, q11] at hw
    simp only [Finset.mem_union, Finset.notMem_empty, false_or, or_false, or_assoc] at hw
    rcases hw with hw | hw | hw | hw | hw
    · rcases l18 w hw with rfl | rfl | rfl
      · left; exact ⟨rfl, Or.inl ⟨by clear * - hk0; omega, by clear * - hk0; omega⟩⟩
      · left; exact ⟨rfl, Or.inl ⟨by clear * - hk0; omega, by clear * - hk0; omega⟩⟩
      · left; exact ⟨rfl, Or.inr rfl⟩
    · obtain ⟨e1, e2⟩ := c12 w hw
      right; refine ⟨e1, ?_⟩
      rcases e2 with ⟨a, b⟩ | e2
      · exact ⟨by clear * - a b hk0; omega, by clear * - a b hk0; omega⟩
      · rw [e2]; exact ⟨by clear * - hk0; omega, by clear * - hk0; omega⟩
    · rcases r18 w hw with rfl | rfl | rfl <;> exact Or.inl ⟨rfl, Or.inl ⟨by clear * - hk0; omega, by clear * - hk0; omega⟩⟩
    · obtain ⟨e1, e2⟩ := d12 w hw
      right; refine ⟨e1, ?_⟩
      rcases e2 with ⟨a, b⟩ | e2
      · exact ⟨by clear * - a b hk0; omega, by clear * - a b hk0; omega⟩
      · rw [e2]; exact ⟨by clear * - hk0; omega, by clear * - hk0; omega⟩
    · rcases w15 w hw with rfl | rfl | rfl <;> exact Or.inl ⟨rfl, Or.inl ⟨by clear * - hk0; omega, by clear * - hk0; omega⟩⟩

set_option maxHeartbeats 1000000 in
/-- The low peel on axis `k`: a cut node at the current slot, the low slab pushed into its left slot,
and the rest (in the new current box) continuing in its right slot; from `CK` to `CH`. -/
lemma axis_low (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false)
    (hEnv : Env s pts r c Z0) (k : ℕ) (hk : k < m) (h53 : s.core.ptrs 53 = k)
    (tlo thi lo hi : Fin m → ℝ) (hQ : BoxAt s (s.core.ptrs 48) tlo thi) (hB : BoxAt s (s.core.ptrs 54) lo hi)
    (hlow : lo ⟨k, hk⟩ < tlo ⟨k, hk⟩) (hcsl : s.core.ptrs 13 ≤ s.core.ptrs 55)
    (hcb : s.core.ptrs 14 ≤ s.core.ptrs 54) (hq : s.core.ptrs 14 ≤ s.core.ptrs 48)
    (hZ : s.core.ptrs 13 ≤ 0) (hcsl0 : s.core.ptrs 55 < 0) (hR : s.core.ptrs 14 ≤ 0) :
    ∃ (t : ℕ) (s' : State), Fr Q s s' t (fun z => z = s.core.ptrs 55) ∧ t ≤ 28 * m + 80 ∧
      s'.core.pc = off + 326 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧
      s'.core.ptrs 13 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧
      s'.core.ptrs 42 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 48 = s.core.ptrs 48 ∧ s'.core.ptrs 53 = k ∧
      s'.core.ptrs 54 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 55 = s.core.ptrs 13 - 1 ∧
      s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧
      s'.integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧
      s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧
      s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 ∧
      s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧
      BoxAt s' (s.core.ptrs 14 - 2 * m) lo (setCoord hi k (tlo ⟨k, hk⟩)) ∧
      BoxAt s' (s.core.ptrs 14 - 4 * m) (setCoord lo k (tlo ⟨k, hk⟩)) hi := by
  have hEnv0 := hEnv
  obtain ⟨hL, e11, e12, e40, e60, e68, e69, e40', e41, e49, e50, e53⟩ := hEnv
  have a1 := hL.1
  have hm1 : 1 ≤ s.core.ptrs 1 := by rw [a1]; exact_mod_cast hm
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20⟩ :=
    ck_low Q off hE (tlo ⟨k, hk⟩) (lo ⟨k, hk⟩) s hpc hh (by rw [h53]; exact (hQ ⟨k, hk⟩).1)
      (by rw [h53]; exact (hB ⟨k, hk⟩).1) (by rw [h53, a1]; exact_mod_cast hk) (by linarith) hm1 hcsl
  generalize hs1 : run Q s detTape 21 = s1 at *
  have P1 : ∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → s1.core.ptrs x = s.core.ptrs x := g9
  have s1p1 : s1.core.ptrs 1 = m := by rw [P1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a1]
  have s1p60 : s1.core.ptrs 60 = 2 * m := by
    rw [P1 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e60]
  have s1p69 : s1.core.ptrs 69 = 0 := by
    rw [P1 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e69]
  have s1p14 : s1.core.ptrs 14 = s.core.ptrs 14 := P1 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t2, ht2, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ :=
    cs_part Q off hE 2 (by decide) s1 g1 g2 hm s1p1 s1p60 g8 s1p69 (by rw [s1p14, g4]; exact hcb)
  generalize hs2 : run Q s1 detTape t2 = s2 at *
  simp only [s1p14, g4, g5, a1, h53, g10] at c3 c4 c5 c6 c7 c12
  have hB2 : BoxAt s2 (s.core.ptrs 14 - 2 * m) lo (setCoord hi k (tlo ⟨k, hk⟩)) := by
    refine boxAt_set_hi (s := s1) (p := s.core.ptrs 54) ?_ k hk _ (fun z hz hz' => c5 z hz hz') c6
    unfold BoxAt; rw [g14]; exact hB
  have P2 : ∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → x ≠ 57 → s2.core.ptrs x = s1.core.ptrs x := c8
  have s2p1 : 1 ≤ s2.core.ptrs 1 := by rw [P2 1 (by decide) (by decide) (by decide) (by decide), s1p1]; exact_mod_cast hm
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩ :=
    seg_r2 Q off hE s2 (by rw [c1]; rfl) c2 s2p1
  generalize hs3 : run Q s2 detTape 17 = s3 at *
  have z2 : s2.core.ptrs 13 = s.core.ptrs 13 - 4 := by rw [P2 13 (by decide) (by decide) (by decide) (by decide), g3]
  have u2 : s2.core.ptrs 52 = s.core.ptrs 13 - 4 := by rw [P2 52 (by decide) (by decide) (by decide) (by decide), g6]
  have sp2 : s2.core.ptrs 42 = s.core.ptrs 42 := by
    rw [P2 42 (by decide) (by decide) (by decide) (by decide), P1 42 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  simp only [z2, u2, sp2, c4] at r3 r4 r9 r13 r14 r15 r16 r18
  have P3 : ∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 →
      s3.core.ptrs x = s2.core.ptrs x := r10
  have s3p1 : s3.core.ptrs 1 = m := by
    rw [P3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      P2 1 (by decide) (by decide) (by decide) (by decide), s1p1]
  have s3p60 : s3.core.ptrs 60 = 2 * m := by
    rw [P3 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      P2 60 (by decide) (by decide) (by decide) (by decide), s1p60]
  have s3p69 : s3.core.ptrs 69 = 0 := by
    rw [P3 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      P2 69 (by decide) (by decide) (by decide) (by decide), s1p69]
  have s3p14 : s3.core.ptrs 14 = s.core.ptrs 14 - 2 * m := by
    rw [P3 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), c3]
  have s3p50 : s3.core.ptrs 50 = s.core.ptrs 54 := by
    rw [r5, P2 54 (by decide) (by decide) (by decide) (by decide),
      P1 54 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have s3p51 : s3.core.ptrs 51 = k := by
    rw [r6, P2 53 (by decide) (by decide) (by decide) (by decide),
      P1 53 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h53]
  have s3r44 : s3.core.regs 44 = tlo ⟨k, hk⟩ := by rw [r11, c9 44 (by decide), g10]
  obtain ⟨t4, ht4, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩ :=
    cs_part Q off hE 3 (by decide) s3 r1 r2 hm s3p1 s3p60 r8 s3p69 (by rw [s3p14, s3p50]; omega)
  generalize hs4 : run Q s3 detTape t4 = s4 at *
  simp only [s3p14, s3p50, s3p51, s3r44] at d3 d4 d5 d6 d7 d12
  have hB4 : BoxAt s4 (s.core.ptrs 14 - 2 * m - 2 * m) (setCoord lo k (tlo ⟨k, hk⟩)) hi := by
    refine boxAt_set_lo (s := s3) (p := s.core.ptrs 54) ?_ k hk _ (fun z hz hz' => d5 z hz hz') d6
    intro jj; have := jj.isLt
    rw [r12, c7 _ (cs_frame (by positivity) (by omega) (Or.inr (by omega))),
      c7 _ (cs_frame (by positivity) (by omega) (Or.inr (by omega))), g14]
    exact hB jj
  have P4 : ∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → x ≠ 57 → s4.core.ptrs x = s3.core.ptrs x := d8
  have s4p1 : 1 ≤ s4.core.ptrs 1 := by rw [P4 1 (by decide) (by decide) (by decide) (by decide), s3p1]; exact_mod_cast hm
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10⟩ := seg_r3 Q off hE s4 (by rw [d1]; rfl) d2 s4p1
  generalize hs5 : run Q s4 detTape 5 = s5 at *
  have hk0 : (k : ℤ) < m := by exact_mod_cast hk
  have PP : ∀ x, x ≠ 13 → x ≠ 14 → x ≠ 42 → x ≠ 46 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 54 → x ≠ 55 → x ≠ 56 →
      x ≠ 57 → x ≠ 58 → x ≠ 62 → s5.core.ptrs x = s.core.ptrs x := by
    intro x a b c d e f g h i j k' l o
    rw [w5 x h i, P4 x b d j k', P3 x a c e f k' l o, P2 x b d j k', P1 x a e f g k' l]
  have p13 : s5.core.ptrs 13 = s.core.ptrs 13 - 7 := by
    rw [w5 13 (by decide) (by decide), P4 13 (by decide) (by decide) (by decide) (by decide), r3]; ring
  have p14 : s5.core.ptrs 14 = s.core.ptrs 14 - 4 * m := by
    rw [w5 14 (by decide) (by decide), d3]; ring
  have I5 : s5.integerMemory = s3.integerMemory := by rw [w8, d10]
  have hI : ∀ z, z ≠ s.core.ptrs 13 - 4 - 3 → z ≠ s.core.ptrs 13 - 4 - 2 → z ≠ s.core.ptrs 13 - 4 - 1 →
      s5.integerMemory z = s1.integerMemory z := fun z a b c => by rw [I5, r16 z a b c, c10]
  have hM : ∀ z, (z < s.core.ptrs 14 - 4 * m ∨ s.core.ptrs 14 ≤ z) → s5.core.mem z = s.core.mem z := by
    intro z hz
    rw [w7, d7 z (cs_frame (by positivity) (by omega) (by omega)), r12,
      c7 z (cs_frame (by positivity) (by omega) (by omega)), g14]
  have hrun : run Q s detTape (21 + t2 + 17 + t4 + 5) = s5 := by
    rw [run_add, run_add, run_add, run_add, hs1, hs2, hs3, hs4, hs5]
  refine ⟨21 + t2 + 17 + t4 + 5, s5, ⟨hrun, by rw [w9, d11, r17, c11, g19]; ring, by rw [p13]; clear * -; omega,
    by rw [p14]; clear * -; omega, fun x hx a b => PP x a b (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega),
    PP 59 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    fun x hx => by
      rw [w6, d9 x (by clear * - hx; omega), r11, c9 x (by clear * - hx; omega),
        g13 x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)],
    fun z hz hne => by
      rw [p13] at hz
      rw [hI z (by clear * - hz; omega) (by clear * - hz; omega) (by clear * - hz; omega),
        g18 z (by clear * - hz; omega) (by clear * - hz; omega) hne],
    fun z hz => hM z (by rw [p14] at hz; exact hz), ?_⟩, by clear * - ht2 ht4; omega, w1, w2, ?_, p13, p14,
    by rw [w5 42 (by decide) (by decide), P4 42 (by decide) (by decide) (by decide) (by decide), r4]; ring,
    PP 48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    by rw [PP 53 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), h53],
    by rw [w3, d4]; ring,
    by rw [w4, P4 52 (by decide) (by decide) (by decide) (by decide), P3 52 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), u2]; ring,
    by rw [hI _ (by clear * -; omega) (by clear * -; omega) (by clear * -; omega), g15, e68],
    by rw [hI _ (by clear * -; omega) (by clear * -; omega) (by clear * -; omega), g16],
    by rw [hI _ (by clear * - hcsl; omega) (by clear * - hcsl; omega) (by clear * - hcsl; omega), g17],
    by rw [I5, show s.core.ptrs 13 - 7 = s.core.ptrs 13 - 4 - 3 by ring, r13],
    by rw [I5, show s.core.ptrs 13 - 6 = s.core.ptrs 13 - 4 - 2 by ring, r14]; ring,
    by rw [I5, show s.core.ptrs 13 - 5 = s.core.ptrs 13 - 4 - 1 by ring, r15], ?_, ?_⟩
  · intro w hw
    have e2 : run Q s detTape (21 + t2) = s2 := by rw [run_add, hs1, hs2]
    have e3 : run Q s detTape (21 + t2 + 17) = s3 := by rw [run_add, e2, hs3]
    have e4 : run Q s detTape (21 + t2 + 17 + t4) = s4 := by rw [run_add, e3, hs4]
    rw [cellsWritten_add Q s _ 5, e4, w10, Finset.union_empty, cellsWritten_add Q s _ t4, e3,
      cellsWritten_add Q s _ 17, e2, cellsWritten_add Q s 21 t2, hs1] at hw
    simp only [Finset.mem_union, or_assoc] at hw
    rcases hw with hw | hw | hw | hw
    · rcases g20 w hw with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, Or.inl ⟨by rw [p13]; clear * -; omega, by clear * -; omega⟩⟩
      · exact Or.inl ⟨rfl, Or.inl ⟨by rw [p13]; clear * -; omega, by clear * -; omega⟩⟩
      · exact Or.inl ⟨rfl, Or.inr rfl⟩
    · obtain ⟨e1, e2⟩ := c12 w hw
      refine Or.inr ⟨e1, ?_⟩
      rw [p14]; rcases e2 with ⟨a, b⟩ | e2
      · exact ⟨by clear * - a; omega, b⟩
      · rw [e2]; exact ⟨by clear * - hk0; omega, by clear * - hk0; omega⟩
    · rcases r18 w hw with rfl | rfl | rfl <;>
        exact Or.inl ⟨rfl, Or.inl ⟨by rw [p13]; clear * -; omega, by clear * -; omega⟩⟩
    · obtain ⟨e1, e2⟩ := d12 w hw
      refine Or.inr ⟨e1, ?_⟩
      rw [p14]; rcases e2 with ⟨a, b⟩ | e2
      · exact ⟨by clear * - a; omega, by clear * - b; omega⟩
      · rw [e2]; exact ⟨by clear * - hk0; omega, by clear * - hk0; omega⟩
  · exact env_of hEnv0 (fun x hx a b c => PP x a b (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega))
      (fun x hx => by
        rw [w6, d9 x (by clear * - hx; omega), r11, c9 x (by clear * - hx; omega),
          g13 x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)])
      (fun z hz => by
        rw [hI z (by clear * - hz hZ; omega) (by clear * - hz hZ; omega) (by clear * - hz hZ; omega),
          g18 z (by clear * - hz hZ; omega) (by clear * - hz hZ; omega) (by clear * - hz hcsl0; omega)])
      (fun z hz => hM z (Or.inr (by clear * - hz hR; omega)))
  · intro jj; have := jj.isLt
    rw [w7, d7 _ (cs_frame (by positivity) (by clear * - hk0; omega) (Or.inr (by clear * -; omega))),
      d7 _ (cs_frame (by positivity) (by clear * - hk0; omega) (Or.inr (by clear * -; omega))), r12]
    exact hB2 jj
  · rw [show s.core.ptrs 14 - 4 * m = s.core.ptrs 14 - 2 * m - 2 * m by ring]
    unfold BoxAt; rw [w7]; exact hB4

set_option maxHeartbeats 1000000 in
/-- The high peel on axis `k`: a cut node at the current slot, the high slab pushed into its right
slot, and the rest (in the new current box) continuing in its left slot; from `CH` to `CK`. -/
lemma axis_high (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (s : State) (hpc : s.core.pc = off + 326) (hh : s.halted = false)
    (hEnv : Env s pts r c Z0) (k : ℕ) (hk : k < m) (h53 : s.core.ptrs 53 = k)
    (tlo thi lo hi : Fin m → ℝ) (hQ : BoxAt s (s.core.ptrs 48) tlo thi) (hB : BoxAt s (s.core.ptrs 54) lo hi)
    (hhigh : hi ⟨k, hk⟩ > thi ⟨k, hk⟩) (hcsl : s.core.ptrs 13 ≤ s.core.ptrs 55)
    (hcb : s.core.ptrs 14 ≤ s.core.ptrs 54) (hq : s.core.ptrs 14 ≤ s.core.ptrs 48)
    (hZ : s.core.ptrs 13 ≤ 0) (hcsl0 : s.core.ptrs 55 < 0) (hR : s.core.ptrs 14 ≤ 0) :
    ∃ (t : ℕ) (s' : State), Fr Q s s' t (fun z => z = s.core.ptrs 55) ∧ t ≤ 28 * m + 80 ∧
      s'.core.pc = off + 283 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧
      s'.core.ptrs 13 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧
      s'.core.ptrs 42 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 48 = s.core.ptrs 48 ∧ s'.core.ptrs 53 = k + 1 ∧
      s'.core.ptrs 54 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 55 = s.core.ptrs 13 - 2 ∧
      s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧
      s'.integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧
      s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧
      s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 1 ∧
      s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧
      BoxAt s' (s.core.ptrs 14 - 2 * m) (setCoord lo k (thi ⟨k, hk⟩)) hi ∧
      BoxAt s' (s.core.ptrs 14 - 4 * m) lo (setCoord hi k (thi ⟨k, hk⟩)) := by
  have hEnv0 := hEnv
  obtain ⟨hL, e11, e12, e40, e60, e68, e69, e40', e41, e49, e50, e53⟩ := hEnv
  have a1 := hL.1
  have hm1 : 1 ≤ s.core.ptrs 1 := by rw [a1]; exact_mod_cast hm
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20⟩ :=
    ch_high Q off hE (thi ⟨k, hk⟩) (hi ⟨k, hk⟩) s hpc hh (by rw [h53, a1]; exact (hQ ⟨k, hk⟩).2)
      (by rw [h53, a1]; exact (hB ⟨k, hk⟩).2) (by linarith) hm1 hcsl
  generalize hs1 : run Q s detTape 22 = s1 at *
  have P1 : ∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → s1.core.ptrs x = s.core.ptrs x := g9
  have s1p1 : s1.core.ptrs 1 = m := by rw [P1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a1]
  have s1p60 : s1.core.ptrs 60 = 2 * m := by
    rw [P1 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e60]
  have s1p69 : s1.core.ptrs 69 = 0 := by
    rw [P1 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e69]
  have s1p14 : s1.core.ptrs 14 = s.core.ptrs 14 := P1 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t2, ht2, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ :=
    cs_part Q off hE 4 (by decide) s1 g1 g2 hm s1p1 s1p60 g8 s1p69 (by rw [s1p14, g4]; exact hcb)
  generalize hs2 : run Q s1 detTape t2 = s2 at *
  simp only [s1p14, g4, g5, h53, g10] at c3 c4 c5 c6 c7 c12
  have hB2 : BoxAt s2 (s.core.ptrs 14 - 2 * m) (setCoord lo k (thi ⟨k, hk⟩)) hi := by
    refine boxAt_set_lo (s := s1) (p := s.core.ptrs 54) ?_ k hk _ (fun z hz hz' => c5 z hz hz') c6
    unfold BoxAt; rw [g14]; exact hB
  have P2 : ∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → x ≠ 57 → s2.core.ptrs x = s1.core.ptrs x := c8
  have s2p1 : 1 ≤ s2.core.ptrs 1 := by rw [P2 1 (by decide) (by decide) (by decide) (by decide), s1p1]; exact_mod_cast hm
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩ :=
    seg_r4 Q off hE s2 (by rw [c1]; rfl) c2 s2p1
  generalize hs3 : run Q s2 detTape 18 = s3 at *
  have z2 : s2.core.ptrs 13 = s.core.ptrs 13 - 4 := by rw [P2 13 (by decide) (by decide) (by decide) (by decide), g3]
  have u2 : s2.core.ptrs 52 = s.core.ptrs 13 - 4 := by rw [P2 52 (by decide) (by decide) (by decide) (by decide), g6]
  have sp2 : s2.core.ptrs 42 = s.core.ptrs 42 := by
    rw [P2 42 (by decide) (by decide) (by decide) (by decide), P1 42 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  simp only [z2, u2, sp2, c4] at r3 r4 r9 r13 r14 r15 r16 r18
  have P3 : ∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 →
      s3.core.ptrs x = s2.core.ptrs x := r10
  have s3p1 : s3.core.ptrs 1 = m := by
    rw [P3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      P2 1 (by decide) (by decide) (by decide) (by decide), s1p1]
  have s3p60 : s3.core.ptrs 60 = 2 * m := by
    rw [P3 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      P2 60 (by decide) (by decide) (by decide) (by decide), s1p60]
  have s3p69 : s3.core.ptrs 69 = 0 := by
    rw [P3 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      P2 69 (by decide) (by decide) (by decide) (by decide), s1p69]
  have s3p14 : s3.core.ptrs 14 = s.core.ptrs 14 - 2 * m := by
    rw [P3 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), c3]
  have s3p50 : s3.core.ptrs 50 = s.core.ptrs 54 := by
    rw [r5, P2 54 (by decide) (by decide) (by decide) (by decide),
      P1 54 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have s3p51 : s3.core.ptrs 51 = m + k := by
    rw [r6, P2 53 (by decide) (by decide) (by decide) (by decide),
      P1 53 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h53,
      P2 1 (by decide) (by decide) (by decide) (by decide), s1p1]
  have s3r44 : s3.core.regs 44 = thi ⟨k, hk⟩ := by rw [r11, c9 44 (by decide), g10]
  obtain ⟨t4, ht4, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩ :=
    cs_part Q off hE 5 (by decide) s3 r1 r2 hm s3p1 s3p60 r8 s3p69 (by rw [s3p14, s3p50]; omega)
  generalize hs4 : run Q s3 detTape t4 = s4 at *
  simp only [s3p14, s3p50, s3p51, s3r44] at d3 d4 d5 d6 d7 d12
  have hB4 : BoxAt s4 (s.core.ptrs 14 - 2 * m - 2 * m) lo (setCoord hi k (thi ⟨k, hk⟩)) := by
    refine boxAt_set_hi (s := s3) (p := s.core.ptrs 54) ?_ k hk _ (fun z hz hz' => d5 z hz hz') d6
    intro jj; have := jj.isLt
    rw [r12, c7 _ (cs_frame (by positivity) (by omega) (Or.inr (by omega))),
      c7 _ (cs_frame (by positivity) (by omega) (Or.inr (by omega))), g14]
    exact hB jj
  have P4 : ∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → x ≠ 57 → s4.core.ptrs x = s3.core.ptrs x := d8
  have s4p1 : 1 ≤ s4.core.ptrs 1 := by rw [P4 1 (by decide) (by decide) (by decide) (by decide), s3p1]; exact_mod_cast hm
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11⟩ := seg_r5 Q off hE s4 (by rw [d1]; rfl) d2 s4p1
  generalize hs5 : run Q s4 detTape 6 = s5 at *
  have hk0 : (k : ℤ) < m := by exact_mod_cast hk
  have PP : ∀ x, x ≠ 13 → x ≠ 14 → x ≠ 42 → x ≠ 46 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 54 → x ≠ 55 → x ≠ 56 →
      x ≠ 57 → x ≠ 58 → x ≠ 62 → x ≠ 53 → s5.core.ptrs x = s.core.ptrs x := by
    intro x a b c d e f g h i j k' l o q
    rw [w6 x q h i, P4 x b d j k', P3 x a c e f k' l o, P2 x b d j k', P1 x a e f g k' l]
  have p13 : s5.core.ptrs 13 = s.core.ptrs 13 - 7 := by
    rw [w6 13 (by decide) (by decide) (by decide), P4 13 (by decide) (by decide) (by decide) (by decide), r3]; ring
  have p14 : s5.core.ptrs 14 = s.core.ptrs 14 - 4 * m := by
    rw [w6 14 (by decide) (by decide) (by decide), d3]; ring
  have I5 : s5.integerMemory = s3.integerMemory := by rw [w9, d10]
  have hI : ∀ z, z ≠ s.core.ptrs 13 - 4 - 3 → z ≠ s.core.ptrs 13 - 4 - 2 → z ≠ s.core.ptrs 13 - 4 - 1 →
      s5.integerMemory z = s1.integerMemory z := fun z a b c => by rw [I5, r16 z a b c, c10]
  have hM : ∀ z, (z < s.core.ptrs 14 - 4 * m ∨ s.core.ptrs 14 ≤ z) → s5.core.mem z = s.core.mem z := by
    intro z hz
    rw [w8, d7 z (cs_frame (by positivity) (by omega) (by omega)), r12,
      c7 z (cs_frame (by positivity) (by omega) (by omega)), g14]
  have hrun : run Q s detTape (22 + t2 + 18 + t4 + 6) = s5 := by
    rw [run_add, run_add, run_add, run_add, hs1, hs2, hs3, hs4, hs5]
  refine ⟨22 + t2 + 18 + t4 + 6, s5, ⟨hrun, by rw [w10, d11, r17, c11, g19]; ring, by rw [p13]; clear * -; omega,
    by rw [p14]; clear * -; omega, fun x hx a b => PP x a b (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega),
    PP 59 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    fun x hx => by
      rw [w7, d9 x (by clear * - hx; omega), r11, c9 x (by clear * - hx; omega),
        g13 x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)],
    fun z hz hne => by
      rw [p13] at hz
      rw [hI z (by clear * - hz; omega) (by clear * - hz; omega) (by clear * - hz; omega),
        g18 z (by clear * - hz; omega) (by clear * - hz; omega) hne],
    fun z hz => hM z (by rw [p14] at hz; exact hz), ?_⟩, by clear * - ht2 ht4; omega, w1, w2, ?_, p13, p14,
    by rw [w6 42 (by decide) (by decide) (by decide), P4 42 (by decide) (by decide) (by decide) (by decide), r4]; ring,
    PP 48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [w3, P4 53 (by decide) (by decide) (by decide) (by decide), P3 53 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), P2 53 (by decide) (by decide) (by decide) (by decide),
      P1 53 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h53],
    by rw [w4, d4]; ring,
    by rw [w5, P4 52 (by decide) (by decide) (by decide) (by decide), P3 52 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), u2]; ring,
    by rw [hI _ (by clear * -; omega) (by clear * -; omega) (by clear * -; omega), g15, e68],
    by rw [hI _ (by clear * -; omega) (by clear * -; omega) (by clear * -; omega), g16],
    by rw [hI _ (by clear * - hcsl; omega) (by clear * - hcsl; omega) (by clear * - hcsl; omega), g17],
    by rw [I5, show s.core.ptrs 13 - 7 = s.core.ptrs 13 - 4 - 3 by ring, r13],
    by rw [I5, show s.core.ptrs 13 - 6 = s.core.ptrs 13 - 4 - 2 by ring, r14]; ring,
    by rw [I5, show s.core.ptrs 13 - 5 = s.core.ptrs 13 - 4 - 1 by ring, r15], ?_, ?_⟩
  · intro w hw
    have e2 : run Q s detTape (22 + t2) = s2 := by rw [run_add, hs1, hs2]
    have e3 : run Q s detTape (22 + t2 + 18) = s3 := by rw [run_add, e2, hs3]
    have e4 : run Q s detTape (22 + t2 + 18 + t4) = s4 := by rw [run_add, e3, hs4]
    rw [cellsWritten_add Q s _ 6, e4, w11, Finset.union_empty, cellsWritten_add Q s _ t4, e3,
      cellsWritten_add Q s _ 18, e2, cellsWritten_add Q s 22 t2, hs1] at hw
    simp only [Finset.mem_union, or_assoc] at hw
    rcases hw with hw | hw | hw | hw
    · rcases g20 w hw with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, Or.inl ⟨by rw [p13]; clear * -; omega, by clear * -; omega⟩⟩
      · exact Or.inl ⟨rfl, Or.inl ⟨by rw [p13]; clear * -; omega, by clear * -; omega⟩⟩
      · exact Or.inl ⟨rfl, Or.inr rfl⟩
    · obtain ⟨e1, e2⟩ := c12 w hw
      refine Or.inr ⟨e1, ?_⟩
      rw [p14]; rcases e2 with ⟨a, b⟩ | e2
      · exact ⟨by clear * - a; omega, b⟩
      · rw [e2]; exact ⟨by clear * - hk0; omega, by clear * - hk0; omega⟩
    · rcases r18 w hw with rfl | rfl | rfl <;>
        exact Or.inl ⟨rfl, Or.inl ⟨by rw [p13]; clear * -; omega, by clear * -; omega⟩⟩
    · obtain ⟨e1, e2⟩ := d12 w hw
      refine Or.inr ⟨e1, ?_⟩
      rw [p14]; rcases e2 with ⟨a, b⟩ | e2
      · exact ⟨by clear * - a; omega, by clear * - b; omega⟩
      · rw [e2]; exact ⟨by clear * - hk0; omega, by clear * - hk0; omega⟩
  · exact env_of hEnv0 (fun x hx a b c => PP x a b (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega))
      (fun x hx => by
        rw [w7, d9 x (by clear * - hx; omega), r11, c9 x (by clear * - hx; omega),
          g13 x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)])
      (fun z hz => by
        rw [hI z (by clear * - hz hZ; omega) (by clear * - hz hZ; omega) (by clear * - hz hZ; omega),
          g18 z (by clear * - hz hZ; omega) (by clear * - hz hZ; omega) (by clear * - hz hcsl0; omega)])
      (fun z hz => hM z (Or.inr (by clear * - hz hR; omega)))
  · intro jj; have := jj.isLt
    rw [w8, d7 _ (cs_frame (by positivity) (by clear * - hk0; omega) (Or.inr (by clear * -; omega))),
      d7 _ (cs_frame (by positivity) (by clear * - hk0; omega) (Or.inr (by clear * -; omega))), r12]
    exact hB2 jj
  · rw [show s.core.ptrs 14 - 4 * m = s.core.ptrs 14 - 2 * m - 2 * m by ring]
    unfold BoxAt; rw [w8]; exact hB4

theorem peel_specs' :
    (∀ {m n : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (lo hi : Fin m → ℝ) (s : State) (hpc : s.core.pc = off + 197) (hh : s.halted = false) (hEnv : Env s pts r c Z0) (h52 : s.core.regs 52 = sigma lo hi) (hc : ¬ (s.core.regs 51 + s.core.regs 51 - s.core.regs 52 ≤ 0)) (hB : BoxAt s (s.core.ptrs 43) lo hi) (hsl : s.core.ptrs 13 ≤ s.core.ptrs 44) (hp : s.core.ptrs 14 ≤ s.core.ptrs 43),
      ∃ (t : ℕ) (s' : State) (k : Fin m), run Q s detTape t = s' ∧ t ≤ 37 * m + 91 ∧ longestAxis lo hi = some k ∧ s'.core.pc = off + 34 ∧ s'.halted = false ∧ s'.core.ptrs 13 = s.core.ptrs 13 - 10 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 42 = s.core.ptrs 13 - 10 ∧ s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 43 ∧ s'.integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 4 ∧ s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧ s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 ∧ s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧ s'.integerMemory (s.core.ptrs 13 - 10) = s.core.ptrs 14 - 4 * m ∧ s'.integerMemory (s.core.ptrs 13 - 9) = s.core.ptrs 13 - 1 ∧ s'.integerMemory (s.core.ptrs 13 - 8) = s.core.ptrs 13 - 7 ∧ BoxAt s' (s.core.ptrs 14 - 2 * m) lo (setCoord hi k ((lo k + hi k) / 2)) ∧ BoxAt s' (s.core.ptrs 14 - 4 * m) (setCoord lo k ((lo k + hi k) / 2)) hi ∧ (∀ x, (x < 13 ∨ (14 < x ∧ x < 42) ∨ x = 40 ∨ x = 59 ∨ x = 60 ∨ x = 68 ∨ x = 69) → s'.core.ptrs x = s.core.ptrs x) ∧ (∀ x, (x < 44 ∨ x = 49 ∨ x = 50 ∨ x = 53) → s'.core.regs x = s.core.regs x) ∧ (∀ z, (z < s.core.ptrs 14 - 4 * m ∨ s.core.ptrs 14 ≤ z) → s'.core.mem z = s.core.mem z) ∧ (∀ z, (z < s.core.ptrs 13 - 10 ∨ s.core.ptrs 13 ≤ z) → z ≠ s.core.ptrs 44 → s'.integerMemory z = s.integerMemory z) ∧ s'.work = s.work + t ∧ (∀ w ∈ cellsWritten Q s t, (w.1 = false ∧ ((s.core.ptrs 13 - 10 ≤ w.2 ∧ w.2 < s.core.ptrs 13) ∨ w.2 = s.core.ptrs 44)) ∨ (w.1 = true ∧ s.core.ptrs 14 - 4 * m ≤ w.2 ∧ w.2 < s.core.ptrs 14))) ∧
    (∀ {m n : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false) (hEnv : Env s pts r c Z0) (k : ℕ) (hk : k < m) (h53 : s.core.ptrs 53 = k) (tlo thi lo hi : Fin m → ℝ) (hQ : BoxAt s (s.core.ptrs 48) tlo thi) (hB : BoxAt s (s.core.ptrs 54) lo hi) (hlow : lo ⟨k, hk⟩ < tlo ⟨k, hk⟩) (hcsl : s.core.ptrs 13 ≤ s.core.ptrs 55) (hcb : s.core.ptrs 14 ≤ s.core.ptrs 54) (hq : s.core.ptrs 14 ≤ s.core.ptrs 48) (hZ : s.core.ptrs 13 ≤ 0) (hcsl0 : s.core.ptrs 55 < 0) (hR : s.core.ptrs 14 ≤ 0),
      ∃ (t : ℕ) (s' : State), Fr Q s s' t (fun z => z = s.core.ptrs 55) ∧ t ≤ 28 * m + 80 ∧ s'.core.pc = off + 326 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧ s'.core.ptrs 13 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 42 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 48 = s.core.ptrs 48 ∧ s'.core.ptrs 53 = k ∧ s'.core.ptrs 54 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 55 = s.core.ptrs 13 - 1 ∧ s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ s'.integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧ s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧ s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 ∧ s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧ BoxAt s' (s.core.ptrs 14 - 2 * m) lo (setCoord hi k (tlo ⟨k, hk⟩)) ∧ BoxAt s' (s.core.ptrs 14 - 4 * m) (setCoord lo k (tlo ⟨k, hk⟩)) hi) ∧
    (∀ {m n : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (s : State) (hpc : s.core.pc = off + 326) (hh : s.halted = false) (hEnv : Env s pts r c Z0) (k : ℕ) (hk : k < m) (h53 : s.core.ptrs 53 = k) (tlo thi lo hi : Fin m → ℝ) (hQ : BoxAt s (s.core.ptrs 48) tlo thi) (hB : BoxAt s (s.core.ptrs 54) lo hi) (hhigh : hi ⟨k, hk⟩ > thi ⟨k, hk⟩) (hcsl : s.core.ptrs 13 ≤ s.core.ptrs 55) (hcb : s.core.ptrs 14 ≤ s.core.ptrs 54) (hq : s.core.ptrs 14 ≤ s.core.ptrs 48) (hZ : s.core.ptrs 13 ≤ 0) (hcsl0 : s.core.ptrs 55 < 0) (hR : s.core.ptrs 14 ≤ 0),
      ∃ (t : ℕ) (s' : State), Fr Q s s' t (fun z => z = s.core.ptrs 55) ∧ t ≤ 28 * m + 80 ∧ s'.core.pc = off + 283 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧ s'.core.ptrs 13 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 42 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 48 = s.core.ptrs 48 ∧ s'.core.ptrs 53 = k + 1 ∧ s'.core.ptrs 54 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 55 = s.core.ptrs 13 - 2 ∧ s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ s'.integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧ s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧ s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 1 ∧ s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧ BoxAt s' (s.core.ptrs 14 - 2 * m) (setCoord lo k (thi ⟨k, hk⟩)) hi ∧ BoxAt s' (s.core.ptrs 14 - 4 * m) lo (setCoord hi k (thi ⟨k, hk⟩))) :=
  ⟨split_pre, axis_low, axis_high⟩

end DetANN.HPIM.BD.SP

namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM

theorem _root_.solution :
    (∀ {m n : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (lo hi : Fin m → ℝ) (s : State) (hpc : s.core.pc = off + 197) (hh : s.halted = false) (hEnv : Env s pts r c Z0) (h52 : s.core.regs 52 = sigma lo hi) (hc : ¬ (s.core.regs 51 + s.core.regs 51 - s.core.regs 52 ≤ 0)) (hB : BoxAt s (s.core.ptrs 43) lo hi) (hsl : s.core.ptrs 13 ≤ s.core.ptrs 44) (hp : s.core.ptrs 14 ≤ s.core.ptrs 43),
      ∃ (t : ℕ) (s' : State) (k : Fin m), run Q s detTape t = s' ∧ t ≤ 37 * m + 91 ∧ longestAxis lo hi = some k ∧ s'.core.pc = off + 34 ∧ s'.halted = false ∧ s'.core.ptrs 13 = s.core.ptrs 13 - 10 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 42 = s.core.ptrs 13 - 10 ∧ s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 43 ∧ s'.integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 4 ∧ s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧ s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 ∧ s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧ s'.integerMemory (s.core.ptrs 13 - 10) = s.core.ptrs 14 - 4 * m ∧ s'.integerMemory (s.core.ptrs 13 - 9) = s.core.ptrs 13 - 1 ∧ s'.integerMemory (s.core.ptrs 13 - 8) = s.core.ptrs 13 - 7 ∧ BoxAt s' (s.core.ptrs 14 - 2 * m) lo (setCoord hi k ((lo k + hi k) / 2)) ∧ BoxAt s' (s.core.ptrs 14 - 4 * m) (setCoord lo k ((lo k + hi k) / 2)) hi ∧ (∀ x, (x < 13 ∨ (14 < x ∧ x < 42) ∨ x = 40 ∨ x = 59 ∨ x = 60 ∨ x = 68 ∨ x = 69) → s'.core.ptrs x = s.core.ptrs x) ∧ (∀ x, (x < 44 ∨ x = 49 ∨ x = 50 ∨ x = 53) → s'.core.regs x = s.core.regs x) ∧ (∀ z, (z < s.core.ptrs 14 - 4 * m ∨ s.core.ptrs 14 ≤ z) → s'.core.mem z = s.core.mem z) ∧ (∀ z, (z < s.core.ptrs 13 - 10 ∨ s.core.ptrs 13 ≤ z) → z ≠ s.core.ptrs 44 → s'.integerMemory z = s.integerMemory z) ∧ s'.work = s.work + t ∧ (∀ w ∈ cellsWritten Q s t, (w.1 = false ∧ ((s.core.ptrs 13 - 10 ≤ w.2 ∧ w.2 < s.core.ptrs 13) ∨ w.2 = s.core.ptrs 44)) ∨ (w.1 = true ∧ s.core.ptrs 14 - 4 * m ≤ w.2 ∧ w.2 < s.core.ptrs 14))) ∧
    (∀ {m n : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false) (hEnv : Env s pts r c Z0) (k : ℕ) (hk : k < m) (h53 : s.core.ptrs 53 = k) (tlo thi lo hi : Fin m → ℝ) (hQ : BoxAt s (s.core.ptrs 48) tlo thi) (hB : BoxAt s (s.core.ptrs 54) lo hi) (hlow : lo ⟨k, hk⟩ < tlo ⟨k, hk⟩) (hcsl : s.core.ptrs 13 ≤ s.core.ptrs 55) (hcb : s.core.ptrs 14 ≤ s.core.ptrs 54) (hq : s.core.ptrs 14 ≤ s.core.ptrs 48) (hZ : s.core.ptrs 13 ≤ 0) (hcsl0 : s.core.ptrs 55 < 0) (hR : s.core.ptrs 14 ≤ 0),
      ∃ (t : ℕ) (s' : State), Fr Q s s' t (fun z => z = s.core.ptrs 55) ∧ t ≤ 28 * m + 80 ∧ s'.core.pc = off + 326 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧ s'.core.ptrs 13 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 42 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 48 = s.core.ptrs 48 ∧ s'.core.ptrs 53 = k ∧ s'.core.ptrs 54 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 55 = s.core.ptrs 13 - 1 ∧ s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ s'.integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧ s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧ s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 ∧ s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧ BoxAt s' (s.core.ptrs 14 - 2 * m) lo (setCoord hi k (tlo ⟨k, hk⟩)) ∧ BoxAt s' (s.core.ptrs 14 - 4 * m) (setCoord lo k (tlo ⟨k, hk⟩)) hi) ∧
    (∀ {m n : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (s : State) (hpc : s.core.pc = off + 326) (hh : s.halted = false) (hEnv : Env s pts r c Z0) (k : ℕ) (hk : k < m) (h53 : s.core.ptrs 53 = k) (tlo thi lo hi : Fin m → ℝ) (hQ : BoxAt s (s.core.ptrs 48) tlo thi) (hB : BoxAt s (s.core.ptrs 54) lo hi) (hhigh : hi ⟨k, hk⟩ > thi ⟨k, hk⟩) (hcsl : s.core.ptrs 13 ≤ s.core.ptrs 55) (hcb : s.core.ptrs 14 ≤ s.core.ptrs 54) (hq : s.core.ptrs 14 ≤ s.core.ptrs 48) (hZ : s.core.ptrs 13 ≤ 0) (hcsl0 : s.core.ptrs 55 < 0) (hR : s.core.ptrs 14 ≤ 0),
      ∃ (t : ℕ) (s' : State), Fr Q s s' t (fun z => z = s.core.ptrs 55) ∧ t ≤ 28 * m + 80 ∧ s'.core.pc = off + 283 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧ s'.core.ptrs 13 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 42 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 48 = s.core.ptrs 48 ∧ s'.core.ptrs 53 = k + 1 ∧ s'.core.ptrs 54 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 55 = s.core.ptrs 13 - 2 ∧ s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ s'.integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧ s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧ s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 1 ∧ s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧ BoxAt s' (s.core.ptrs 14 - 2 * m) (setCoord lo k (thi ⟨k, hk⟩)) hi ∧ BoxAt s' (s.core.ptrs 14 - 4 * m) lo (setCoord hi k (thi ⟨k, hk⟩))) :=
  DetANN.HPIM.BD.SP.peel_specs'

end DetANN.HPIM.BD
