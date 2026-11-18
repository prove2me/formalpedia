-- Prove2me | solution 1 for DetANN.HPIM.BD.loop_specs
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T21:38:21.935206+00:00
-- url     : https://prove2.me/submissions/98816916-a0c9-41c8-b490-3b4f11b18130

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
import Theorems.Thm_DetANN_HPIM_BD_scan_steps
import Theorems.Thm_DetANN_HPIM_BD_split_steps

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

end DetANN.HPIM.PP

-- ===== BD_SegA =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

/-- One step of the root box copy. -/
lemma icp_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State)
    (hpc : s.core.pc = off + 13) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 17 + s.core.ptrs 46) = x)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 60)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 7).core.pc = off + 13 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 7).core.ptrs 50 = s.core.ptrs 43 + s.core.ptrs 46 ∧
      (∀ x, x ≠ 46 → x ≠ 50 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 55 = x ∧
      (∀ x, x ≠ 55 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem (s.core.ptrs 43 + s.core.ptrs 46) = x ∧
      (∀ z, z ≠ s.core.ptrs 43 + s.core.ptrs 46 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 43 + s.core.ptrs 46) :=
  scan_steps.2.1 Q off hE x s hpc hh fr0 hb0 hm1

lemma icp_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 13) (hh : s.halted = false)
    (hb0 : s.core.ptrs 60 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 20 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ :=
  scan_steps.2.2.1 Q off hE s hpc hh hb0 hm1

lemma dl_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 53) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 86 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

/-- One coordinate of both squared distances. -/
lemma dl_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x lo hi : ℝ) (s : State)
    (hpc : s.core.pc = off + 53) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x)
    (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = lo)
    (fr2 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = hi)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 1)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 33).core.pc = off + 53 ∧
      (run Q s detTape 33).halted = false ∧
      (run Q s detTape 33).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 33).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 33).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 33).core.regs 42 = (s.core.regs 42 + (((((lo - x) + (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) + Real.sqrt (((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) * ((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)))) / s.core.regs 53) * ((((lo - x) + (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) + Real.sqrt (((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) * ((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)))) / s.core.regs 53))) ∧
      (run Q s detTape 33).core.regs 43 = (s.core.regs 43 + (((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) * ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53))) ∧
      (run Q s detTape 33).core.regs 44 = x ∧
      (run Q s detTape 33).core.regs 45 = lo ∧
      (run Q s detTape 33).core.regs 46 = hi ∧
      (run Q s detTape 33).core.regs 47 = ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) ∧
      (run Q s detTape 33).core.regs 48 = (hi - x) ∧
      (run Q s detTape 33).core.regs 54 = (((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) * ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53)) ∧
      (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 47 → x ≠ 48 → x ≠ 54 → (run Q s detTape 33).core.regs x = s.core.regs x) ∧
      (run Q s detTape 33).core.mem = s.core.mem ∧
      (run Q s detTape 33).integerMemory = s.integerMemory ∧
      (run Q s detTape 33).work = s.work + 33 ∧
      cellsWritten Q s 33 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.1 Q off hE x lo hi s hpc hh fr0 fr1 fr2 hb0 hm1

lemma up_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 93) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 126 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

/-- One coordinate of the running min and max. -/
lemma up_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x mn mx : ℝ) (s : State)
    (hpc : s.core.pc = off + 93) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x)
    (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = mn)
    (fr2 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = mx)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 1)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 23).core.pc = off + 93 ∧
      (run Q s detTape 23).halted = false ∧
      (run Q s detTape 23).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 23).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 23).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 23).core.regs 44 = x ∧
      (run Q s detTape 23).core.regs 45 = mx ∧
      (run Q s detTape 23).core.regs 47 = (((mx + x) + Real.sqrt ((mx - x) * (mx - x))) / s.core.regs 53) ∧
      (run Q s detTape 23).core.regs 54 = Real.sqrt ((mx - x) * (mx - x)) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 23).core.regs x = s.core.regs x) ∧
      (run Q s detTape 23).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = (((mn + x) - Real.sqrt ((mn - x) * (mn - x))) / s.core.regs 53) ∧
      (run Q s detTape 23).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = (((mx + x) + Real.sqrt ((mx - x) * (mx - x))) / s.core.regs 53) ∧
      (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 23).core.mem z = s.core.mem z) ∧
      (run Q s detTape 23).integerMemory = s.integerMemory ∧
      (run Q s detTape 23).work = s.work + 23 ∧
      ∀ c ∈ cellsWritten Q s 23, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE x mn mx s hpc hh fr0 fr1 fr2 hb0 hm1

lemma fi_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State)
    (hpc : s.core.pc = off + 116) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 1)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 9).core.pc = off + 116 ∧
      (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 9).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs 44 = x ∧
      (∀ x, x ≠ 44 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧
      (run Q s detTape 9).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = x ∧
      (run Q s detTape 9).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = x ∧
      (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 9).core.mem z = s.core.mem z) ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧
      ∀ c ∈ cellsWritten Q s 9, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE x s hpc hh fr0 hb0 hm1

lemma fi_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 116) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 2).core.pc = off + 126 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 49 = 1 ∧
      (∀ x, x ≠ 49 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

end DetANN.HPIM.BD

-- ===== BD_SegB =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

lemma tb_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 134) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 161 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ :=
  split_steps.1 Q off hE s hpc hh hb0 hm1

/-- One coordinate of the tight box. -/
lemma tb_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (mn lo mx hi : ℝ) (s : State)
    (hpc : s.core.pc = off + 134) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = mn)
    (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = lo)
    (fr2 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = mx)
    (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = hi)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 1)
    (hm1 : 1 ≤ s.core.ptrs 1)
    (hx0 : s.core.ptrs 48 < s.core.ptrs 43) :
    (run Q s detTape 27).core.pc = off + 134 ∧
      (run Q s detTape 27).halted = false ∧
      (run Q s detTape 27).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 27).core.ptrs 50 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (run Q s detTape 27).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 50 → x ≠ 57 → (run Q s detTape 27).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 27).core.regs 44 = (mx + s.core.regs 49) ∧
      (run Q s detTape 27).core.regs 45 = hi ∧
      (run Q s detTape 27).core.regs 47 = ((((mx + s.core.regs 49) + hi) - Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi))) / s.core.regs 53) ∧
      (run Q s detTape 27).core.regs 54 = Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi)) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 27).core.regs x = s.core.regs x) ∧
      (run Q s detTape 27).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = ((((mn - s.core.regs 49) + lo) + Real.sqrt (((mn - s.core.regs 49) - lo) * ((mn - s.core.regs 49) - lo))) / s.core.regs 53) ∧
      (run Q s detTape 27).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = ((((mx + s.core.regs 49) + hi) - Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi))) / s.core.regs 53) ∧
      (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 27).core.mem z = s.core.mem z) ∧
      (run Q s detTape 27).integerMemory = s.integerMemory ∧
      (run Q s detTape 27).work = s.work + 27 ∧
      ∀ c ∈ cellsWritten Q s 27, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) :=
  split_steps.2.1 Q off hE mn lo mx hi s hpc hh fr0 fr1 fr2 fr3 hb0 hm1 hx0

lemma sg_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 172) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 197 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ :=
  split_steps.2.2.2.1 Q off hE s hpc hh hb0 hm1

/-- One coordinate of both longest sides. -/
lemma sg_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b c d : ℝ) (s : State)
    (hpc : s.core.pc = off + 172) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = a)
    (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = b)
    (fr2 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = c)
    (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = d)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 1)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 25).core.pc = off + 172 ∧
      (run Q s detTape 25).halted = false ∧
      (run Q s detTape 25).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 25).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 25).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 25).core.regs 44 = c ∧
      (run Q s detTape 25).core.regs 45 = d ∧
      (run Q s detTape 25).core.regs 47 = (d - c) ∧
      (run Q s detTape 25).core.regs 51 = (((s.core.regs 51 + (b - a)) + Real.sqrt ((s.core.regs 51 - (b - a)) * (s.core.regs 51 - (b - a)))) / s.core.regs 53) ∧
      (run Q s detTape 25).core.regs 52 = (((s.core.regs 52 + (d - c)) + Real.sqrt ((s.core.regs 52 - (d - c)) * (s.core.regs 52 - (d - c)))) / s.core.regs 53) ∧
      (run Q s detTape 25).core.regs 54 = Real.sqrt ((s.core.regs 52 - (d - c)) * (s.core.regs 52 - (d - c))) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 51 → x ≠ 52 → x ≠ 54 → (run Q s detTape 25).core.regs x = s.core.regs x) ∧
      (run Q s detTape 25).core.mem = s.core.mem ∧
      (run Q s detTape 25).integerMemory = s.integerMemory ∧
      (run Q s detTape 25).work = s.work + 25 ∧
      cellsWritten Q s 25 = ∅ :=
  split_steps.2.2.2.2.1 Q off hE a b c d s hpc hh fr0 fr1 fr2 fr3 hb0 hm1

lemma la_next (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b : ℝ) (s : State)
    (hpc : s.core.pc = off + 201) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53) = a)
    (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1) = b)
    (hb0 : ¬ (s.core.regs 52 - (b - a)) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 9).core.pc = off + 201 ∧
      (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 53 = s.core.ptrs 53 + 1 ∧
      (run Q s detTape 9).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 53 → x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs 44 = a ∧
      (run Q s detTape 9).core.regs 45 = b ∧
      (run Q s detTape 9).core.regs 47 = (b - a) ∧
      (run Q s detTape 9).core.regs 54 = (s.core.regs 52 - (b - a)) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧
      (run Q s detTape 9).core.mem = s.core.mem ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧
      cellsWritten Q s 9 = ∅ :=
  split_steps.2.2.2.2.2.2.2.1 Q off hE a b s hpc hh fr0 fr1 hb0 hm1

lemma la_found (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b : ℝ) (s : State)
    (hpc : s.core.pc = off + 201) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53) = a)
    (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1) = b)
    (hb0 : (s.core.regs 52 - (b - a)) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 7).core.pc = off + 210 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 44 = a ∧
      (run Q s detTape 7).core.regs 45 = b ∧
      (run Q s detTape 7).core.regs 47 = (b - a) ∧
      (run Q s detTape 7).core.regs 54 = (s.core.regs 52 - (b - a)) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      cellsWritten Q s 7 = ∅ :=
  split_steps.2.2.2.2.2.2.2.2.1 Q off hE a b s hpc hh fr0 fr1 hb0 hm1

lemma cl_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State)
    (hpc : s.core.pc = off + 261) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 50 + s.core.ptrs 46) = x)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 60)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 7).core.pc = off + 261 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 56 + s.core.ptrs 46 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 55 = x ∧
      (∀ x, x ≠ 55 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem (s.core.ptrs 56 + s.core.ptrs 46) = x ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 46 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 56 + s.core.ptrs 46) :=
  split_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE x s hpc hh fr0 hb0 hm1

lemma cl_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 261) (hh : s.halted = false)
    (hb0 : s.core.ptrs 60 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 268 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ :=
  split_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

end DetANN.HPIM.BD

-- ===== BD_Math =====
namespace DetANN.HPIM.BD

open DetANN.HPIM DetANN.HPIM.BS

variable {m n : ℕ}

lemma psum_succ (g : Fin m → ℝ) {k : ℕ} (hk : k < m) : psum g (k + 1) = psum g k + g ⟨k, hk⟩ := by
  unfold psum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hk⟩ : Fin m)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hk⟩ : Fin m))]
  simp only [lt_add_one, if_true, lt_irrefl, if_false, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have : (j : ℕ) ≠ k := fun h => (Finset.mem_erase.1 hj).1 (Fin.ext h)
  by_cases h : (j : ℕ) < k
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

lemma psum_all (g : Fin m → ℝ) : psum g m = ∑ j, g j := by
  unfold psum
  exact Finset.sum_congr rfl fun j _ => if_pos j.isLt

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

lemma sqrt_sq_abs (a : ℝ) : Real.sqrt (a * a) = |a| := Real.sqrt_mul_self_eq_abs a

lemma max2 (a b : ℝ) : ((a + b) + Real.sqrt ((a - b) * (a - b))) / 2 = max a b := by
  rw [sqrt_sq_abs]
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith), max_eq_right h]; ring
  · rw [abs_of_nonneg (by linarith), max_eq_left h]; ring

lemma min2 (a b : ℝ) : ((a + b) - Real.sqrt ((a - b) * (a - b))) / 2 = min a b := by
  rw [sqrt_sq_abs]
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith), min_eq_left h]; ring
  · rw [abs_of_nonneg (by linarith), min_eq_right h]; ring

lemma max0 (y : ℝ) : (y + Real.sqrt (y * y)) / 2 = max 0 y := by
  have := max2 y 0
  simp only [add_zero, sub_zero] at this
  rw [this, max_comm]

end DetANN.HPIM.BD

-- ===== BD_PrfL =====
namespace DetANN.HPIM.BD.SL

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

lemma dl_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (lo hi pt : Fin m → ℝ) :
    ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 53 → s.halted = false →
      s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 →
      (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) → BoxAt s (s.core.ptrs 43) lo hi →
      s.core.regs 42 = psum (t1 lo hi pt) j → s.core.regs 43 = psum (t2 lo hi pt) j →
      ∃ t, t ≤ 33 * k + 1 ∧ (run Q s detTape t).core.pc = off + 86 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.regs 42 = boxDist2 lo hi pt ∧
        (run Q s detTape t).core.regs 43 = boxMaxDist2 lo hi pt ∧
        (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 47 → x ≠ 48 → x ≠ 54 →
          (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ := by
  intro k
  induction k with
  | zero =>
    intro j s hjk hpc hh h1 hm h46 h53 _ _ h42 h43
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
      dl_exit Q off hE s hpc hh (by rw [h1, h46]; omega) (by rw [h1]; exact_mod_cast hm)
    refine ⟨1, by omega, g1, g2, ?_, ?_, fun x _ _ => by rw [g3], fun x _ _ _ _ _ _ _ _ => by rw [g4],
      g5, g6, g7, g8⟩
    · rw [g4, h42, show j = m by omega, psum_all]; rfl
    · rw [g4, h43, show j = m by omega, psum_all]; rfl
  | succ k ih =>
    intro j s hjk hpc hh h1 hm h46 h53 hpt hB h42 h43
    have hj : j < m := by omega
    have e0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = pt ⟨j, hj⟩ := by rw [h46]; exact hpt ⟨j, hj⟩
    have e1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = lo ⟨j, hj⟩ := by rw [h46]; exact (hB ⟨j, hj⟩).1
    have e2 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = hi ⟨j, hj⟩ := by
      rw [h46, h1]; exact (hB ⟨j, hj⟩).2
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩ :=
      dl_step Q off hE _ _ _ s hpc hh e0 e1 e2 (by rw [h1, h46]; exact_mod_cast hj) (by rw [h1]; exact_mod_cast hm)
    set s1 := run Q s detTape 33 with hs1
    have r53 : s1.core.regs 53 = 2 := by rw [g14 53 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h53]
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
      ih (j + 1) s1 (by omega) g1 g2 (by rw [g5 1 (by decide) (by decide), h1]) hm (by rw [g3, h46]; push_cast; ring)
        r53 (by intro jj; rw [g5 47 (by decide) (by decide), g15]; exact hpt jj)
        (by rw [g5 43 (by decide) (by decide)]; unfold BoxAt; rw [g15]; exact hB)
        (by rw [g6, h42, h53, max0, max2, psum_succ _ hj, t1, sq])
        (by rw [g7, h43, h53, max2, psum_succ _ hj, t2, sq])
    refine ⟨33 + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, q3, q4, fun x x1 x2 => by rw [q5 x x1 x2, g5 x x1 x2],
      fun x x1 x2 x3 x4 x5 x6 x7 x8 => by rw [q6 x x1 x2 x3 x4 x5 x6 x7 x8, g14 x x1 x2 x3 x4 x5 x6 x7 x8],
      by rw [q7, g15], by rw [q8, g16], by rw [q9, g17]; ring, by rw [g18, q10]; simp⟩

/-- The near box `[mn, mx]` is stored at `q` in the layout of `BoxAt`. -/
lemma up_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pt mn0 mx0 : Fin m → ℝ) :
    ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 93 → s.halted = false →
      s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 →
      s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 47 →
      (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) →
      (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = min (mn0 jj) (pt jj) ∧
        s.core.mem (s.core.ptrs 48 + jj + m) = max (mx0 jj) (pt jj)) →
      (∀ jj : Fin m, j ≤ (jj : ℕ) → s.core.mem (s.core.ptrs 48 + jj) = mn0 jj ∧
        s.core.mem (s.core.ptrs 48 + jj + m) = mx0 jj) →
      ∃ t, t ≤ 23 * k + 1 ∧ (run Q s detTape t).core.pc = off + 126 ∧
        (run Q s detTape t).halted = false ∧
        BoxAt (run Q s detTape t) (s.core.ptrs 48) (fun jj => min (mn0 jj) (pt jj))
          (fun jj => max (mx0 jj) (pt jj)) ∧
        (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) →
          (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m := by
  intro k
  induction k with
  | zero =>
    intro j s hjk hpc hh h1 hm h46 h53 _ _ hlt _
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
      up_exit Q off hE s hpc hh (by rw [h1, h46]; omega) (by rw [h1]; exact_mod_cast hm)
    refine ⟨1, by omega, g1, g2, ?_, fun z _ => by rw [g5], fun x _ _ => by rw [g3],
      fun x _ _ _ _ => by rw [g4], g6, g7, by rw [g8]; simp⟩
    intro jj; rw [g5]; exact hlt jj (by omega)
  | succ k ih =>
    intro j s hjk hpc hh h1 hm h46 h53 hq hpt hlt hge
    have hj : j < m := by omega
    have e0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = pt ⟨j, hj⟩ := by rw [h46]; exact hpt ⟨j, hj⟩
    have e1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = mn0 ⟨j, hj⟩ := by
      rw [h46]; exact (hge ⟨j, hj⟩ le_rfl).1
    have e2 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = mx0 ⟨j, hj⟩ := by
      rw [h46, h1]; exact (hge ⟨j, hj⟩ le_rfl).2
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩ :=
      up_step Q off hE _ _ _ s hpc hh e0 e1 e2 (by rw [h1, h46]; exact_mod_cast hj) (by rw [h1]; exact_mod_cast hm)
    set s1 := run Q s detTape 23 with hs1
    have r53 : s1.core.regs 53 = 2 := by rw [g10 53 (by decide) (by decide) (by decide) (by decide), h53]
    have p47 := g5 47 (by decide) (by decide)
    have p48 := g5 48 (by decide) (by decide)
    rw [h53, min2, h46] at g11
    rw [h53, max2, h46, h1] at g12
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih (j + 1) s1 (by omega) g1 g2 (by rw [g5 1 (by decide) (by decide), h1]) hm
        (by rw [g3, h46]; push_cast; ring) r53 (by rw [p47, p48]; exact hq)
        (by intro jj; rw [p47, g13 _ (by have := jj.isLt; omega) (by have := jj.isLt; omega)]; exact hpt jj)
        (by
          intro jj hjj
          have := jj.isLt
          rw [p48]
          rcases Nat.lt_or_ge (jj : ℕ) j with h | h
          · rw [g13 (s.core.ptrs 48 + jj) (by omega) (by omega),
              g13 (s.core.ptrs 48 + jj + m) (by omega) (by omega)]; exact hlt jj h
          · have e : jj = ⟨j, hj⟩ := Fin.ext (show (jj : ℕ) = j by omega)
            subst e; exact ⟨g11, g12⟩)
        (by
          intro jj hjj
          have := jj.isLt
          rw [p48, g13 (s.core.ptrs 48 + jj) (by omega) (by omega),
            g13 (s.core.ptrs 48 + jj + m) (by omega) (by omega)]
          exact hge jj (by omega))
    refine ⟨23 + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, by rw [← p48]; exact q3, ?_, fun x x1 x2 => by rw [q5 x x1 x2, g5 x x1 x2],
      fun x x1 x2 x3 x4 => by rw [q6 x x1 x2 x3 x4, g10 x x1 x2 x3 x4], by rw [q7, g14],
      by rw [q8, g15]; ring, ?_⟩
    · intro z hz
      rw [q4 z (by rw [p48]; exact hz), g13 _ (by omega) (by omega)]
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · rcases g16 c hc with rfl | rfl <;> refine ⟨rfl, by omega, by omega⟩
      · obtain ⟨c1, c2, c3⟩ := q9 c hc; rw [p48] at c2 c3; exact ⟨c1, c2, c3⟩

lemma fi_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pt : Fin m → ℝ) :
    ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 116 → s.halted = false →
      s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j →
      s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 47 →
      (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) →
      (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = pt jj ∧
        s.core.mem (s.core.ptrs 48 + jj + m) = pt jj) →
      ∃ t, t ≤ 9 * k + 2 ∧ (run Q s detTape t).core.pc = off + 126 ∧
        (run Q s detTape t).halted = false ∧
        BoxAt (run Q s detTape t) (s.core.ptrs 48) pt pt ∧
        (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) →
          (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (run Q s detTape t).core.ptrs 49 = 1 ∧
        (∀ x, x ≠ 46 → x ≠ 49 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 44 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m := by
  intro k
  induction k with
  | zero =>
    intro j s hjk hpc hh h1 hm h46 _ _ hlt
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
      fi_exit Q off hE s hpc hh (by rw [h1, h46]; omega) (by rw [h1]; exact_mod_cast hm)
    refine ⟨2, by omega, g1, g2, ?_, fun z _ => by rw [g6], g3, fun x _ x2 _ => g4 x x2,
      fun x _ => by rw [g5], g7, g8, by rw [g9]; simp⟩
    intro jj; rw [g6]; exact hlt jj (by omega)
  | succ k ih =>
    intro j s hjk hpc hh h1 hm h46 hq hpt hlt
    have hj : j < m := by omega
    have e0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = pt ⟨j, hj⟩ := by rw [h46]; exact hpt ⟨j, hj⟩
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ :=
      fi_step Q off hE _ s hpc hh e0 (by rw [h1, h46]; exact_mod_cast hj) (by rw [h1]; exact_mod_cast hm)
    set s1 := run Q s detTape 9 with hs1
    have p47 := g5 47 (by decide) (by decide)
    have p48 := g5 48 (by decide) (by decide)
    rw [h46] at g8
    rw [h46, h1] at g9
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
      ih (j + 1) s1 (by omega) g1 g2 (by rw [g5 1 (by decide) (by decide), h1]) hm
        (by rw [g3, h46]; push_cast; ring) (by rw [p47, p48]; exact hq)
        (by intro jj; rw [p47, g10 _ (by have := jj.isLt; omega) (by have := jj.isLt; omega)]; exact hpt jj)
        (by
          intro jj hjj
          have := jj.isLt
          rw [p48]
          rcases Nat.lt_or_ge (jj : ℕ) j with h | h
          · rw [g10 (s.core.ptrs 48 + jj) (by omega) (by omega),
              g10 (s.core.ptrs 48 + jj + m) (by omega) (by omega)]; exact hlt jj h
          · have e : jj = ⟨j, hj⟩ := Fin.ext (show (jj : ℕ) = j by omega)
            subst e; exact ⟨g8, g9⟩)
    refine ⟨9 + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, by rw [← p48]; exact q3, ?_, q5, fun x x1 x2 x3 => by rw [q6 x x1 x2 x3, g5 x x1 x3],
      fun x x1 => by rw [q7 x x1, g7 x x1], by rw [q8, g11], by rw [q9, g12]; ring, ?_⟩
    · intro z hz
      rw [q4 z (by rw [p48]; exact hz), g10 _ (by omega) (by omega)]
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · rcases g13 c hc with rfl | rfl <;> refine ⟨rfl, by omega, by omega⟩
      · obtain ⟨c1, c2, c3⟩ := q10 c hc; rw [p48] at c2 c3; exact ⟨c1, c2, c3⟩

lemma tb_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (mn0 mx0 lo hi : Fin m → ℝ) (r2 : ℝ) :
    ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 134 → s.halted = false →
      s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 → s.core.regs 49 = r2 →
      s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 43 → BoxAt s (s.core.ptrs 43) lo hi →
      (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = max (mn0 jj - r2) (lo jj) ∧
        s.core.mem (s.core.ptrs 48 + jj + m) = min (mx0 jj + r2) (hi jj)) →
      (∀ jj : Fin m, j ≤ (jj : ℕ) → s.core.mem (s.core.ptrs 48 + jj) = mn0 jj ∧
        s.core.mem (s.core.ptrs 48 + jj + m) = mx0 jj) →
      ∃ t, t ≤ 27 * k + 1 ∧ (run Q s detTape t).core.pc = off + 161 ∧
        (run Q s detTape t).halted = false ∧
        BoxAt (run Q s detTape t) (s.core.ptrs 48) (fun jj => max (mn0 jj - r2) (lo jj))
          (fun jj => min (mx0 jj + r2) (hi jj)) ∧
        (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) →
          (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (∀ x, x ≠ 46 → x ≠ 50 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m := by
  intro k
  induction k with
  | zero =>
    intro j s hjk hpc hh h1 hm h46 _ _ _ _ hlt _
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
      tb_exit Q off hE s hpc hh (by rw [h1, h46]; omega) (by rw [h1]; exact_mod_cast hm)
    refine ⟨1, by omega, g1, g2, ?_, fun z _ => by rw [g5], fun x _ _ _ => by rw [g3],
      fun x _ _ _ _ => by rw [g4], g6, g7, by rw [g8]; simp⟩
    intro jj; rw [g5]; exact hlt jj (by omega)
  | succ k ih =>
    intro j s hjk hpc hh h1 hm h46 h53 h49 hq hB hlt hge
    have hj : j < m := by omega
    have e0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = mn0 ⟨j, hj⟩ := by
      rw [h46]; exact (hge ⟨j, hj⟩ le_rfl).1
    have e1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = lo ⟨j, hj⟩ := by rw [h46]; exact (hB ⟨j, hj⟩).1
    have e2 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = mx0 ⟨j, hj⟩ := by
      rw [h46, h1]; exact (hge ⟨j, hj⟩ le_rfl).2
    have e3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = hi ⟨j, hj⟩ := by
      rw [h46, h1]; exact (hB ⟨j, hj⟩).2
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17⟩ :=
      tb_step Q off hE _ _ _ _ s hpc hh e0 e1 e2 e3 (by rw [h1, h46]; exact_mod_cast hj)
        (by rw [h1]; exact_mod_cast hm) (by omega)
    set s1 := run Q s detTape 27 with hs1
    have r53 : s1.core.regs 53 = 2 := by rw [g11 53 (by decide) (by decide) (by decide) (by decide), h53]
    have r49 : s1.core.regs 49 = r2 := by rw [g11 49 (by decide) (by decide) (by decide) (by decide), h49]
    have p43 := g6 43 (by decide) (by decide) (by decide)
    have p48 := g6 48 (by decide) (by decide) (by decide)
    rw [h53, h49, max2, h46] at g12
    rw [h53, h49, min2, h46, h1] at g13
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih (j + 1) s1 (by omega) g1 g2 (by rw [g6 1 (by decide) (by decide) (by decide), h1]) hm
        (by rw [g3, h46]; push_cast; ring) r53 r49 (by rw [p43, p48]; exact hq)
        (by
          rw [p43]; intro jj; have := jj.isLt
          rw [g14 _ (by omega) (by omega), g14 _ (by omega) (by omega)]; exact hB jj)
        (by
          intro jj hjj
          have := jj.isLt
          rw [p48]
          rcases Nat.lt_or_ge (jj : ℕ) j with h | h
          · rw [g14 (s.core.ptrs 48 + jj) (by omega) (by omega),
              g14 (s.core.ptrs 48 + jj + m) (by omega) (by omega)]; exact hlt jj h
          · have e : jj = ⟨j, hj⟩ := Fin.ext (show (jj : ℕ) = j by omega)
            subst e; exact ⟨g12, g13⟩)
        (by
          intro jj hjj
          have := jj.isLt
          rw [p48, g14 (s.core.ptrs 48 + jj) (by omega) (by omega),
            g14 (s.core.ptrs 48 + jj + m) (by omega) (by omega)]
          exact hge jj (by omega))
    refine ⟨27 + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, by rw [← p48]; exact q3, ?_, fun x x1 x2 x3 => by rw [q5 x x1 x2 x3, g6 x x1 x2 x3],
      fun x x1 x2 x3 x4 => by rw [q6 x x1 x2 x3 x4, g11 x x1 x2 x3 x4], by rw [q7, g15],
      by rw [q8, g16]; ring, ?_⟩
    · intro z hz
      rw [q4 z (by rw [p48]; exact hz), g14 _ (by omega) (by omega)]
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · rcases g17 c hc with rfl | rfl <;> refine ⟨rfl, by omega, by omega⟩
      · obtain ⟨c1, c2, c3⟩ := q9 c hc; rw [p48] at c2 c3; exact ⟨c1, c2, c3⟩

lemma sg_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tlo thi lo hi : Fin m → ℝ) :
    ∀ (k j : ℕ) (s : State), j + k = m → 1 ≤ j → s.core.pc = off + 172 → s.halted = false →
      s.core.ptrs 1 = m → s.core.ptrs 46 = j → s.core.regs 53 = 2 →
      BoxAt s (s.core.ptrs 48) tlo thi → BoxAt s (s.core.ptrs 43) lo hi →
      s.core.regs 51 = rmax (side tlo thi) (j - 1) → s.core.regs 52 = rmax (side lo hi) (j - 1) →
      ∃ t, t ≤ 25 * k + 1 ∧ (run Q s detTape t).core.pc = off + 197 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.regs 51 = rmax (side tlo thi) (m - 1) ∧
        (run Q s detTape t).core.regs 52 = rmax (side lo hi) (m - 1) ∧
        (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 51 → x ≠ 52 → x ≠ 54 →
          (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ := by
  intro k
  induction k with
  | zero =>
    intro j s hjk hj1 hpc hh h1 h46 _ _ _ h51 h52
    obtain rfl : j = m := by omega
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
      sg_exit Q off hE s hpc hh (by rw [h1, h46]) (by rw [h1]; exact_mod_cast hj1)
    refine ⟨1, by omega, g1, g2, by rw [g4, h51], by rw [g4, h52],
      fun x _ _ => by rw [g3], fun x _ _ _ _ _ _ => by rw [g4], g5, g6, g7, g8⟩
  | succ k ih =>
    intro j s hjk hj1 hpc hh h1 h46 h53 hB hB' h51 h52
    have hj : j < m := by omega
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩ :=
      sg_step Q off hE (tlo ⟨j, hj⟩) (thi ⟨j, hj⟩) (lo ⟨j, hj⟩) (hi ⟨j, hj⟩) s hpc hh
        (by rw [h46]; exact (hB ⟨j, hj⟩).1) (by rw [h46, h1]; exact (hB ⟨j, hj⟩).2)
        (by rw [h46]; exact (hB' ⟨j, hj⟩).1) (by rw [h46, h1]; exact (hB' ⟨j, hj⟩).2)
        (by rw [h1, h46]; exact_mod_cast hj) (by rw [h1]; exact_mod_cast hj1.trans hj.le)
    set s1 := run Q s detTape 25 with hs1
    have r53 : s1.core.regs 53 = 2 := by
      rw [g12 53 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h53]
    have hrm : ∀ g : ℕ → ℝ, rmax g j = max (rmax g (j - 1)) (g j) := by
      intro g; obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩; rfl
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
      ih (j + 1) s1 (by omega) (by omega) g1 g2 (by rw [g5 1 (by decide) (by decide), h1])
        (by rw [g3, h46]; push_cast; ring) r53
        (by rw [g5 48 (by decide) (by decide)]; unfold BoxAt; rw [g13]; exact hB)
        (by rw [g5 43 (by decide) (by decide)]; unfold BoxAt; rw [g13]; exact hB')
        (by rw [g9, h53, max2, h51, Nat.add_sub_cancel, hrm]; congr 1; unfold side; rw [dif_pos hj])
        (by rw [g10, h53, max2, h52, Nat.add_sub_cancel, hrm]; congr 1; unfold side; rw [dif_pos hj])
    refine ⟨25 + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, q3, q4, fun x x1 x2 => by rw [q5 x x1 x2, g5 x x1 x2],
      fun x x1 x2 x3 x4 x5 x6 => by rw [q6 x x1 x2 x3 x4 x5 x6, g12 x x1 x2 x3 x4 x5 x6],
      by rw [q7, g13], by rw [q8, g14], by rw [q9, g15]; ring, by rw [g16, q10]; simp⟩

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
        (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ := by
  intro d
  induction d with
  | zero =>
    intro k s hkd hpc hh h1 h53 h52 hB
    have hkk : k = ks := by omega
    subst hkk
    have hk : k < m := hks
    have e0 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53) = lo ⟨k, hk⟩ := by rw [h53]; exact (hB ⟨k, hk⟩).1
    have e1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1) = hi ⟨k, hk⟩ := by
      rw [h53, h1]; exact (hB ⟨k, hk⟩).2
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ :=
      la_found Q off hE _ _ s hpc hh e0 e1 (by rw [h52]; linarith)
        (by rw [h1]; exact_mod_cast (Nat.zero_lt_of_lt hk))
    exact ⟨7, k, hk, le_rfl, by omega, by omega, hσ, fun j _ h1 h2 => absurd h2 (by omega),
      g1, g2, by rw [g4 53 (by decide), h53], g5, g6, fun x x1 x2 => g4 x x2, fun x x1 x2 x3 x4 => g9 x x1 x2 x3 x4,
      g10, g11, g12, g13⟩
  | succ d ih =>
    intro k s hkd hpc hh h1 h53 h52 hB
    have hk : k < m := by omega
    have e0 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53) = lo ⟨k, hk⟩ := by rw [h53]; exact (hB ⟨k, hk⟩).1
    have e1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1) = hi ⟨k, hk⟩ := by
      rw [h53, h1]; exact (hB ⟨k, hk⟩).2
    by_cases hc : σ ≤ hi ⟨k, hk⟩ - lo ⟨k, hk⟩
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ :=
        la_found Q off hE _ _ s hpc hh e0 e1 (by rw [h52]; linarith)
          (by rw [h1]; exact_mod_cast (Nat.zero_lt_of_lt hk))
      exact ⟨7, k, hk, le_rfl, by omega, by omega, hc, fun j _ h1 h2 => absurd h2 (by omega),
        g1, g2, by rw [g4 53 (by decide), h53], g5, g6, fun x x1 x2 => g4 x x2,
        fun x x1 x2 x3 x4 => g9 x x1 x2 x3 x4, g10, g11, g12, g13⟩
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ :=
        la_next Q off hE _ _ s hpc hh e0 e1 (by rw [h52]; intro h; exact hc (by linarith))
          (by rw [h1]; exact_mod_cast (Nat.zero_lt_of_lt hk))
      set s1 := run Q s detTape 9 with hs1
      obtain ⟨t2, k0, hk0, q0, q0', q0'', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13⟩ :=
        ih (k + 1) s1 (by omega) g1 g2 (by rw [g5 1 (by decide) (by decide), h1]) (by rw [g3, h53]; push_cast; ring)
          (by rw [g10 52 (by decide) (by decide) (by decide) (by decide), h52])
          (by rw [g5 43 (by decide) (by decide)]; unfold BoxAt; rw [g11]; exact hB)
      refine ⟨9 + t2, k0, hk0, by omega, q0', by omega, q1, ?_, ?_⟩
      · intro j hj j1 j2
        rcases Nat.eq_or_lt_of_le j1 with e | e
        · subst e; exact hc
        · exact q2 j hj (by omega) j2
      rw [run_add, cellsWritten_add, ← hs1]
      exact ⟨q3, q4, q5, q6, q7, fun x x1 x2 => by rw [q8 x x1 x2, g5 x x1 x2],
        fun x x1 x2 x3 x4 => by rw [q9 x x1 x2 x3 x4, g10 x x1 x2 x3 x4], by rw [q10, g11],
        by rw [q11, g12], by rw [q12, g13]; ring, by rw [g14, q13]; simp⟩

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
        ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 56 ≤ c.2 ∧ c.2 < s.core.ptrs 56 + L := by
  intro k
  induction k with
  | zero =>
    intro j s hjk hpc hh hm h60 h46 _ _ hlt
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := cl_exit Q off hE s hpc hh (by rw [h60, h46]; omega) hm
    refine ⟨1, by omega, g1, g2, fun z hz => by rw [g5]; exact hlt z (by omega), fun z _ => by rw [g5],
      fun x _ _ => by rw [g3], fun x _ => by rw [g4], g6, g7, by rw [g8]; simp⟩
  | succ k ih =>
    intro j s hjk hpc hh hm h60 h46 hd hsrc hlt
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ :=
      cl_step Q off hE (src j) s hpc hh (by rw [h46]; exact hsrc j (by omega)) (by rw [h60, h46]; exact_mod_cast (by omega : j < L)) hm
    set s1 := run Q s detTape 7 with hs1
    have p50 := g5 50 (by decide) (by decide)
    have p56 := g5 56 (by decide) (by decide)
    rw [h46] at g8
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih (j + 1) s1 (by omega) g1 g2 (by rw [g5 1 (by decide) (by decide)]; exact hm)
        (by rw [g5 60 (by decide) (by decide), h60]) (by rw [g3, h46]; push_cast; ring) (by rw [p50, p56]; exact hd)
        (by intro z hz; rw [p50, g9 _ (by omega)]; exact hsrc z hz)
        (by
          intro z hz
          rw [p56]
          rcases Nat.lt_or_ge z j with h | h
          · rw [g9 _ (by omega)]; exact hlt z h
          · rw [show z = j by omega]; exact g8)
    refine ⟨7 + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, by rw [← p56]; exact q3, ?_, fun x x1 x2 => by rw [q5 x x1 x2, g5 x x1 x2],
      fun x x1 => by rw [q6 x x1, g7 x x1], by rw [q7, g10], by rw [q8, g11]; ring, ?_⟩
    · intro z hz
      rw [q4 z (by rw [p56]; exact hz), g9 _ (by omega)]
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · rw [g12 c hc]; exact ⟨rfl, by omega, by omega⟩
      · obtain ⟨c1, c2, c3⟩ := q9 c hc; rw [p56] at c2 c3; exact ⟨c1, c2, c3⟩

lemma icp_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (src : ℕ → ℝ) (L : ℕ) :
    ∀ (k j : ℕ) (s : State), j + k = L → s.core.pc = off + 13 → s.halted = false → 1 ≤ s.core.ptrs 1 →
      s.core.ptrs 60 = L → s.core.ptrs 46 = j → s.core.ptrs 43 + L ≤ s.core.ptrs 17 →
      (∀ z, z < L → s.core.mem (s.core.ptrs 17 + z) = src z) →
      (∀ z, z < j → s.core.mem (s.core.ptrs 43 + z) = src z) →
      ∃ t, t ≤ 7 * k + 1 ∧ (run Q s detTape t).core.pc = off + 20 ∧
        (run Q s detTape t).halted = false ∧
        (∀ z, z < L → (run Q s detTape t).core.mem (s.core.ptrs 43 + z) = src z) ∧
        (∀ z, (z < s.core.ptrs 43 ∨ s.core.ptrs 43 + L ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (∀ x, x ≠ 46 → x ≠ 50 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 55 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 43 ≤ c.2 ∧ c.2 < s.core.ptrs 43 + L := by
  intro k
  induction k with
  | zero =>
    intro j s hjk hpc hh hm h60 h46 _ _ hlt
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := icp_exit Q off hE s hpc hh (by rw [h60, h46]; omega) hm
    refine ⟨1, by omega, g1, g2, fun z hz => by rw [g5]; exact hlt z (by omega), fun z _ => by rw [g5],
      fun x _ _ => by rw [g3], fun x _ => by rw [g4], g6, g7, by rw [g8]; simp⟩
  | succ k ih =>
    intro j s hjk hpc hh hm h60 h46 hd hsrc hlt
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ :=
      icp_step Q off hE (src j) s hpc hh (by rw [h46]; exact hsrc j (by omega)) (by rw [h60, h46]; exact_mod_cast (by omega : j < L)) hm
    set s1 := run Q s detTape 7 with hs1
    have p17 := g5 17 (by decide) (by decide)
    have p43 := g5 43 (by decide) (by decide)
    rw [h46] at g8
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih (j + 1) s1 (by omega) g1 g2 (by rw [g5 1 (by decide) (by decide)]; exact hm)
        (by rw [g5 60 (by decide) (by decide), h60]) (by rw [g3, h46]; push_cast; ring) (by rw [p17, p43]; exact hd)
        (by intro z hz; rw [p17, g9 _ (by omega)]; exact hsrc z hz)
        (by
          intro z hz
          rw [p43]
          rcases Nat.lt_or_ge z j with h | h
          · rw [g9 _ (by omega)]; exact hlt z h
          · rw [show z = j by omega]; exact g8)
    refine ⟨7 + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, by rw [← p43]; exact q3, ?_, fun x x1 x2 => by rw [q5 x x1 x2, g5 x x1 x2],
      fun x x1 => by rw [q6 x x1, g7 x x1], by rw [q7, g10], by rw [q8, g11]; ring, ?_⟩
    · intro z hz
      rw [q4 z (by rw [p43]; exact hz), g9 _ (by omega)]
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · rw [g12 c hc]; exact ⟨rfl, by omega, by omega⟩
      · obtain ⟨c1, c2, c3⟩ := q9 c hc; rw [p43] at c2 c3; exact ⟨c1, c2, c3⟩

theorem loop_specs' :
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (lo hi pt : Fin m → ℝ),
      ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 53 → s.halted = false → s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 → (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) → BoxAt s (s.core.ptrs 43) lo hi → s.core.regs 42 = psum (t1 lo hi pt) j → s.core.regs 43 = psum (t2 lo hi pt) j → ∃ t, t ≤ 33 * k + 1 ∧ (run Q s detTape t).core.pc = off + 86 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.regs 42 = boxDist2 lo hi pt ∧ (run Q s detTape t).core.regs 43 = boxMaxDist2 lo hi pt ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 47 → x ≠ 48 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅) ∧
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pt mn0 mx0 : Fin m → ℝ),
      ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 93 → s.halted = false → s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 → s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 47 → (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) → (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = min (mn0 jj) (pt jj) ∧ s.core.mem (s.core.ptrs 48 + jj + m) = max (mx0 jj) (pt jj)) → (∀ jj : Fin m, j ≤ (jj : ℕ) → s.core.mem (s.core.ptrs 48 + jj) = mn0 jj ∧ s.core.mem (s.core.ptrs 48 + jj + m) = mx0 jj) → ∃ t, t ≤ 23 * k + 1 ∧ (run Q s detTape t).core.pc = off + 126 ∧ (run Q s detTape t).halted = false ∧ BoxAt (run Q s detTape t) (s.core.ptrs 48) (fun jj => min (mn0 jj) (pt jj)) (fun jj => max (mx0 jj) (pt jj)) ∧ (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m) ∧
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pt : Fin m → ℝ),
      ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 116 → s.halted = false → s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 47 → (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) → (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = pt jj ∧ s.core.mem (s.core.ptrs 48 + jj + m) = pt jj) → ∃ t, t ≤ 9 * k + 2 ∧ (run Q s detTape t).core.pc = off + 126 ∧ (run Q s detTape t).halted = false ∧ BoxAt (run Q s detTape t) (s.core.ptrs 48) pt pt ∧ (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧ (run Q s detTape t).core.ptrs 49 = 1 ∧ (∀ x, x ≠ 46 → x ≠ 49 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 44 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m) ∧
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (mn0 mx0 lo hi : Fin m → ℝ) (r2 : ℝ),
      ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 134 → s.halted = false → s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 → s.core.regs 49 = r2 → s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 43 → BoxAt s (s.core.ptrs 43) lo hi → (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = max (mn0 jj - r2) (lo jj) ∧ s.core.mem (s.core.ptrs 48 + jj + m) = min (mx0 jj + r2) (hi jj)) → (∀ jj : Fin m, j ≤ (jj : ℕ) → s.core.mem (s.core.ptrs 48 + jj) = mn0 jj ∧ s.core.mem (s.core.ptrs 48 + jj + m) = mx0 jj) → ∃ t, t ≤ 27 * k + 1 ∧ (run Q s detTape t).core.pc = off + 161 ∧ (run Q s detTape t).halted = false ∧ BoxAt (run Q s detTape t) (s.core.ptrs 48) (fun jj => max (mn0 jj - r2) (lo jj)) (fun jj => min (mx0 jj + r2) (hi jj)) ∧ (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧ (∀ x, x ≠ 46 → x ≠ 50 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m) ∧
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tlo thi lo hi : Fin m → ℝ),
      ∀ (k j : ℕ) (s : State), j + k = m → 1 ≤ j → s.core.pc = off + 172 → s.halted = false → s.core.ptrs 1 = m → s.core.ptrs 46 = j → s.core.regs 53 = 2 → BoxAt s (s.core.ptrs 48) tlo thi → BoxAt s (s.core.ptrs 43) lo hi → s.core.regs 51 = rmax (side tlo thi) (j - 1) → s.core.regs 52 = rmax (side lo hi) (j - 1) → ∃ t, t ≤ 25 * k + 1 ∧ (run Q s detTape t).core.pc = off + 197 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.regs 51 = rmax (side tlo thi) (m - 1) ∧ (run Q s detTape t).core.regs 52 = rmax (side lo hi) (m - 1) ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 51 → x ≠ 52 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅) ∧
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (lo hi : Fin m → ℝ) (σ : ℝ) (ks : ℕ) (hks : ks < m) (hσ : σ ≤ hi ⟨ks, hks⟩ - lo ⟨ks, hks⟩),
      ∀ (d k : ℕ) (s : State), k + d = ks → s.core.pc = off + 201 → s.halted = false → s.core.ptrs 1 = m → s.core.ptrs 53 = k → s.core.regs 52 = σ → BoxAt s (s.core.ptrs 43) lo hi → ∃ t k0, ∃ hk0 : k0 < m, k ≤ k0 ∧ k0 ≤ ks ∧ t ≤ 9 * d + 7 ∧ σ ≤ hi ⟨k0, hk0⟩ - lo ⟨k0, hk0⟩ ∧ (∀ j (hj : j < m), k ≤ j → j < k0 → ¬ σ ≤ hi ⟨j, hj⟩ - lo ⟨j, hj⟩) ∧ (run Q s detTape t).core.pc = off + 210 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 53 = k0 ∧ (run Q s detTape t).core.regs 44 = lo ⟨k0, hk0⟩ ∧ (run Q s detTape t).core.regs 45 = hi ⟨k0, hk0⟩ ∧ (∀ x, x ≠ 53 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (src : ℕ → ℝ) (L : ℕ),
      ∀ (k j : ℕ) (s : State), j + k = L → s.core.pc = off + 261 → s.halted = false → 1 ≤ s.core.ptrs 1 → s.core.ptrs 60 = L → s.core.ptrs 46 = j → s.core.ptrs 56 + L ≤ s.core.ptrs 50 → (∀ z, z < L → s.core.mem (s.core.ptrs 50 + z) = src z) → (∀ z, z < j → s.core.mem (s.core.ptrs 56 + z) = src z) → ∃ t, t ≤ 7 * k + 1 ∧ (run Q s detTape t).core.pc = off + 268 ∧ (run Q s detTape t).halted = false ∧ (∀ z, z < L → (run Q s detTape t).core.mem (s.core.ptrs 56 + z) = src z) ∧ (∀ z, (z < s.core.ptrs 56 ∨ s.core.ptrs 56 + L ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 55 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 56 ≤ c.2 ∧ c.2 < s.core.ptrs 56 + L) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (src : ℕ → ℝ) (L : ℕ),
      ∀ (k j : ℕ) (s : State), j + k = L → s.core.pc = off + 13 → s.halted = false → 1 ≤ s.core.ptrs 1 → s.core.ptrs 60 = L → s.core.ptrs 46 = j → s.core.ptrs 43 + L ≤ s.core.ptrs 17 → (∀ z, z < L → s.core.mem (s.core.ptrs 17 + z) = src z) → (∀ z, z < j → s.core.mem (s.core.ptrs 43 + z) = src z) → ∃ t, t ≤ 7 * k + 1 ∧ (run Q s detTape t).core.pc = off + 20 ∧ (run Q s detTape t).halted = false ∧ (∀ z, z < L → (run Q s detTape t).core.mem (s.core.ptrs 43 + z) = src z) ∧ (∀ z, (z < s.core.ptrs 43 ∨ s.core.ptrs 43 + L ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧ (∀ x, x ≠ 46 → x ≠ 50 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 55 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 43 ≤ c.2 ∧ c.2 < s.core.ptrs 43 + L) :=
  ⟨dl_loop, up_loop, fi_loop, tb_loop, sg_loop, la_loop, cl_loop, icp_loop⟩

end DetANN.HPIM.BD.SL

namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM

theorem _root_.solution :
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (lo hi pt : Fin m → ℝ),
      ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 53 → s.halted = false → s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 → (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) → BoxAt s (s.core.ptrs 43) lo hi → s.core.regs 42 = psum (t1 lo hi pt) j → s.core.regs 43 = psum (t2 lo hi pt) j → ∃ t, t ≤ 33 * k + 1 ∧ (run Q s detTape t).core.pc = off + 86 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.regs 42 = boxDist2 lo hi pt ∧ (run Q s detTape t).core.regs 43 = boxMaxDist2 lo hi pt ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 47 → x ≠ 48 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅) ∧
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pt mn0 mx0 : Fin m → ℝ),
      ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 93 → s.halted = false → s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 → s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 47 → (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) → (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = min (mn0 jj) (pt jj) ∧ s.core.mem (s.core.ptrs 48 + jj + m) = max (mx0 jj) (pt jj)) → (∀ jj : Fin m, j ≤ (jj : ℕ) → s.core.mem (s.core.ptrs 48 + jj) = mn0 jj ∧ s.core.mem (s.core.ptrs 48 + jj + m) = mx0 jj) → ∃ t, t ≤ 23 * k + 1 ∧ (run Q s detTape t).core.pc = off + 126 ∧ (run Q s detTape t).halted = false ∧ BoxAt (run Q s detTape t) (s.core.ptrs 48) (fun jj => min (mn0 jj) (pt jj)) (fun jj => max (mx0 jj) (pt jj)) ∧ (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m) ∧
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pt : Fin m → ℝ),
      ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 116 → s.halted = false → s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 47 → (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) → (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = pt jj ∧ s.core.mem (s.core.ptrs 48 + jj + m) = pt jj) → ∃ t, t ≤ 9 * k + 2 ∧ (run Q s detTape t).core.pc = off + 126 ∧ (run Q s detTape t).halted = false ∧ BoxAt (run Q s detTape t) (s.core.ptrs 48) pt pt ∧ (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧ (run Q s detTape t).core.ptrs 49 = 1 ∧ (∀ x, x ≠ 46 → x ≠ 49 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 44 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m) ∧
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (mn0 mx0 lo hi : Fin m → ℝ) (r2 : ℝ),
      ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 134 → s.halted = false → s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 → s.core.regs 49 = r2 → s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 43 → BoxAt s (s.core.ptrs 43) lo hi → (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = max (mn0 jj - r2) (lo jj) ∧ s.core.mem (s.core.ptrs 48 + jj + m) = min (mx0 jj + r2) (hi jj)) → (∀ jj : Fin m, j ≤ (jj : ℕ) → s.core.mem (s.core.ptrs 48 + jj) = mn0 jj ∧ s.core.mem (s.core.ptrs 48 + jj + m) = mx0 jj) → ∃ t, t ≤ 27 * k + 1 ∧ (run Q s detTape t).core.pc = off + 161 ∧ (run Q s detTape t).halted = false ∧ BoxAt (run Q s detTape t) (s.core.ptrs 48) (fun jj => max (mn0 jj - r2) (lo jj)) (fun jj => min (mx0 jj + r2) (hi jj)) ∧ (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧ (∀ x, x ≠ 46 → x ≠ 50 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m) ∧
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tlo thi lo hi : Fin m → ℝ),
      ∀ (k j : ℕ) (s : State), j + k = m → 1 ≤ j → s.core.pc = off + 172 → s.halted = false → s.core.ptrs 1 = m → s.core.ptrs 46 = j → s.core.regs 53 = 2 → BoxAt s (s.core.ptrs 48) tlo thi → BoxAt s (s.core.ptrs 43) lo hi → s.core.regs 51 = rmax (side tlo thi) (j - 1) → s.core.regs 52 = rmax (side lo hi) (j - 1) → ∃ t, t ≤ 25 * k + 1 ∧ (run Q s detTape t).core.pc = off + 197 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.regs 51 = rmax (side tlo thi) (m - 1) ∧ (run Q s detTape t).core.regs 52 = rmax (side lo hi) (m - 1) ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 51 → x ≠ 52 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅) ∧
    (∀ {m : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (lo hi : Fin m → ℝ) (σ : ℝ) (ks : ℕ) (hks : ks < m) (hσ : σ ≤ hi ⟨ks, hks⟩ - lo ⟨ks, hks⟩),
      ∀ (d k : ℕ) (s : State), k + d = ks → s.core.pc = off + 201 → s.halted = false → s.core.ptrs 1 = m → s.core.ptrs 53 = k → s.core.regs 52 = σ → BoxAt s (s.core.ptrs 43) lo hi → ∃ t k0, ∃ hk0 : k0 < m, k ≤ k0 ∧ k0 ≤ ks ∧ t ≤ 9 * d + 7 ∧ σ ≤ hi ⟨k0, hk0⟩ - lo ⟨k0, hk0⟩ ∧ (∀ j (hj : j < m), k ≤ j → j < k0 → ¬ σ ≤ hi ⟨j, hj⟩ - lo ⟨j, hj⟩) ∧ (run Q s detTape t).core.pc = off + 210 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 53 = k0 ∧ (run Q s detTape t).core.regs 44 = lo ⟨k0, hk0⟩ ∧ (run Q s detTape t).core.regs 45 = hi ⟨k0, hk0⟩ ∧ (∀ x, x ≠ 53 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (src : ℕ → ℝ) (L : ℕ),
      ∀ (k j : ℕ) (s : State), j + k = L → s.core.pc = off + 261 → s.halted = false → 1 ≤ s.core.ptrs 1 → s.core.ptrs 60 = L → s.core.ptrs 46 = j → s.core.ptrs 56 + L ≤ s.core.ptrs 50 → (∀ z, z < L → s.core.mem (s.core.ptrs 50 + z) = src z) → (∀ z, z < j → s.core.mem (s.core.ptrs 56 + z) = src z) → ∃ t, t ≤ 7 * k + 1 ∧ (run Q s detTape t).core.pc = off + 268 ∧ (run Q s detTape t).halted = false ∧ (∀ z, z < L → (run Q s detTape t).core.mem (s.core.ptrs 56 + z) = src z) ∧ (∀ z, (z < s.core.ptrs 56 ∨ s.core.ptrs 56 + L ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 55 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 56 ≤ c.2 ∧ c.2 < s.core.ptrs 56 + L) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (src : ℕ → ℝ) (L : ℕ),
      ∀ (k j : ℕ) (s : State), j + k = L → s.core.pc = off + 13 → s.halted = false → 1 ≤ s.core.ptrs 1 → s.core.ptrs 60 = L → s.core.ptrs 46 = j → s.core.ptrs 43 + L ≤ s.core.ptrs 17 → (∀ z, z < L → s.core.mem (s.core.ptrs 17 + z) = src z) → (∀ z, z < j → s.core.mem (s.core.ptrs 43 + z) = src z) → ∃ t, t ≤ 7 * k + 1 ∧ (run Q s detTape t).core.pc = off + 20 ∧ (run Q s detTape t).halted = false ∧ (∀ z, z < L → (run Q s detTape t).core.mem (s.core.ptrs 43 + z) = src z) ∧ (∀ z, (z < s.core.ptrs 43 ∨ s.core.ptrs 43 + L ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧ (∀ x, x ≠ 46 → x ≠ 50 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 55 → (run Q s detTape t).core.regs x = s.core.regs x) ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 43 ≤ c.2 ∧ c.2 < s.core.ptrs 43 + L) :=
  DetANN.HPIM.BD.SL.loop_specs'

end DetANN.HPIM.BD
