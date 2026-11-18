-- Prove2me | solution 1 for DetANN.HPIM.PP.init_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T09:27:31.039336+00:00
-- url     : https://prove2.me/submissions/dae90c3a-af48-46a8-abc2-9699efc2e352

import Mathlib
import Definitions.Def_DetANN_HPIMPreProg
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks

-- ===== QP_Work =====
open PNormReg PNormRegLib SmaleNinth

namespace DetANN.HPIM.QP

lemma RAMStep_eq {R : RAMProgram} {s : RAMConfig} {i : RAMInstr} (h : R[s.pc]? = some i) :
    RAMStep R s = coreExec i s := by
  simp only [RAMStep, h]
  cases i <;> rfl

lemma core_get {P : Program} {pc : ℕ} {i : RAMInstr} (h : P[pc]? = some (.core i)) :
    (coreProgram P)[pc]? = some i := by
  simp [coreProgram, List.getElem?_map, h]

lemma step_eq_exec (P : Program) (ω : ℕ → Bool) (s : State) (ins : Instr)
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) : step P ω s = exec ω ins s := by
  cases ins with
  | core i => simp [step, exec, hh, h, RAMStep_eq (core_get h)]
  | _ => simp [step, exec, hh, h]

lemma run_succ (P : Program) (s : State) (ω : ℕ → Bool) (n : ℕ) :
    run P s ω (n + 1) = run P (step P ω s) ω n := by
  simp [run, Function.iterate_succ_apply]

lemma run_zero (P : Program) (s : State) (ω : ℕ → Bool) : run P s ω 0 = s := rfl

lemma run_add (P : Program) (s : State) (ω : ℕ → Bool) (a b : ℕ) :
    run P s ω (a + b) = run P (run P s ω a) ω b := by
  simp only [run]; rw [add_comm, Function.iterate_add_apply]

lemma run_exec {P : Program} {s : State} {ω : ℕ → Bool} {n : ℕ} {ins : Instr}
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) :
    run P s ω (n + 1) = run P (exec ω ins s) ω n := by
  rw [run_succ, step_eq_exec P ω s ins hh h]

end DetANN.HPIM.QP

-- ===== PP_Ladder =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP

/-- One step of a host `Q` through instruction `i` of an embedded block. -/
lemma run_exec_at {Q B : Program} {off i : ℕ} {ins : Instr} (hE : Embeds Q B off) {s : State}
    {ω : ℕ → Bool} {n : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + i)
    (hB : B[i]? = some ins) : run Q s ω (n + 1) = run Q (exec ω ins s) ω n :=
  run_exec hh (by rw [hpc]; exact hE i ins hB)

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib DetANN.HPIM.QP

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

lemma cellsWritten_zero (P : Program) (s : State) : cellsWritten P s 0 = ∅ := by
  simp [cellsWritten]

lemma embeds_append_right {A B : Program} {off : ℕ} (C : Program) (h : Embeds A B off) :
    Embeds (A ++ C) B off := by
  intro i x hx
  have := h i x hx
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 this).1]
  exact this

lemma embeds_tail (X p : Program) : Embeds (X ++ p) p X.length := by
  intro i x h
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact h

lemma ladder_len (off : ℕ) : (ladder off).length = 14 := rfl

lemma seg0_len (off : ℕ) : (seg0 off).length = 39 := rfl

lemma seg2_len (off RETURN : ℕ) : (seg2 off RETURN).length = 58 := rfl

lemma seg4_len (off : ℕ) : (seg4 off).length = 9 := rfl

lemma seg6_len (off LKE : ℕ) : (seg6 off LKE).length = 82 := rfl

lemma seg8_len (off : ℕ) : (seg8 off).length = 0 := rfl

lemma seg10_len (off LK : ℕ) : (seg10 off LK).length = 26 := rfl

lemma seg12_len (off : ℕ) : (seg12 off).length = 29 := rfl

lemma seg14_len (off NODE : ℕ) : (seg14 off NODE).length = 107 := rfl

variable (B : Blocks)

lemma emb0 (hB : B.WF) : Embeds (Blocks.prog B) (seg0 B.o0) (B.o0) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 14 apply embeds_append_right
  have := embeds_tail ([]) (seg0 B.o0)
  convert this using 1
  all_goals first | rfl | simp [Blocks.o0]

lemma emb1 (hB : B.WF) : Embeds (Blocks.prog B) (ladder B.o1) (B.o1) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 13 apply embeds_append_right
  have := embeds_tail (seg0 B.o0) (ladder B.o1)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb2 (hB : B.WF) : Embeds (Blocks.prog B) (seg2 B.o2 B.lbl_RETURN) (B.o2) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 12 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1) (seg2 B.o2 B.lbl_RETURN)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

end DetANN.HPIM.PP

-- ===== PP_Step =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The cell stored to by instruction `ins` in state `s`. -/
def wcell (ins : Instr) (s : State) : Option (Bool × ℤ) :=
  match ins with
  | .core (.store q _) => some (true, s.core.ptrs q)
  | .integerStore a _ => some (false, s.core.ptrs a)
  | _ => none

lemma cw_exec_at {Q B : Program} {off i : ℕ} {ins : Instr} (hE : Embeds Q B off) {s : State}
    {n : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + i) (hB : B[i]? = some ins) :
    cellsWritten Q s (n + 1) = (wcell ins s).toFinset ∪ cellsWritten Q (exec detTape ins s) n := by
  have hQ : Q[s.core.pc]? = some ins := by rw [hpc]; exact hE i ins hB
  rw [show n + 1 = 1 + n by omega, cellsWritten_add]
  congr 1
  · simp only [cellsWritten, Finset.range_one, Finset.singleton_biUnion, run_zero, writtenCell, hh,
      Bool.false_eq_true, if_false, hQ]
    cases ins with
    | core i => cases i <;> rfl
    | _ => rfl
  · rw [run_succ, run_zero, step_eq_exec Q detTape s ins hh hQ]

lemma cw_zero (Q : Program) (s : State) : cellsWritten Q s 0 = ∅ := cellsWritten_zero Q s

end DetANN.HPIM.PP

-- ===== PP_LadderCW =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The search loop (`pc = off + 1`). -/
lemma ladder_loop_cw (Q : Program) (off : ℕ) (hE : Embeds Q (ladder off) off) (ρ : ℕ → ℝ) (e b : ℝ)
    (hρ : ∀ k, ρ (k + 1) = ρ k * e) (K : ℕ) (hK : b ≤ ρ K) (hmin : ∀ k < K, ¬ b ≤ ρ k) :
    ∀ d j, j + d = K → ∀ s : State, s.core.pc = off + 1 → s.halted = false →
      s.core.regs 40 = b → s.core.regs 41 = ρ j → s.core.regs 42 = e → s.core.ptrs 40 = j →
      ∃ n, n = 5 * d + 2 ∧ (run Q s detTape n).core.pc = off + 6 ∧ (run Q s detTape n).halted = false ∧
        (run Q s detTape n).core.ptrs 40 = K ∧ (run Q s detTape n).core.mem = s.core.mem ∧
        (run Q s detTape n).integerMemory = s.integerMemory ∧
        (∀ x, x ≠ 40 → (run Q s detTape n).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 41 → x ≠ 43 → (run Q s detTape n).core.regs x = s.core.regs x) ∧
        (run Q s detTape n).work = s.work + n ∧ cellsWritten Q s n = ∅ := by
  intro d
  induction d with
  | zero =>
    intro j hj s hpc hh h40 h41 h42 hp40
    simp only [Nat.add_zero] at hj; subst hj
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h40 h41 h42 hp40; subst hpc hh
    refine ⟨2, rfl, ?_⟩
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd])
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Function.update_apply]
    rw [if_pos (by simp [h40, h41]; exact hK), run_zero, cw_zero]
    refine ⟨rfl, rfl, hp40, rfl, rfl, fun x _ => rfl, ?_, by simp⟩
    intro x h1 h3; simp [Function.update_apply, h3]
  | succ d ih =>
    intro j hj s hpc hh h40 h41 h42 hp40
    have hlt : j < K := by omega
    have hno := hmin j hlt
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt', w⟩ := s
    simp only at hpc hh h40 h41 h42 hp40; subst hpc hh
    set S := run Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 5 with hSdef
    have hS : S.core.pc = off + 1 ∧ S.halted = false ∧ S.core.regs 40 = b ∧ S.core.regs 41 = ρ (j + 1) ∧
        S.core.regs 42 = e ∧ S.core.ptrs 40 = ((j + 1 : ℕ) : ℤ) ∧ S.core.mem = mem ∧ S.integerMemory = im ∧
        (∀ x, x ≠ 40 → S.core.ptrs x = ptrs x) ∧ (∀ x, x ≠ 41 → x ≠ 43 → S.core.regs x = regs x) ∧
        S.work = w + 5 ∧ cellsWritten Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ 5 = ∅ := by
      rw [hSdef]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Function.update_apply]
      rw [if_neg (by simp [h40, h41]; exact not_le.mp hno)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union]
      rw [if_pos le_rfl, run_zero, cw_zero]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · simp [Function.update_apply, h40]
      · simp [Function.update_apply, h41, h42, hρ]
      · simp [Function.update_apply, h42]
      · simp [Function.update_apply, hp40]
      · intro x hx; simp [Function.update_apply, hx]
      · intro x h1 h3; simp [Function.update_apply, h1, h3]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, aw, acw⟩ := hS
    obtain ⟨n, hn, b1, b2, b3, b4, b5, b6, b7, bw, bcw⟩ := ih (j + 1) (by omega) S a1 a2 a3 a4 a5 a6
    refine ⟨5 + n, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hSdef]
    refine ⟨b1, b2, b3, by rw [b4, a7], by rw [b5, a8], ?_, ?_, by rw [bw, aw]; ring,
      by rw [acw, bcw]; rfl⟩
    · intro x hx; rw [b6 x hx, a9 x hx]
    · intro x h1 h3; rw [b7 x h1 h3, a10 x h1 h3]

/-- The `clog₂` loop (`pc = off + 10`). -/
lemma ladder_clog_cw (Q : Program) (off : ℕ) (hE : Embeds Q (ladder off) off) (K : ℕ) :
    ∀ d t, t + d = Nat.clog 2 K → ∀ s : State, s.core.pc = off + 10 → s.halted = false →
      s.core.ptrs 40 = K → s.core.ptrs 42 = t → s.core.ptrs 43 = 2 ^ t →
      ∃ n, n = 4 * d + 1 ∧ (run Q s detTape n).core.pc = off + 14 ∧ (run Q s detTape n).halted = false ∧
        (run Q s detTape n).core.ptrs 42 = Nat.clog 2 K ∧ (run Q s detTape n).core.mem = s.core.mem ∧
        (run Q s detTape n).integerMemory = s.integerMemory ∧
        (∀ x, x ≠ 42 → x ≠ 43 → (run Q s detTape n).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape n).core.regs = s.core.regs ∧ (run Q s detTape n).work = s.work + n ∧ cellsWritten Q s n = ∅ := by
  intro d
  induction d with
  | zero =>
    intro t ht s hpc hh h40 h42 h43
    simp only [Nat.add_zero] at ht; subst ht
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h40 h42 h43; subst hpc hh
    refine ⟨1, rfl, ?_⟩
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union]
    rw [if_pos (by rw [h40, h43]; exact_mod_cast Nat.le_pow_clog (by norm_num) K), run_zero, cw_zero]
    exact ⟨rfl, rfl, h42, rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ d ih =>
    intro t ht s hpc hh h40 h42 h43
    have hlt : ¬ (K ≤ 2 ^ t) := by
      intro h; have := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2 h; omega
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt', w⟩ := s
    simp only at hpc hh h40 h42 h43; subst hpc hh
    set S := run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 4 with hSdef
    have hS : S.core.pc = off + 10 ∧ S.halted = false ∧ S.core.ptrs 40 = K ∧
        S.core.ptrs 42 = ((t + 1 : ℕ) : ℤ) ∧ S.core.ptrs 43 = 2 ^ (t + 1) ∧ S.core.mem = mem ∧
        S.integerMemory = im ∧ (∀ x, x ≠ 42 → x ≠ 43 → S.core.ptrs x = ptrs x) ∧
        S.core.regs = regs ∧ S.work = w + 4 ∧
        cellsWritten Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ 4 = ∅ := by
      rw [hSdef]
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union]
      rw [if_neg (by rw [h40, h43]; exact_mod_cast hlt)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union]
      rw [if_pos le_rfl, run_zero, cw_zero]
      refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, ?_, rfl, rfl, rfl⟩
      · simp [Function.update_apply, h40]
      · simp [Function.update_apply, h42]
      · simp [Function.update_apply, h43]; ring
      · intro x h2 h3; simp [Function.update_apply, h2, h3]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, aw, acw⟩ := hS
    obtain ⟨n, hn, b1, b2, b3, b4, b5, b6, b7, bw, bcw⟩ := ih (t + 1) (by omega) S a1 a2 a3 a4 a5
    refine ⟨4 + n, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hSdef]
    refine ⟨b1, b2, b3, by rw [b4, a6], by rw [b5, a7], ?_, by rw [b7, a9], by rw [bw, aw]; ring,
      by rw [acw, bcw]; rfl⟩
    intro x h2 h3; rw [b6 x h2 h3, a8 x h2 h3]

/-- **Ladder block specification**, in any host `Q` embedding the block at `off`. -/
theorem ladder_spec_cw (Q : Program) (off : ℕ) (hE : Embeds Q (ladder off) off) (ρ : ℕ → ℝ) (e b : ℝ)
    (hρ : ∀ k, ρ (k + 1) = ρ k * e) (hex : ∃ k, b ≤ ρ k) (s : State) (hpc : s.core.pc = off)
    (hh : s.halted = false) (h40 : s.core.regs 40 = b) (h41 : s.core.regs 41 = ρ 0)
    (h42 : s.core.regs 42 = e) :
    ∃ n, n = 5 * Nat.find hex + 4 * Nat.clog 2 (Nat.find hex) + 8 ∧
      (run Q s detTape n).core.pc = off + 14 ∧ (run Q s detTape n).halted = false ∧
      (run Q s detTape n).core.ptrs 41 = Nat.find hex + 1 ∧
      (run Q s detTape n).core.ptrs 42 = Nat.clog 2 (Nat.find hex) ∧
      (run Q s detTape n).core.mem = s.core.mem ∧ (run Q s detTape n).integerMemory = s.integerMemory ∧
      (∀ x, x ∉ [40, 41, 42, 43] → (run Q s detTape n).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 41 → x ≠ 43 → (run Q s detTape n).core.regs x = s.core.regs x) ∧
      (run Q s detTape n).work = s.work + n ∧ cellsWritten Q s n = ∅ := by
  set K := Nat.find hex with hKdef
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h40 h41 h42; subst pc hh
  -- step 0: k := 0
  set S0 := run Q ⟨⟨off, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 1 with hS0
  have e0 : S0 = ⟨⟨off + 1, regs, Function.update ptrs 40 0, mem⟩, im, cur, false, w + 1⟩ := by
    rw [hS0, run_exec_at (i := 0) hE rfl (by simp) rfl]; simp only [exec, coreExec]; rw [run_zero]
  have c0 : cellsWritten Q ⟨⟨off, regs, ptrs, mem⟩, im, cur, false, w⟩ 1 = ∅ := by
    rw [cw_exec_at (i := 0) (n := 0) hE rfl (by simp) rfl]; simp [wcell, cw_zero]
  obtain ⟨n1, hn1, a1, a2, a3, a4, a5, a6, a7, aw, acw⟩ :=
    ladder_loop_cw Q off hE ρ e b hρ K (Nat.find_spec hex) (fun k hk => Nat.find_min hex hk) K 0
      (by omega) S0 (by rw [e0]) (by rw [e0]) (by rw [e0]; exact h40) (by rw [e0]; exact h41)
      (by rw [e0]; exact h42) (by rw [e0]; simp)
  generalize hS1 : run Q S0 detTape n1 = S1 at a1 a2 a3 a4 a5 a6 a7 aw
  obtain ⟨⟨pc1, regs1, ptrs1, mem1⟩, im1, cur1, hlt1, w1⟩ := S1
  simp only at a1 a2 a3 a4 a5 a6 a7 aw; subst a1 a2
  -- steps 6–9
  set S2 := run Q ⟨⟨off + 6, regs1, ptrs1, mem1⟩, im1, cur1, false, w1⟩ detTape 4 with hS2
  have e2 : S2.core.pc = off + 10 ∧ S2.halted = false ∧ S2.core.ptrs 40 = K ∧ S2.core.ptrs 41 = K + 1 ∧
      S2.core.ptrs 42 = ((0 : ℕ) : ℤ) ∧ S2.core.ptrs 43 = 2 ^ 0 ∧ S2.core.mem = mem1 ∧
      S2.integerMemory = im1 ∧ (∀ x, x ∉ [41, 42, 43] → S2.core.ptrs x = ptrs1 x) ∧
      S2.core.regs = regs1 ∧ S2.work = w1 + 4 ∧
      cellsWritten Q ⟨⟨off + 6, regs1, ptrs1, mem1⟩, im1, cur1, false, w1⟩ 4 = ∅ := by
    rw [hS2]; (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd]); rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl, rfl, rfl⟩
    · simp [Function.update_apply, a3]
    · simp [Function.update_apply, a3]
    · simp [Function.update_apply]
    · simp [Function.update_apply]
    · intro x hx; simp at hx; simp [Function.update_apply, hx]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, cw, ccw⟩ := e2
  obtain ⟨n3, hn3, d1, d2, d3, d4, d5, d6, d7, dw, dcw⟩ :=
    ladder_clog_cw Q off hE K (Nat.clog 2 K) 0 (by omega) S2 c1 c2 c3 c5 c6
  refine ⟨1 + n1 + 4 + n3, by omega, ?_⟩
  have hcw : cellsWritten Q ⟨⟨off, regs, ptrs, mem⟩, im, cur, false, w⟩ (1 + n1 + 4 + n3) = ∅ := by
    rw [show 1 + n1 + 4 + n3 = 1 + (n1 + (4 + n3)) by ring, cellsWritten_add, c0, ← hS0,
      cellsWritten_add, acw, hS1, cellsWritten_add, ccw, ← hS2, dcw]; simp
  rw [hcw, run_add, run_add, run_add, ← hS0, hS1, ← hS2]
  refine ⟨d1, d2, ?_, d3, by rw [d4, c7, a4, e0], by rw [d5, c8, a5, e0], ?_, ?_, ?_, rfl⟩
  · rw [d6 41 (by norm_num) (by norm_num), c4]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [d6 x hx.2.2.1 hx.2.2.2, c9 x (by simp [hx.2.1, hx.2.2.1, hx.2.2.2]), a6 x hx.1, e0]
    simp [Function.update_apply, hx.1]
  · intro x h1 h3; rw [d7, c10, a7 x h1 h3, e0]
  · rw [dw, cw, aw, e0]; ring

end DetANN.HPIM.PP

-- ===== PP_InitSeg =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

lemma i0_a (Q : Program) (off : ℕ) (hE : Embeds Q (seg0 off) off) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) :
    (run Q s detTape 14).core.pc = off + 14 ∧ (run Q s detTape 14).halted = false ∧
      (run Q s detTape 14).core.ptrs 23 = s.integerMemory 0 ∧
      (run Q s detTape 14).core.ptrs 1 = s.integerMemory 1 ∧
      (run Q s detTape 14).core.ptrs 5 = 0 ∧ (run Q s detTape 14).core.ptrs 6 = 1 ∧
      (run Q s detTape 14).core.regs 0 = s.core.mem 0 ∧ (run Q s detTape 14).core.regs 20 = 0 ∧
      (run Q s detTape 14).core.regs 21 = 2 ∧ (run Q s detTape 14).core.regs 22 = 4 ∧
      (run Q s detTape 14).core.regs 7 = 1 ∧
      (run Q s detTape 14).core.regs 1 = 1 + s.core.mem 0 / 4 ∧
      (run Q s detTape 14).integerMemory = s.integerMemory ∧
      (run Q s detTape 14).core.mem = s.core.mem ∧ (run Q s detTape 14).work = s.work + 14 ∧
      cellsWritten Q s 14 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh; subst hpc hh
  rw [run_exec_at (i := 0) hE rfl (by simp) rfl, cw_exec_at (i := 0) hE rfl (by simp) rfl]
  simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
    if_false]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  (all_goals first
      | rfl | trivial
      | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]; done)
      | (intro x h1 h2; simp (config := {decide := true}) [Function.update_apply, h1, h2]; done)
      | (intro x h1; simp (config := {decide := true}) [Function.update_apply, h1]; done)
      | (intro x hx
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
         simp (config := {decide := true}) [Function.update_apply, hx]; done)
      | (simp (config := {decide := true}) [Function.update_apply]; done))

lemma i0_cl_step (Q : Program) (off : ℕ) (hE : Embeds Q (seg0 off) off) (s : State)
    (hpc : s.core.pc = off + 14) (hh : s.halted = false) (hlt : ¬ s.core.ptrs 23 ≤ s.core.ptrs 6) :
    (run Q s detTape 4).core.pc = off + 14 ∧ (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 5 = s.core.ptrs 5 + 1 ∧
      (run Q s detTape 4).core.ptrs 6 = s.core.ptrs 6 + s.core.ptrs 6 ∧
      (∀ x, x ≠ 5 → x ≠ 6 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧ (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt', w⟩ := s
  simp only at hpc hh hlt; subst hpc hh
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_neg hlt]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_pos le_rfl, run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  (all_goals first
      | rfl | trivial
      | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]; done)
      | (intro x h1 h2; simp (config := {decide := true}) [Function.update_apply, h1, h2]; done)
      | (intro x h1; simp (config := {decide := true}) [Function.update_apply, h1]; done)
      | (intro x hx
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
         simp (config := {decide := true}) [Function.update_apply, hx]; done)
      | (simp (config := {decide := true}) [Function.update_apply]; done))

/-- The `clog₂ N` doubling loop (`CL`). -/
lemma i0_cl (Q : Program) (off : ℕ) (hE : Embeds Q (seg0 off) off) (K : ℕ) :
    ∀ d t, t + d = Nat.clog 2 K → ∀ s : State, s.core.pc = off + 14 → s.halted = false →
      s.core.ptrs 23 = K → s.core.ptrs 5 = t → s.core.ptrs 6 = 2 ^ t →
      ∃ n, n = 4 * d + 1 ∧ (run Q s detTape n).core.pc = off + 18 ∧
        (run Q s detTape n).halted = false ∧ (run Q s detTape n).core.ptrs 5 = Nat.clog 2 K ∧
        (∀ x, x ≠ 5 → x ≠ 6 → (run Q s detTape n).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape n).core.regs = s.core.regs ∧
        (run Q s detTape n).integerMemory = s.integerMemory ∧
        (run Q s detTape n).core.mem = s.core.mem ∧ (run Q s detTape n).work = s.work + n ∧
        cellsWritten Q s n = ∅ := by
  intro d
  induction d with
  | zero =>
    intro t ht s hpc hh h23 h5 h6
    simp only [Nat.add_zero] at ht; subst ht
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h23 h5 h6; subst hpc hh
    refine ⟨1, rfl, ?_⟩
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h23, h6]; exact_mod_cast Nat.le_pow_clog (by norm_num) K), run_zero, cw_zero]
    exact ⟨rfl, rfl, h5, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, by simp⟩
  | succ d ih =>
    intro t ht s hpc hh h23 h5 h6
    have hlt : ¬ s.core.ptrs 23 ≤ s.core.ptrs 6 := by
      rw [h23, h6]; intro h
      have h' : K ≤ 2 ^ t := by exact_mod_cast h
      have := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2 h'; omega
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, aw, acw⟩ := i0_cl_step Q off hE s hpc hh hlt
    obtain ⟨n, hn, b1, b2, b3, b4, b5, b6, b7, bw, bcw⟩ := ih (t + 1) (by omega) _ a1 a2
      (by rw [a5 23 (by norm_num) (by norm_num), h23]) (by rw [a3, h5]; push_cast; ring)
      (by rw [a4, h6]; ring)
    refine ⟨4 + n, by omega, ?_⟩
    rw [run_add, cellsWritten_add, acw, bcw]
    refine ⟨b1, b2, b3, fun x h1 h2 => by rw [b4 x h1 h2, a5 x h1 h2], by rw [b5, a6], by rw [b6, a7],
      by rw [b7, a8], by rw [bw, aw]; ring, by simp⟩

lemma i0_b (Q : Program) (off : ℕ) (hE : Embeds Q (seg0 off) off) (s : State)
    (hpc : s.core.pc = off + 18) (hh : s.halted = false) :
    (run Q s detTape 8).core.pc = off + 26 ∧ (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.regs 2 =
        s.core.regs 22 * ((s.core.ptrs 5 : ℝ) + s.core.regs 7) / s.core.regs 0 ∧
      (∀ x, x ∉ [2, 5] → (run Q s detTape 8).core.regs x = s.core.regs x) ∧
      (run Q s detTape 8).core.ptrs 12 = 4 ∧ (run Q s detTape 8).core.ptrs 6 = 1 ∧
      (run Q s detTape 8).core.ptrs 3 = 0 ∧ (run Q s detTape 8).core.ptrs 7 = 4 ∧
      (∀ x, x ∉ [3, 6, 7, 12] → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).work = s.work + 8 ∧
      cellsWritten Q s 8 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh; subst hpc hh
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  (all_goals first
      | rfl | trivial
      | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]; done)
      | (intro x h1 h2; simp (config := {decide := true}) [Function.update_apply, h1, h2]; done)
      | (intro x h1; simp (config := {decide := true}) [Function.update_apply, h1]; done)
      | (intro x hx
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
         simp (config := {decide := true}) [Function.update_apply, hx]; done)
      | (simp (config := {decide := true}) [Function.update_apply]; done))

lemma i0_pa_step (Q : Program) (off : ℕ) (hE : Embeds Q (seg0 off) off) (s : State)
    (hpc : s.core.pc = off + 26) (hh : s.halted = false) (hlt : ¬ s.core.ptrs 23 ≤ s.core.ptrs 3) :
    (run Q s detTape 6).core.pc = off + 26 ∧ (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 3 = s.core.ptrs 3 + 1 ∧
      (run Q s detTape 6).core.ptrs 6 = s.core.ptrs 6 + s.core.ptrs 1 ∧
      (run Q s detTape 6).core.ptrs 7 = s.core.ptrs 7 + 1 ∧
      (∀ x, x ∉ [3, 6, 7] → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).integerMemory =
        Function.update s.integerMemory (s.core.ptrs 7) (s.core.ptrs 6) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧ (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 ⊆ {(false, s.core.ptrs 7)} := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt', w⟩ := s
  simp only at hpc hh hlt; subst hpc hh
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_neg hlt]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_pos le_rfl, run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro c hc; simp at hc ⊢; exact hc)
    | (all_goals first
          | rfl | trivial
          | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]; done)
          | (intro x h1 h2; simp (config := {decide := true}) [Function.update_apply, h1, h2]; done)
          | (intro x h1; simp (config := {decide := true}) [Function.update_apply, h1]; done)
          | (intro x hx
             simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
             simp (config := {decide := true}) [Function.update_apply, hx]; done)
          | (simp (config := {decide := true}) [Function.update_apply]; done))

/-- The point-address loop (`PAL`): `I[4 + g] = 1 + g m`. -/
lemma i0_pa (Q : Program) (off : ℕ) (hE : Embeds Q (seg0 off) off) (N m : ℕ) :
    ∀ d i, i + d = N → ∀ s : State, s.core.pc = off + 26 → s.halted = false →
      s.core.ptrs 23 = N → s.core.ptrs 1 = m → s.core.ptrs 3 = i →
      s.core.ptrs 6 = 1 + (i : ℤ) * m → s.core.ptrs 7 = 4 + i →
      ∃ n, n = 6 * d + 1 ∧ (run Q s detTape n).core.pc = off + 32 ∧
        (run Q s detTape n).halted = false ∧ (run Q s detTape n).core.ptrs 6 = 1 + (N : ℤ) * m ∧
        (∀ x, x ∉ [3, 6, 7] → (run Q s detTape n).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape n).core.regs = s.core.regs ∧
        (∀ g : ℕ, i ≤ g → g < N → (run Q s detTape n).integerMemory (4 + g) = 1 + (g : ℤ) * m) ∧
        (∀ z : ℤ, (z < 4 + i ∨ 4 + N ≤ z) → (run Q s detTape n).integerMemory z = s.integerMemory z) ∧
        (run Q s detTape n).core.mem = s.core.mem ∧ (run Q s detTape n).work = s.work + n ∧
        (∀ c ∈ cellsWritten Q s n, c.1 = false ∧ 4 + (i : ℤ) ≤ c.2 ∧ c.2 < 4 + N) := by
  intro d
  induction d with
  | zero =>
    intro i hi s hpc hh h23 h1 h3 h6 h7
    simp only [Nat.add_zero] at hi; subst hi
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h23 h1 h3 h6 h7; subst hpc hh
    refine ⟨1, rfl, ?_⟩
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h23, h3]), run_zero, cw_zero]
    exact ⟨rfl, rfl, h6, fun _ _ => rfl, rfl, fun g h1 h2 => by omega, fun _ _ => rfl, rfl, rfl,
      by simp⟩
  | succ d ih =>
    intro i hi s hpc hh h23 h1 h3 h6 h7
    have hlt : ¬ s.core.ptrs 23 ≤ s.core.ptrs 3 := by rw [h23, h3]; push_cast; omega
    obtain ⟨a1, a2, a3, a6, a7, aP, aR, aI, aM, aw, acw⟩ := i0_pa_step Q off hE s hpc hh hlt
    obtain ⟨n, hn, b1, b2, b6, bP, bR, bI, bI', bM, bw, bcw⟩ := ih (i + 1) (by omega) _ a1 a2
      (by rw [aP 23 (by simp), h23]) (by rw [aP 1 (by simp), h1]) (by rw [a3, h3]; push_cast; ring)
      (by rw [a6, h6, h1]; push_cast; ring) (by rw [a7, h7]; push_cast; ring)
    refine ⟨6 + n, by omega, ?_⟩
    rw [run_add, cellsWritten_add]
    refine ⟨b1, b2, b6, fun x hx => by rw [bP x hx, aP x hx], by rw [bR, aR], fun g hg1 hg2 => ?_,
      fun z hz => ?_, by rw [bM, aM], by rw [bw, aw]; ring, fun c hc => ?_⟩
    · rcases Nat.eq_or_lt_of_le hg1 with rfl | hg
      · rw [bI' (4 + (i : ℤ)) (Or.inl (by push_cast; omega)), aI, h7, Function.update_self, h6]
      · exact bI g (by omega) hg2
    · rw [bI' z (by push_cast at hz ⊢; omega), aI, Function.update_of_ne (by rw [h7]; omega)]
    · simp only [Finset.mem_union] at hc
      rcases hc with hc | hc
      · have := acw hc; simp only [Finset.mem_singleton] at this; subst this
        rw [h7]; exact ⟨rfl, le_rfl, by push_cast; omega⟩
      · obtain ⟨e1, e2, e3⟩ := bcw c hc; exact ⟨e1, by push_cast at e2; omega, e3⟩

lemma i0_c (Q : Program) (off : ℕ) (hE : Embeds Q (seg0 off) off) (s : State)
    (hpc : s.core.pc = off + 32) (hh : s.halted = false) :
    (run Q s detTape 7).core.pc = off + 39 ∧ (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 16 = s.core.ptrs 6 ∧
      (∀ x, x ≠ 16 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 40 = 8 * (s.core.ptrs 23 : ℝ) * s.core.regs 2 ∧
      (run Q s detTape 7).core.regs 41 = s.core.regs 7 / s.core.regs 1 ∧
      (run Q s detTape 7).core.regs 42 = s.core.regs 1 + s.core.regs 20 ∧
      (∀ x, x ∉ [5, 6, 40, 41, 42] → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧ (run Q s detTape 7).work = s.work + 7 ∧
      cellsWritten Q s 7 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh; subst hpc hh
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  (all_goals first
      | rfl | trivial
      | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]; done)
      | (intro x h1 h2; simp (config := {decide := true}) [Function.update_apply, h1, h2]; done)
      | (intro x h1; simp (config := {decide := true}) [Function.update_apply, h1]; done)
      | (intro x hx
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
         simp (config := {decide := true}) [Function.update_apply, hx]; done)
      | (simp (config := {decide := true}) [Function.update_apply]; done))

lemma i2_a (Q : Program) (off RET : ℕ) (hE : Embeds Q (seg2 off RET) off) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) :
    (run Q s detTape 6).core.pc = off + 6 ∧ (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 3 = 0 ∧ (run Q s detTape 6).core.ptrs 6 = 1 ∧
      (run Q s detTape 6).core.ptrs 7 = s.core.ptrs 12 + s.core.ptrs 23 ∧
      (∀ x, x ∉ [3, 6, 7, 9] → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).integerMemory =
        Function.update s.integerMemory 3 (s.core.ptrs 12 + s.core.ptrs 23) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧ (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 ⊆ {(false, 3)} := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh; subst hpc hh
  rw [run_exec_at (i := 0) hE rfl (by simp) rfl, cw_exec_at (i := 0) hE rfl (by simp) rfl]
  simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
    if_false]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro c hc; simp at hc ⊢; exact hc)
    | (all_goals first
          | rfl | trivial
          | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]; done)
          | (intro x h1 h2; simp (config := {decide := true}) [Function.update_apply, h1, h2]; done)
          | (intro x h1; simp (config := {decide := true}) [Function.update_apply, h1]; done)
          | (intro x hx
             simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
             simp (config := {decide := true}) [Function.update_apply, hx]; done)
          | (simp (config := {decide := true}) [Function.update_apply]; done))

lemma i2_pw_step (Q : Program) (off RET : ℕ) (hE : Embeds Q (seg2 off RET) off) (s : State)
    (hpc : s.core.pc = off + 6) (hh : s.halted = false) (hle : s.core.ptrs 3 ≤ s.core.ptrs 42) :
    (run Q s detTape 6).core.pc = off + 6 ∧ (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 3 = s.core.ptrs 3 + 1 ∧
      (run Q s detTape 6).core.ptrs 6 = s.core.ptrs 6 + s.core.ptrs 6 ∧
      (run Q s detTape 6).core.ptrs 7 = s.core.ptrs 7 + 1 ∧
      (∀ x, x ∉ [3, 6, 7] → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).integerMemory =
        Function.update s.integerMemory (s.core.ptrs 7) (s.core.ptrs 6) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧ (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 ⊆ {(false, s.core.ptrs 7)} := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt', w⟩ := s
  simp only at hpc hh hle; subst hpc hh
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_pos hle]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_pos le_rfl, run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro c hc; simp at hc ⊢; exact hc)
    | (all_goals first
          | rfl | trivial
          | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]; done)
          | (intro x h1 h2; simp (config := {decide := true}) [Function.update_apply, h1, h2]; done)
          | (intro x h1; simp (config := {decide := true}) [Function.update_apply, h1]; done)
          | (intro x hx
             simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
             simp (config := {decide := true}) [Function.update_apply, hx]; done)
          | (simp (config := {decide := true}) [Function.update_apply]; done))

/-- The power-table loop (`PWL`): `I[A + t] = 2^t` for `t ≤ T`. -/
lemma i2_pw (Q : Program) (off RET : ℕ) (hE : Embeds Q (seg2 off RET) off) (A : ℤ) (T : ℕ) :
    ∀ d t, t + d = T + 1 → ∀ s : State, s.core.pc = off + 6 → s.halted = false →
      s.core.ptrs 42 = T → s.core.ptrs 3 = t → s.core.ptrs 6 = 2 ^ t → s.core.ptrs 7 = A + t →
      ∃ n, n = 6 * d + 2 ∧ (run Q s detTape n).core.pc = off + 13 ∧
        (run Q s detTape n).halted = false ∧ (run Q s detTape n).core.ptrs 7 = A + T + 1 ∧
        (∀ x, x ∉ [3, 6, 7] → (run Q s detTape n).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape n).core.regs = s.core.regs ∧
        (∀ u : ℕ, t ≤ u → u ≤ T → (run Q s detTape n).integerMemory (A + u) = 2 ^ u) ∧
        (∀ z, (z < A + t ∨ A + T < z) → (run Q s detTape n).integerMemory z = s.integerMemory z) ∧
        (run Q s detTape n).core.mem = s.core.mem ∧ (run Q s detTape n).work = s.work + n ∧
        (∀ c ∈ cellsWritten Q s n, c.1 = false ∧ A + t ≤ c.2 ∧ c.2 ≤ A + T) := by
  intro d
  induction d with
  | zero =>
    intro t ht s hpc hh h42 h3 h6 h7
    simp only [Nat.add_zero] at ht; subst ht
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h42 h3 h6 h7; subst hpc hh
    refine ⟨2, rfl, ?_⟩
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_neg (by rw [h3, h42]; push_cast; omega)]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos le_rfl, run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp only [h7]; push_cast; ring, fun _ _ => rfl, rfl, fun u h1 h2 => by omega,
      fun _ _ => rfl, rfl, rfl, by simp⟩
  | succ d ih =>
    intro t ht s hpc hh h42 h3 h6 h7
    have hle : s.core.ptrs 3 ≤ s.core.ptrs 42 := by rw [h3, h42]; push_cast; omega
    obtain ⟨a1, a2, a3, a6, a7, aP, aR, aI, aM, aw, acw⟩ := i2_pw_step Q off RET hE s hpc hh hle
    obtain ⟨n, hn, b1, b2, b7, bP, bR, bI, bI', bM, bw, bcw⟩ := ih (t + 1) (by omega) _ a1 a2
      (by rw [aP 42 (by simp), h42]) (by rw [a3, h3]; push_cast; ring)
      (by rw [a6, h6]; ring) (by rw [a7, h7]; push_cast; ring)
    refine ⟨6 + n, by omega, ?_⟩
    rw [run_add, cellsWritten_add]
    refine ⟨b1, b2, b7, fun x hx => by rw [bP x hx, aP x hx], by rw [bR, aR], fun u hu1 hu2 => ?_,
      fun z hz => ?_, by rw [bM, aM], by rw [bw, aw]; ring, fun c hc => ?_⟩
    · rcases Nat.eq_or_lt_of_le hu1 with rfl | hu
      · rw [bI' (A + (t : ℤ)) (Or.inl (by push_cast; omega)), aI, h7, Function.update_self, h6]
      · exact bI u (by omega) hu2
    · rw [bI' z (by push_cast at hz ⊢; omega), aI, Function.update_of_ne (by rw [h7]; omega)]
    · simp only [Finset.mem_union] at hc
      rcases hc with hc | hc
      · have := acw hc; simp only [Finset.mem_singleton] at this; subst this
        rw [h7]; exact ⟨rfl, le_rfl, by push_cast; omega⟩
      · obtain ⟨e1, e2, e3⟩ := bcw c hc; exact ⟨e1, by push_cast at e2; omega, e3⟩

lemma i2_b (Q : Program) (off RET : ℕ) (hE : Embeds Q (seg2 off RET) off) (s : State)
    (hpc : s.core.pc = off + 13) (hh : s.halted = false) :
    (run Q s detTape 4).core.pc = off + 17 ∧ (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 15 = s.core.ptrs 7 ∧
      (run Q s detTape 4).core.ptrs 10 = s.core.ptrs 7 ∧
      (run Q s detTape 4).core.ptrs 3 = 0 ∧ (run Q s detTape 4).core.ptrs 7 = s.core.ptrs 7 ∧
      (∀ x, x ∉ [3, 7, 10, 15] → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧ (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh; subst hpc hh
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  (all_goals first
      | rfl | trivial
      | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]; done)
      | (intro x h1 h2; simp (config := {decide := true}) [Function.update_apply, h1, h2]; done)
      | (intro x h1; simp (config := {decide := true}) [Function.update_apply, h1]; done)
      | (intro x hx
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
         simp (config := {decide := true}) [Function.update_apply, hx]; done)
      | (simp (config := {decide := true}) [Function.update_apply]; done))

lemma i2_rs_step (Q : Program) (off RET : ℕ) (hE : Embeds Q (seg2 off RET) off) (s : State)
    (hpc : s.core.pc = off + 17) (hh : s.halted = false) (hlt : ¬ s.core.ptrs 23 ≤ s.core.ptrs 3) :
    (run Q s detTape 5).core.pc = off + 17 ∧ (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 3 = s.core.ptrs 3 + 1 ∧
      (run Q s detTape 5).core.ptrs 7 = s.core.ptrs 7 + 1 ∧
      (∀ x, x ∉ [3, 7] → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).integerMemory =
        Function.update s.integerMemory (s.core.ptrs 7) (s.core.ptrs 3) ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧ (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 ⊆ {(false, s.core.ptrs 7)} := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt', w⟩ := s
  simp only at hpc hh hlt; subst hpc hh
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_neg hlt]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_pos le_rfl, run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro c hc; simp at hc ⊢; exact hc)
    | (all_goals first
          | rfl | trivial
          | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]; done)
          | (intro x h1 h2; simp (config := {decide := true}) [Function.update_apply, h1, h2]; done)
          | (intro x h1; simp (config := {decide := true}) [Function.update_apply, h1]; done)
          | (intro x hx
             simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
             simp (config := {decide := true}) [Function.update_apply, hx]; done)
          | (simp (config := {decide := true}) [Function.update_apply]; done))

/-- The root-list loop (`RSL`): `I[A + g] = g`. -/
lemma i2_rs (Q : Program) (off RET : ℕ) (hE : Embeds Q (seg2 off RET) off) (A : ℤ) (N : ℕ) :
    ∀ d i, i + d = N → ∀ s : State, s.core.pc = off + 17 → s.halted = false →
      s.core.ptrs 23 = N → s.core.ptrs 3 = i → s.core.ptrs 7 = A + i →
      ∃ n, n = 5 * d + 1 ∧ (run Q s detTape n).core.pc = off + 22 ∧
        (run Q s detTape n).halted = false ∧ (run Q s detTape n).core.ptrs 7 = A + N ∧
        (∀ x, x ∉ [3, 7] → (run Q s detTape n).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape n).core.regs = s.core.regs ∧
        (∀ g : ℕ, i ≤ g → g < N → (run Q s detTape n).integerMemory (A + g) = g) ∧
        (∀ z, (z < A + i ∨ A + N ≤ z) → (run Q s detTape n).integerMemory z = s.integerMemory z) ∧
        (run Q s detTape n).core.mem = s.core.mem ∧ (run Q s detTape n).work = s.work + n ∧
        (∀ c ∈ cellsWritten Q s n, c.1 = false ∧ A + i ≤ c.2 ∧ c.2 < A + N) := by
  intro d
  induction d with
  | zero =>
    intro i hi s hpc hh h23 h3 h7
    simp only [Nat.add_zero] at hi; subst hi
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h23 h3 h7; subst hpc hh
    refine ⟨1, rfl, ?_⟩
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h23, h3]), run_zero, cw_zero]
    exact ⟨rfl, rfl, h7, fun _ _ => rfl, rfl, fun g h1 h2 => by omega, fun _ _ => rfl, rfl, rfl,
      by simp⟩
  | succ d ih =>
    intro i hi s hpc hh h23 h3 h7
    have hlt : ¬ s.core.ptrs 23 ≤ s.core.ptrs 3 := by rw [h23, h3]; push_cast; omega
    obtain ⟨a1, a2, a3, a7, aP, aR, aI, aM, aw, acw⟩ := i2_rs_step Q off RET hE s hpc hh hlt
    obtain ⟨n, hn, b1, b2, b7, bP, bR, bI, bI', bM, bw, bcw⟩ := ih (i + 1) (by omega) _ a1 a2
      (by rw [aP 23 (by simp), h23]) (by rw [a3, h3]; push_cast; ring) (by rw [a7, h7]; push_cast; ring)
    refine ⟨5 + n, by omega, ?_⟩
    rw [run_add, cellsWritten_add]
    refine ⟨b1, b2, b7, fun x hx => by rw [bP x hx, aP x hx], by rw [bR, aR], fun g hg1 hg2 => ?_,
      fun z hz => ?_, by rw [bM, aM], by rw [bw, aw]; ring, fun c hc => ?_⟩
    · rcases Nat.eq_or_lt_of_le hg1 with rfl | hg
      · rw [bI' (A + (i : ℤ)) (Or.inl (by push_cast; omega)), aI, h7, Function.update_self, h3]
      · exact bI g (by omega) hg2
    · rw [bI' z (by push_cast at hz ⊢; omega), aI, Function.update_of_ne (by rw [h7]; omega)]
    · simp only [Finset.mem_union] at hc
      rcases hc with hc | hc
      · have := acw hc; simp only [Finset.mem_singleton] at this; subst this
        rw [h7]; exact ⟨rfl, le_rfl, by push_cast; omega⟩
      · obtain ⟨e1, e2, e3⟩ := bcw c hc; exact ⟨e1, by push_cast at e2; omega, e3⟩

lemma i2_c (Q : Program) (off RET : ℕ) (hE : Embeds Q (seg2 off RET) off) (s : State)
    (hpc : s.core.pc = off + 22) (hh : s.halted = false) :
    (run Q s detTape 17).core.pc = off + 39 ∧ (run Q s detTape 17).halted = false ∧
      (run Q s detTape 17).core.ptrs 2 = s.core.ptrs 7 ∧
      (run Q s detTape 17).core.ptrs 15 = s.core.ptrs 7 + 8 ∧
      (run Q s detTape 17).core.ptrs 8 = -10 ∧ (run Q s detTape 17).core.ptrs 13 = -10 ∧
      (run Q s detTape 17).core.ptrs 14 = 0 ∧
      (∀ x, x ∉ [2, 6, 8, 13, 14, 15, 27] → (run Q s detTape 17).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 17).core.regs = s.core.regs ∧
      (run Q s detTape 17).integerMemory =
        Function.update (Function.update (Function.update (Function.update s.integerMemory
          (s.core.ptrs 7 + 3) (s.core.ptrs 10)) (s.core.ptrs 7 + 7) (s.core.ptrs 23)) 2
          (s.core.ptrs 7)) (-10) 0 ∧
      (run Q s detTape 17).core.mem = s.core.mem ∧ (run Q s detTape 17).work = s.work + 17 ∧
      cellsWritten Q s 17 ⊆
        {(false, s.core.ptrs 7 + 3), (false, s.core.ptrs 7 + 7), (false, 2), (false, -10)} := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh; subst hpc hh
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_pos le_rfl, run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro c hc
       simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union,
         Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc
       simp only [Finset.mem_insert, Finset.mem_singleton]
       rcases hc with h | h | h | h <;> subst h <;> simp (config := {decide := true}) [Function.update_apply])
    | (all_goals first
          | rfl | trivial
          | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]; done)
          | (intro x h1 h2; simp (config := {decide := true}) [Function.update_apply, h1, h2]; done)
          | (intro x h1; simp (config := {decide := true}) [Function.update_apply, h1]; done)
          | (intro x hx
             simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
             simp (config := {decide := true}) [Function.update_apply, hx]; done)
          | (simp (config := {decide := true}) [Function.update_apply]; done))

end DetANN.HPIM.PP

-- ===== PP_Init =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM Classical

lemma flat_getD (m : ℕ) : ∀ (N : ℕ) (Y : Fin N → Fin m → ℝ) (g : ℕ) (hg : g < N) (j : ℕ) (hj : j < m),
    (List.ofFn fun i => List.ofFn (Y i)).flatten.getD (g * m + j) 0 = Y ⟨g, hg⟩ ⟨j, hj⟩ := by
  intro N
  induction N with
  | zero => intro Y g hg; omega
  | succ N ih =>
    intro Y g hg j hj
    rw [List.ofFn_succ, List.flatten_cons]
    rcases g with _ | g
    · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_ofFn]
      simp
    · rw [List.getD_append_right _ _ _ _ (by simp; nlinarith)]
      simp only [List.length_ofFn]
      have := ih (fun i => Y i.succ) g (by first | (clear * - hN; omega) | omega) j hj
      rw [show (g + 1) * m + j - m = g * m + j by rw [Nat.add_mul]; omega, this]
      rfl

lemma univ_emb (N : ℕ) (i : Fin (Finset.univ : Finset (Fin N)).card) :
    (((Finset.univ : Finset (Fin N)).orderEmbOfFin rfl i : Fin N) : ℕ) = i := by
  have hc : (Finset.univ : Finset (Fin N)).card = N := by simp
  have := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin N))) rfl
    (f := fun k => ⟨k, by have := k.isLt; omega⟩) (fun _ => Finset.mem_univ _)
    (fun a b h => by simpa [Fin.lt_def] using h)
  rw [← this]

section Input

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

lemma input_im0 : (inputState Y δ).integerMemory 0 = N := by
  simp [inputState, PNormReg.initState]

lemma input_im1 : (inputState Y δ).integerMemory 1 = m := by
  simp [inputState, PNormReg.initState]

lemma input_mem0 : (inputState Y δ).core.mem 0 = δ := by
  simp [inputState, PNormReg.initState]

lemma input_pts (g : Fin N) (j : Fin m) :
    (inputState Y δ).core.mem (1 + (g : ℤ) * m + j) = Y g j := by
  have hz : (1 + (g : ℤ) * m + j) = ((g * m + j + 1 : ℕ) : ℤ) := by push_cast; ring
  simp only [inputState, PNormReg.initState]
  rw [if_pos (by positivity), hz, Int.toNat_natCast, List.getD_cons_succ]
  exact flat_getD m N (fun i j => Y i j) g g.isLt j j.isLt

end Input

lemma gCond_ex (δ : ℝ) (N : ℕ) (hδ : 0 < δ) : ∃ k, gCond N δ k := by
  have he : 1 < 1 + δ / 4 := by linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (8 * (N : ℝ) * lamOf N δ * (1 + δ / 4)) he
  refine ⟨k, ?_⟩
  unfold gCond
  rw [one_div_mul_eq_div, le_div_iff₀ (by linarith)]
  linarith

/-- The cells written by the initialization (as a pure set computation). -/
lemma init_cw (N T0 : ℕ) (p : ℤ) (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 : Finset (Bool × ℤ))
    (h1 : C1 = ∅) (h2 : C2 = ∅) (h3 : C3 = ∅)
    (h4 : ∀ c ∈ C4, c.1 = false ∧ (4 : ℤ) + ((0 : ℕ) : ℤ) ≤ c.2 ∧ c.2 < 4 + (N : ℤ))
    (h5 : C5 = ∅) (h6 : C6 = ∅) (h7 : C7 ⊆ {(false, 3)})
    (h8 : ∀ c ∈ C8, c.1 = false ∧ (4 + (N : ℤ)) + ((0 : ℕ) : ℤ) ≤ c.2 ∧ c.2 ≤ (4 + (N : ℤ)) + (T0 : ℤ))
    (h9 : C9 = ∅)
    (h10 : ∀ c ∈ C10, c.1 = false ∧ Hbase N T0 + ((0 : ℕ) : ℤ) ≤ c.2 ∧ c.2 < Hbase N T0 + N)
    (h11 : C11 ⊆ {(false, p + 3), (false, p + 7), (false, 2), (false, -10)})
    (hp : p = Hbase N T0 + N) :
    ∀ c ∈ C1 ∪ C2 ∪ C3 ∪ C4 ∪ C5 ∪ C6 ∪ C7 ∪ C8 ∪ C9 ∪ C10 ∪ C11,
      c.1 = false ∧ -10 ≤ c.2 ∧ c.2 < Hbase N T0 + N + 8 := by
  have hHb : Hbase N T0 = 4 + N + T0 + 1 := rfl
  intro c hc
  simp only [Finset.mem_union] at hc
  rcases hc with (((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h
  · rw [h1] at h; simp at h
  · rw [h2] at h; simp at h
  · rw [h3] at h; simp at h
  · obtain ⟨u1, u2, u3⟩ := h4 c h
    exact ⟨u1, by push_cast at u2; omega, by omega⟩
  · rw [h5] at h; simp at h
  · rw [h6] at h; simp at h
  · have := h7 h; simp only [Finset.mem_singleton] at this; subst this
    exact ⟨rfl, by norm_num, by omega⟩
  · obtain ⟨u1, u2, u3⟩ := h8 c h
    exact ⟨u1, by push_cast at u2; omega, by omega⟩
  · rw [h9] at h; simp at h
  · obtain ⟨u1, u2, u3⟩ := h10 c h
    exact ⟨u1, by push_cast at u2; omega, by omega⟩
  · have := h11 h
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e | e | e | e <;> subst e <;> exact ⟨rfl, by omega, by omega⟩

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

set_option maxHeartbeats 2000000 in
/-- **Initialization**: from the input layout to `NODE` on the root. -/
theorem init_spec (B : Blocks) (hB : B.WF) (hN : 1 ≤ N) (hδ : 0 < δ) :
    ∃ t, (run (Blocks.prog B) (inputState Y δ) detTape t).core.pc = B.lbl_NODE ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).halted = false ∧
      GInv Y δ (T0G N δ) (v0G N δ) (run (Blocks.prog B) (inputState Y δ) detTape t) ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 2 = v0G N δ ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 13 = -10 ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 14 = 0 ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 8 = -10 ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 15 = v0G N δ + 8 ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 16 = 1 + (N : ℤ) * m ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).integerMemory (v0G N δ + 3) =
        Hbase N (T0G N δ) ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).integerMemory (v0G N δ + 7) = N ∧
      SList (run (Blocks.prog B) (inputState Y δ) detTape t) (Hbase N (T0G N δ))
        (Finset.univ : Finset (Fin N)) ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).integerMemory (-10) = 0 ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).work ≤
        75 + 4 * Nat.clog 2 N + 11 * N + 5 * KG N δ + 10 * T0G N δ ∧
      (∀ c ∈ cellsWritten (Blocks.prog B) (inputState Y δ) t,
        c.1 = false ∧ -10 ≤ c.2 ∧ c.2 < v0G N δ + 8) := by
  have hE0 := emb0 B hB
  have hE1 := emb1 B hB
  have hE2 := emb2 B hB
  set s0 := inputState Y δ with hs0
  have p0 : s0.core.pc = B.o0 := rfl
  have h0 : s0.halted = false := rfl
  have w0 : s0.work = 0 := rfl
  -- seg0, part A
  obtain ⟨a1, a2, a23, a1', a5, a6, ar0, ar20, ar21, ar22, ar7, ar1, aI, aM, aw, acw⟩ :=
    i0_a (Blocks.prog B) B.o0 hE0 s0 p0 h0
  set s1 := run (Blocks.prog B) s0 detTape 14 with hs1
  -- the clog loop
  obtain ⟨n2, hn2, b1, b2, b5, bP, bR, bI, bM, bw, bcw⟩ :=
    i0_cl (Blocks.prog B) B.o0 hE0 N (Nat.clog 2 N) 0 (by first | (clear * - hN; omega) | omega) s1 a1 a2
      (by rw [a23, input_im0]) (by rw [a5]; simp) (by rw [a6]; simp)
  set s2 := run (Blocks.prog B) s1 detTape n2 with hs2
  -- part B
  obtain ⟨c1, c2, cr2, cR, c12, c6, c3, c7, cP, cI, cM, cw, ccw⟩ :=
    i0_b (Blocks.prog B) B.o0 hE0 s2 b1 b2
  set s3 := run (Blocks.prog B) s2 detTape 8 with hs3
  have q23_3 : s3.core.ptrs 23 = N := by
    rw [cP 23 (by simp), bP 23 (by norm_num) (by norm_num), a23, input_im0]
  have q1_3 : s3.core.ptrs 1 = m := by
    rw [cP 1 (by simp), bP 1 (by norm_num) (by norm_num), a1', input_im1]
  -- the point-address loop
  obtain ⟨n4, hn4, d1, d2, d6, dP, dR, dI, dI', dM, dw, dcw⟩ :=
    i0_pa (Blocks.prog B) B.o0 hE0 N m N 0 (by first | (clear * - hN; omega) | omega) s3 c1 c2 q23_3 q1_3 (by rw [c3]; simp)
      (by rw [c6]; simp) (by rw [c7]; simp)
  set s4 := run (Blocks.prog B) s3 detTape n4 with hs4
  -- part C
  obtain ⟨e1, e2, e16, eP, e40, e41, e42, eR, eI, eM, ew, ecw⟩ :=
    i0_c (Blocks.prog B) B.o0 hE0 s4 d1 d2
  set s5 := run (Blocks.prog B) s4 detTape 7 with hs5
  have r0_3 : s3.core.regs 0 = δ := by rw [cR 0 (by simp), bR, ar0, input_mem0]
  have r1_3 : s3.core.regs 1 = 1 + δ / 4 := by rw [cR 1 (by simp), bR, ar1, input_mem0]
  have r7_3 : s3.core.regs 7 = 1 := by rw [cR 7 (by simp), bR, ar7]
  have r20_3 : s3.core.regs 20 = 0 := by rw [cR 20 (by simp), bR, ar20]
  have r21_3 : s3.core.regs 21 = 2 := by rw [cR 21 (by simp), bR, ar21]
  have r22_3 : s3.core.regs 22 = 4 := by rw [cR 22 (by simp), bR, ar22]
  have r2_3 : s3.core.regs 2 = lamOf N δ := by
    rw [cr2, bR, ar22, ar7, ar0, input_mem0, b5]; unfold lamOf; push_cast; ring
  have q23_4 : s4.core.ptrs 23 = N := by rw [dP 23 (by simp), q23_3]
  -- the global ladder
  set ρ : ℕ → ℝ := fun k => 1 / (1 + δ / 4) * (1 + δ / 4) ^ k with hρdef
  have hρ : ∀ k, ρ (k + 1) = ρ k * (1 + δ / 4) := fun k => by simp only [hρdef]; ring
  have hex : ∃ k, 8 * (N : ℝ) * lamOf N δ ≤ ρ k := gCond_ex δ N hδ
  obtain ⟨n6, hn6, f1, f2, f41, f42, fM, fI, fP, fR, fw, fcw⟩ :=
    ladder_spec_cw (Blocks.prog B) B.o1 hE1 ρ (1 + δ / 4) (8 * (N : ℝ) * lamOf N δ) hρ hex s5
      (by rw [e1]; rfl) e2
      (by rw [e40, q23_4, dR, r2_3]; push_cast; ring)
      (by rw [e41, dR, r7_3, r1_3]; simp only [hρdef]; ring)
      (by rw [e42, dR, r1_3, r20_3]; ring)
  set s6 := run (Blocks.prog B) s5 detTape n6 with hs6
  have hKG : Nat.find hex = KG N δ := by
    unfold KG; rw [dif_pos (gCond_ex δ N hδ)]
    apply le_antisymm
    · exact Nat.find_min' hex (Nat.find_spec (gCond_ex δ N hδ))
    · exact Nat.find_min' (gCond_ex δ N hδ) (Nat.find_spec hex)
  -- seg2 head
  obtain ⟨g1, g2, g3, g6, g7, gP, gR, gI, gM, gw, gcw⟩ :=
    i2_a (Blocks.prog B) B.o2 B.lbl_RETURN hE2 s6 (by rw [f1]; rfl) f2
  set s7 := run (Blocks.prog B) s6 detTape 6 with hs7
  have q12_6 : s6.core.ptrs 12 = 4 := by
    rw [fP 12 (by simp), eP 12 (by norm_num), dP 12 (by simp), c12]
  have q23_6 : s6.core.ptrs 23 = N := by
    rw [fP 23 (by simp), eP 23 (by norm_num), q23_4]
  have q7_7 : s7.core.ptrs 7 = 4 + N := by rw [g7, q12_6, q23_6]
  obtain ⟨n8, hn8, h1, h2, h7, hP, hR, hI, hI', hM, hw, hcw⟩ :=
    i2_pw (Blocks.prog B) B.o2 B.lbl_RETURN hE2 (4 + N) (T0G N δ) (T0G N δ + 1) 0 (by first | (clear * - hN; omega) | omega) s7 g1 g2
      (by rw [gP 42 (by simp), f42, hKG]; rfl) (by rw [g3]; simp) (by rw [g6]; simp)
      (by rw [q7_7]; simp)
  set s8 := run (Blocks.prog B) s7 detTape n8 with hs8
  obtain ⟨i1, i2, i15, i10, i3, i7, iP, iR, iI, iM, iw, icw⟩ :=
    i2_b (Blocks.prog B) B.o2 B.lbl_RETURN hE2 s8 h1 h2
  set s9 := run (Blocks.prog B) s8 detTape 4 with hs9
  have hHb : Hbase N (T0G N δ) = 4 + N + T0G N δ + 1 := rfl
  have q7_9 : s9.core.ptrs 7 = Hbase N (T0G N δ) := by rw [i7, h7, hHb]
  have q23_8 : s8.core.ptrs 23 = N := by rw [hP 23 (by simp), gP 23 (by simp), q23_6]
  have q23_9 : s9.core.ptrs 23 = N := by rw [iP 23 (by simp), q23_8]
  obtain ⟨n10, hn10, j1, j2, j7, jP, jR, jI, jI', jM, jw, jcw⟩ :=
    i2_rs (Blocks.prog B) B.o2 B.lbl_RETURN hE2 (Hbase N (T0G N δ)) N N 0 (by first | (clear * - hN; omega) | omega) s9 i1 i2 q23_9
      (by rw [i3]; simp) (by rw [q7_9]; simp)
  set s10 := run (Blocks.prog B) s9 detTape n10 with hs10
  obtain ⟨k1, k2, k2', k15, k8, k13, k14, kP, kR, kI, kM, kw, kcw⟩ :=
    i2_c (Blocks.prog B) B.o2 B.lbl_RETURN hE2 s10 j1 j2
  set s11 := run (Blocks.prog B) s10 detTape 17 with hs11
  have hv0 : s10.core.ptrs 7 = v0G N δ := by rw [j7]; rfl
  have q10_10 : s10.core.ptrs 10 = Hbase N (T0G N δ) := by
    rw [jP 10 (by simp), i10, h7, hHb]
  have q23_10 : s10.core.ptrs 23 = N := by rw [jP 23 (by simp), q23_9]
  have hHb5 : (5 : ℤ) ≤ Hbase N (T0G N δ) := by rw [hHb]; omega
  have hv0' : v0G N δ = Hbase N (T0G N δ) + N := rfl
  -- integer memory through the stages
  have J11 : ∀ z : ℤ, z ≠ v0G N δ + 3 → z ≠ v0G N δ + 7 → z ≠ 2 → z ≠ -10 →
      s11.integerMemory z = s10.integerMemory z := by
    intro z z1 z2 z3 z4
    rw [kI, hv0]
    simp only [Function.update_apply]
    rw [if_neg z4, if_neg z3, if_neg z2, if_neg z1]
  have J10 : ∀ z : ℤ, z < Hbase N (T0G N δ) → s10.integerMemory z = s8.integerMemory z := by
    intro z hz; rw [jI' z (Or.inl (by push_cast; omega)), iI]
  have J8 : ∀ z : ℤ, z < 4 + N → s8.integerMemory z = s7.integerMemory z := by
    intro z hz; exact hI' z (Or.inl (by push_cast; omega))
  have J7 : ∀ z : ℤ, z ≠ 3 → s7.integerMemory z = s4.integerMemory z := by
    intro z hz; rw [gI, Function.update_of_ne hz, fI, eI]
  have J4 : ∀ z : ℤ, z < 4 → s4.integerMemory z = s0.integerMemory z := by
    intro z hz; rw [dI' z (Or.inl (by push_cast; omega)), cI, bI, aI]
  have M11 : s11.core.mem = s0.core.mem := by
    rw [kM, jM, iM, hM, gM, fM, eM, dM, cM, bM, aM]
  -- registers and pointers at the end
  have R11 : ∀ x, x ∉ [2, 5, 6, 40, 41, 42, 43] → s11.core.regs x = s3.core.regs x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [kR, jR, iR, hR, gR, fR x hx.2.2.2.2.1 hx.2.2.2.2.2.2, eR x (by simp; omega), dR]
  have P11 : ∀ x, x ∉ [2, 3, 6, 7, 8, 9, 10, 13, 14, 15, 16, 27, 40, 41, 42, 43] →
      s11.core.ptrs x = s3.core.ptrs x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [kP x (by simp; omega), jP x (by simp; omega), iP x (by simp; omega), hP x (by simp; omega),
      gP x (by simp; omega), fP x (by simp; omega), eP x (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), dP x (by simp; omega)]
  refine ⟨14 + n2 + 8 + n4 + 7 + n6 + 6 + n8 + 4 + n10 + 17, ?_⟩
  have R2 : run (Blocks.prog B) s0 detTape (14 + n2) = s2 := by rw [run_add]
  have R3 : run (Blocks.prog B) s0 detTape (14 + n2 + 8) = s3 := by rw [run_add, R2]
  have R4 : run (Blocks.prog B) s0 detTape (14 + n2 + 8 + n4) = s4 := by rw [run_add, R3]
  have R5 : run (Blocks.prog B) s0 detTape (14 + n2 + 8 + n4 + 7) = s5 := by rw [run_add, R4]
  have R6 : run (Blocks.prog B) s0 detTape (14 + n2 + 8 + n4 + 7 + n6) = s6 := by rw [run_add, R5]
  have R7 : run (Blocks.prog B) s0 detTape (14 + n2 + 8 + n4 + 7 + n6 + 6) = s7 := by rw [run_add, R6]
  have R8 : run (Blocks.prog B) s0 detTape (14 + n2 + 8 + n4 + 7 + n6 + 6 + n8) = s8 := by
    rw [run_add, R7]
  have R9 : run (Blocks.prog B) s0 detTape (14 + n2 + 8 + n4 + 7 + n6 + 6 + n8 + 4) = s9 := by
    rw [run_add, R8]
  have R10 : run (Blocks.prog B) s0 detTape (14 + n2 + 8 + n4 + 7 + n6 + 6 + n8 + 4 + n10) = s10 := by
    rw [run_add, R9]
  have RR : run (Blocks.prog B) s0 detTape (14 + n2 + 8 + n4 + 7 + n6 + 6 + n8 + 4 + n10 + 17) = s11 := by
    rw [run_add, R10]
  have CW : cellsWritten (Blocks.prog B) s0 (14 + n2 + 8 + n4 + 7 + n6 + 6 + n8 + 4 + n10 + 17) =
      cellsWritten (Blocks.prog B) s0 14 ∪ cellsWritten (Blocks.prog B) s1 n2 ∪
        cellsWritten (Blocks.prog B) s2 8 ∪ cellsWritten (Blocks.prog B) s3 n4 ∪
        cellsWritten (Blocks.prog B) s4 7 ∪ cellsWritten (Blocks.prog B) s5 n6 ∪
        cellsWritten (Blocks.prog B) s6 6 ∪ cellsWritten (Blocks.prog B) s7 n8 ∪
        cellsWritten (Blocks.prog B) s8 4 ∪ cellsWritten (Blocks.prog B) s9 n10 ∪
        cellsWritten (Blocks.prog B) s10 17 := by
    rw [cellsWritten_add, R10, cellsWritten_add, R9, cellsWritten_add, R8, cellsWritten_add, R7,
      cellsWritten_add, R6, cellsWritten_add, R5, cellsWritten_add, R4, cellsWritten_add, R3,
      cellsWritten_add, R2, cellsWritten_add]
  rw [RR, CW]
  refine ⟨by rw [k1]; rfl, k2, ?_, by rw [k2', hv0], k13, k14, k8, by rw [k15, hv0], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- the global invariant
    refine ⟨by rw [P11 1 (by simp), q1_3], by rw [P11 12 (by simp), c12],
      by rw [P11 23 (by simp), q23_3], by rw [R11 0 (by simp), r0_3], by rw [R11 1 (by simp), r1_3],
      ?_, by rw [R11 20 (by simp), r20_3], by rw [R11 21 (by simp), r21_3],
      by rw [R11 22 (by simp), r22_3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [kR, jR, iR, hR, gR, fR 2 (by norm_num) (by norm_num), eR 2 (by simp), dR, r2_3]
    · rw [J11 1 (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), J10 1 (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), J8 1 (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega),
        J7 1 (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), J4 1 (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), input_im1]
    · rw [kI, Function.update_of_ne (by norm_num : (2 : ℤ) ≠ -10), Function.update_self, hv0]
    · rw [J11 3 (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), J10 3 (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), J8 3 (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), gI,
        Function.update_self, q12_6, q23_6]
    · intro g
      have hg := g.isLt
      rw [J11 _ (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), J10 _ (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), J8 _ (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega),
        J7 _ (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega)]
      exact dI g (Nat.zero_le _) hg
    · intro t ht
      rw [J11 _ (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), J10 _ (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega)]
      exact hI t (Nat.zero_le _) ht
    · intro g j
      rw [M11]; exact input_pts Y δ g j
  · rw [kP 16 (by simp), jP 16 (by simp), iP 16 (by simp), hP 16 (by simp), gP 16 (by simp),
      fP 16 (by simp), e16, d6]
  · rw [kI, hv0, Function.update_of_ne (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), Function.update_of_ne (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega),
      Function.update_of_ne (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), Function.update_self, q10_10]
  · rw [kI, hv0, Function.update_of_ne (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), Function.update_of_ne (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega),
      Function.update_self, q23_10]
  · intro i
    have hi : (i : ℕ) < N := by have := i.isLt; simpa using this
    rw [J11 _ (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega) (by first | (clear * - hHb5 hv0' hHb hN; omega) | (clear * - hHb5 hv0' hHb hN hi; omega) | omega), jI i (Nat.zero_le _) hi, univ_emb]
  · rw [kI, Function.update_self]
  · have : s11.work = s0.work + (14 + n2 + 8 + n4 + 7 + n6 + 6 + n8 + 4 + n10 + 17) := by
      rw [kw, jw, iw, hw, gw, fw, ew, dw, cw, bw, aw]; ring
    rw [this, w0, hn2, hn4, hn6, hn8, hn10, hKG]
    unfold T0G
    omega
  · exact init_cw N (T0G N δ) (s10.core.ptrs 7) _ _ _ _ _ _ _ _ _ _ _ acw bcw ccw dcw ecw fcw gcw hcw icw
      jcw kcw hv0

end DetANN.HPIM.PP

theorem solution : type_of% @DetANN.HPIM.PP.init_spec := @DetANN.HPIM.PP.init_spec
