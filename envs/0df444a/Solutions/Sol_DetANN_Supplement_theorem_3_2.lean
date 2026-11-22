-- Prove2me | solution 1 for DetANN.Supplement.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-21T07:12:41.508272+00:00
-- url     : https://prove2.me/submissions/a9f2a404-3861-4180-96c4-5c01d52ee682

import Mathlib
import Definitions.Def_DetANN_HPIMBSP
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMBalProg
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_SignChoice
import Definitions.Def_DetANN_Supplement_Greedy
import Definitions.Def_DetANN_Supplement_PreDedup
import Definitions.Def_DetANN_Supplement_BlockConstruction
import Definitions.Def_DetANN_BalancedBlocks
import Theorems.Thm_DetANN_Supplement_Thm32_eval_spec
import Theorems.Thm_DetANN_Supplement_Thm32_pre_setup_spec
import Theorems.Thm_DetANN_Supplement_Thm32_pre_params_spec
import Theorems.Thm_DetANN_theorem_3_2_greedy
import Theorems.Thm_DetANN_parseval_signed_blocks
import Theorems.Thm_DetANN_sylvester_hadamard
import Theorems.Thm_DetANN_Supplement_Thm32_ev_block
import Theorems.Thm_DetANN_Supplement_Thm32_reps_spec

namespace DetANN.HPIM.QP
end DetANN.HPIM.QP
namespace DetANN.HPIM
end DetANN.HPIM
namespace DetANN.HPIM.PP
end DetANN.HPIM.PP
namespace DetANN.HPIM.SegStep
end DetANN.HPIM.SegStep
namespace DetANN.Supplement
end DetANN.Supplement

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

end DetANN.HPIM.PP

-- ===== PP_Det =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib DetANN DetANN.HPIM

/-- One admissible deterministic instruction. -/
def Good (op : Instr) : Prop :=
  (match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True) ∧ (∀ r, op ≠ .coin r) ∧ (∀ r a e, op ≠ .rpow r a e)

lemma det_of_good {P : Program} (h : ∀ op ∈ P, Good op) : DetProgram P :=
  ⟨fun op hop => (h op hop).1, fun op hop => (h op hop).2⟩

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

-- ===== BB_Lay =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/-- The output tree `B` is stored at `u` with all its cells in `[u, u')` (integer) and `[v, v')`
(real), stably under any change outside these ranges. -/
def Good (s : State) (u v u' v' : ℤ) (B : BoxTree m) : Prop :=
  ∀ s'' : State, (∀ z, u ≤ z → z < u' → s''.integerMemory z = s.integerMemory z) →
    (∀ z, v ≤ z → z < v' → s''.core.mem z = s.core.mem z) → BoxTreeAt m s'' u B

end DetANN.HPIM.BB

-- ===== SegStep =====
namespace DetANN.HPIM.SegStep

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP

lemma embeds_app_right {Q A B : Program} {o : ℕ} (h : Embeds Q (A ++ B) o) :
    Embeds Q B (o + A.length) := by
  intro i x hx
  have := h (A.length + i) x (by rw [List.getElem?_append_right (by omega)]; simpa using hx)
  rwa [← Nat.add_assoc] at this

lemma embeds_app_left {Q A B : Program} {o : ℕ} (h : Embeds Q (A ++ B) o) : Embeds Q A o := by
  intro i x hx
  exact h i x (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]; exact hx)

lemma run_exec_seg {Q B : Program} {off c n i : ℕ} {ins : Instr} (hE : Embeds Q B (off + c))
    {s : State} {ω : ℕ → Bool} {k : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + n)
    (hn : i + c = n) (hB : B[i]? = some ins) : run Q s ω (k + 1) = run Q (exec ω ins s) ω k :=
  run_exec_at hE hh (by rw [hpc]; omega) hB

lemma cw_exec_seg {Q B : Program} {off c n i : ℕ} {ins : Instr} (hE : Embeds Q B (off + c))
    {s : State} {k : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + n) (hn : i + c = n)
    (hB : B[i]? = some ins) :
    cellsWritten Q s (k + 1) = (wcell ins s).toFinset ∪ cellsWritten Q (exec detTape ins s) k :=
  cw_exec_at hE hh (by rw [hpc]; omega) hB

end DetANN.HPIM.SegStep

-- ===== T32_EvProg =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP

lemma len_fw (off : ℕ) : (fw off).length = 23 := rfl

lemma det_fw (off : ℕ) : DetProgram (fw off) := by
  apply det_of_good
  intro op hop
  unfold fw at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals trivial

lemma det_evA (off : ℕ) : DetProgram (evA off) := by
  apply det_of_good
  intro op hop
  unfold evA at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨1, ?_⟩; norm_num; done)

lemma det_evB (off : ℕ) : DetProgram (evB off) := by
  apply det_of_good
  intro op hop
  unfold evB at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals trivial

end DetANN.Supplement.Thm32

-- ===== T32_PreProg =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP

lemma len_preA (q : ℚ) (off : ℕ) : (preA q off).length = 41 := rfl

lemma len_preB0 (q : ℚ) (off : ℕ) : (preB0 q off).length = 51 := rfl

lemma len_preB1 (q : ℚ) (off : ℕ) : (preB1 q off).length = 73 := rfl

lemma emb_preB {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB0 q off ++ preB1 q off ++ preB2 q off ++ preB3 q off ++ preB4 q off ++ preB5 q off ++ preB6 q off) (off + 64) := by
  have h := embeds_app_right hE
  simpa only [List.length_append, len_preA, len_fw, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_preB0 {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB0 q off) (off + 64) := by
  have h := embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (emb_preB hE))))))
  simpa only [Nat.add_zero] using h

lemma emb_preB2 {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB2 q off) (off + 188) := by
  have h := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (emb_preB hE)))))
  simpa only [List.length_append, len_preB0, len_preB1, Nat.add_assoc, Nat.reduceAdd] using h

end DetANN.Supplement.Thm32

-- ===== T32_PreSegC =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

/-- Sign index `k = 0`. -/
lemma g_init (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 188) (hh : s.halted = false) :
    (run Q s detTape 1).core.pc = off + 189 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs 48 = 0 ∧
      (∀ x, x ≠ 48 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- Sign `k` := `+1`; call `EVAL` with `ret = 0`. -/
lemma g_call (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 189) (hh : s.halted = false)
    (hb0 : s.core.ptrs 48 < s.core.ptrs 47) :
    (run Q s detTape 5).core.pc = off + 206 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 49 = s.core.ptrs 15 - s.core.ptrs 48 ∧
      (run Q s detTape 5).core.ptrs 50 = 0 ∧
      (∀ x, x ≠ 49 → x ≠ 50 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem (s.core.ptrs 15 - s.core.ptrs 48) = s.core.regs 7 ∧
      (∀ z, z ≠ s.core.ptrs 15 - s.core.ptrs 48 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 15 - s.core.ptrs 48) := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

/-- All signs done; `I[0] = L`. -/
lemma g_done (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 189) (hh : s.halted = false)
    (hb0 : s.core.ptrs 47 ≤ s.core.ptrs 48) :
    (run Q s detTape 2).core.pc = off + 205 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory (s.core.ptrs 0) = s.core.ptrs 14 ∧
      (∀ z, z ≠ s.core.ptrs 0 → (run Q s detTape 2).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      ∀ c ∈ cellsWritten Q s 2, c = (false, s.core.ptrs 0) := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

/-- Save `E(+1)`; sign `k` := `-1`; call `EVAL` with `ret = 1`. -/
lemma r0 (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 194) (hh : s.halted = false) :
    (run Q s detTape 4).core.pc = off + 206 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 50 = 1 ∧
      (∀ x, x ≠ 50 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs 12 = (s.core.regs 13 + s.core.regs 6) ∧
      (∀ x, x ≠ 12 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem (s.core.ptrs 49) = s.core.regs 8 ∧
      (∀ z, z ≠ s.core.ptrs 49 → (run Q s detTape 4).core.mem z = s.core.mem z) ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      ∀ c ∈ cellsWritten Q s 4, c = (true, s.core.ptrs 49) := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

/-- `E(+1) ≤ E(-1)`: sign `k` := `+1`; next sign. -/
lemma r1_set (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 198) (hh : s.halted = false)
    (hb0 : (s.core.regs 12 - s.core.regs 13) ≤ 0) :
    (run Q s detTape 5).core.pc = off + 189 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 48 = s.core.ptrs 48 + 1 ∧
      (∀ x, x ≠ 48 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs 2 = (s.core.regs 12 - s.core.regs 13) ∧
      (∀ x, x ≠ 2 → (run Q s detTape 5).core.regs x = s.core.regs x) ∧
      (run Q s detTape 5).core.mem (s.core.ptrs 49) = s.core.regs 7 ∧
      (∀ z, z ≠ s.core.ptrs 49 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 49) := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

/-- `E(+1) > E(-1)`: keep `-1`; next sign. -/
lemma r1_keep (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 198) (hh : s.halted = false)
    (hb0 : ¬ (s.core.regs 12 - s.core.regs 13) ≤ 0) :
    (run Q s detTape 5).core.pc = off + 189 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 48 = s.core.ptrs 48 + 1 ∧
      (∀ x, x ≠ 48 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs 2 = (s.core.regs 12 - s.core.regs 13) ∧
      (∀ x, x ≠ 2 → (run Q s detTape 5).core.regs x = s.core.regs x) ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

end DetANN.Supplement.Thm32

-- ===== T32_Greedy =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

lemma pre_halt (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 205) (hh : s.halted = false) :
    (run Q s detTape 1).halted = true ∧ (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh ⊢
  subst hh
  rw [hpc, run_exec_seg hS rfl rfl rfl rfl]
  simp [exec, run_zero]

lemma signsAt_set {mem mem' : ℤ → ℝ} {L k : ℕ} {ξ : Fin L → Fin (2 ^ k) → Bool} (kk : ℕ) (b : Bool)
    (hS : SignsAt mem L k ξ) (hw : mem' (-(2 ^ k : ℤ) - 1 - kk) = signOf b)
    (hfr : ∀ z, z ≠ -(2 ^ k : ℤ) - 1 - kk → mem' z = mem z) :
    SignsAt mem' L k (setSignAt kk b ξ) := by
  intro ℓ r
  unfold setSignAt
  by_cases h : (ℓ : ℕ) * 2 ^ k + r = kk
  · rw [if_pos h]
    have e : ((ℓ : ℤ) * 2 ^ k + r) = kk := by exact_mod_cast h
    rw [e]; exact hw
  · rw [if_neg h]
    have hne : -(2 ^ k : ℤ) - 1 - ((ℓ : ℤ) * 2 ^ k + r) ≠ -(2 ^ k : ℤ) - 1 - kk := by
      intro e
      apply h
      have : ((ℓ : ℤ) * 2 ^ k + r) = kk := by linarith
      exact_mod_cast this
    rw [hfr _ hne]; exact hS ℓ r

lemma signsAt_of {mem mem' : ℤ → ℝ} {L k : ℕ} {ξ : Fin L → Fin (2 ^ k) → Bool}
    (hS : SignsAt mem L k ξ) (hfr : ∀ z, z < 0 → mem' z = mem z) : SignsAt mem' L k ξ := by
  intro ℓ r
  rw [hfr _ (by
    have : (0 : ℤ) ≤ (ℓ : ℤ) * 2 ^ k + r := by positivity
    have : (0 : ℤ) < 2 ^ k := by positivity
    omega)]
  exact hS ℓ r

lemma setSignAt_twice {L d : ℕ} (kk : ℕ) (b b' : Bool) (ξ : Fin L → Fin d → Bool) :
    setSignAt kk b (setSignAt kk b' ξ) = setSignAt kk b ξ := by
  funext ℓ r; unfold setSignAt; split_ifs <;> rfl

/-- Everything `EVAL` reads that the greedy loop keeps fixed. -/
def Ctx (k L p₀ : ℕ) (τ : ℝ) (l : List (EuclideanSpace ℝ (Fin (2 ^ k)))) (Hb Db t0 : ℤ)
    (s : State) : Prop :=
  s.core.ptrs 0 = 0 ∧ s.core.ptrs 1 = 1 ∧ s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ) ∧ s.core.ptrs 14 = L ∧
  s.core.ptrs 15 = -((2 ^ k : ℕ) : ℤ) - 1 ∧ s.core.ptrs 24 = Hb ∧ s.core.ptrs 26 = Db ∧
  s.core.ptrs 27 = Db + ((l.length * 2 ^ k : ℕ) : ℤ) ∧ s.core.ptrs 36 = 2 * (p₀ : ℤ) ∧
  s.core.ptrs 37 = 2 * (p₀ : ℤ) + 1 ∧ s.core.ptrs 39 = 4 * (p₀ : ℤ) + 1 ∧ s.core.ptrs 40 = t0 ∧
  s.core.ptrs 41 = t0 + (4 * (p₀ : ℤ) + 1) ∧ s.core.ptrs 42 = t0 + 2 * (4 * (p₀ : ℤ) + 1) ∧
  s.core.ptrs 43 = t0 + 3 * (4 * (p₀ : ℤ) + 1) ∧
  s.core.ptrs 44 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + (2 * (p₀ : ℤ) + 1) ∧
  s.core.ptrs 45 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + 2 * (2 * (p₀ : ℤ) + 1) ∧
  s.core.ptrs 46 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + 3 * (2 * (p₀ : ℤ) + 1) ∧
  s.core.ptrs 47 = ((L * 2 ^ k : ℕ) : ℤ) ∧
  s.core.regs 5 = τ ∧ s.core.regs 6 = 0 ∧ s.core.regs 7 = 1 ∧ s.core.regs 8 = -1 ∧
  (∀ r j : Fin (2 ^ k), s.core.mem (Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) = sylvester k j r) ∧
  TableAt s.core.mem Db l ∧
  (∀ i : ℕ, i < 4 * p₀ + 1 → s.core.mem (t0 + i) = (i.factorial : ℝ))

/-- The pointers kept by `Ctx`. -/
def CritP (y : ℕ) : Prop :=
  y = 0 ∨ y = 1 ∨ y = 3 ∨ y = 14 ∨ y = 15 ∨ y = 24 ∨ y = 26 ∨ y = 27 ∨ y = 36 ∨ y = 37 ∨
    (39 ≤ y ∧ y ≤ 47)

lemma ctx_of {k L p₀ : ℕ} {τ : ℝ} {l : List (EuclideanSpace ℝ (Fin (2 ^ k)))} {Hb Db t0 : ℤ}
    (hH0 : 0 ≤ Hb) (hHD : Hb + ((2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ Db)
    (hDt : Db + ((l.length * 2 ^ k : ℕ) : ℤ) ≤ t0) {s s' : State}
    (hc : Ctx k L p₀ τ l Hb Db t0 s) (hp : ∀ y, CritP y → s'.core.ptrs y = s.core.ptrs y)
    (hr : ∀ y, 5 ≤ y → y ≤ 8 → s'.core.regs y = s.core.regs y)
    (hm : ∀ z, 0 ≤ z → z < t0 + (4 * (p₀ : ℤ) + 1) → s'.core.mem z = s.core.mem z) :
    Ctx k L p₀ τ l Hb Db t0 s' := by
  obtain ⟨a0, a1, a3, a14, a15, a24, a26, a27, a36, a37, a39, a40, a41, a42, a43, a44, a45, a46, a47,
    b5, b6, b7, b8, hcol, hT, hF⟩ := hc
  have hd0 : (0 : ℤ) ≤ ((2 ^ k * 2 ^ k : ℕ) : ℤ) := by positivity
  have hl0 : (0 : ℤ) ≤ ((l.length * 2 ^ k : ℕ) : ℤ) := by positivity
  have hK : (0 : ℤ) ≤ (p₀ : ℤ) := by positivity
  refine ⟨by rw [hp 0 (by unfold CritP; omega)]; exact a0, by rw [hp 1 (by unfold CritP; omega)]; exact a1,
    by rw [hp 3 (by unfold CritP; omega)]; exact a3, by rw [hp 14 (by unfold CritP; omega)]; exact a14,
    by rw [hp 15 (by unfold CritP; omega)]; exact a15, by rw [hp 24 (by unfold CritP; omega)]; exact a24,
    by rw [hp 26 (by unfold CritP; omega)]; exact a26, by rw [hp 27 (by unfold CritP; omega)]; exact a27,
    by rw [hp 36 (by unfold CritP; omega)]; exact a36, by rw [hp 37 (by unfold CritP; omega)]; exact a37,
    by rw [hp 39 (by unfold CritP; omega)]; exact a39, by rw [hp 40 (by unfold CritP; omega)]; exact a40,
    by rw [hp 41 (by unfold CritP; omega)]; exact a41, by rw [hp 42 (by unfold CritP; omega)]; exact a42,
    by rw [hp 43 (by unfold CritP; omega)]; exact a43, by rw [hp 44 (by unfold CritP; omega)]; exact a44,
    by rw [hp 45 (by unfold CritP; omega)]; exact a45, by rw [hp 46 (by unfold CritP; omega)]; exact a46,
    by rw [hp 47 (by unfold CritP; omega)]; exact a47,
    by rw [hr 5 (by omega) (by omega)]; exact b5, by rw [hr 6 (by omega) (by omega)]; exact b6,
    by rw [hr 7 (by omega) (by omega)]; exact b7, by rw [hr 8 (by omega) (by omega)]; exact b8,
    ?_, ?_, ?_⟩
  · intro r j
    have hlt : (r : ℕ) * 2 ^ k + j < 2 ^ k * 2 ^ k := by
      have := r.isLt; have := j.isLt; nlinarith
    have hlt' : (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ) < ((2 ^ k * 2 ^ k : ℕ) : ℤ) := by exact_mod_cast hlt
    have : (0 : ℤ) ≤ (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ) := by positivity
    rw [hm _ (by omega) (by omega)]; exact hcol r j
  · intro m v hv c
    have hm' : m < l.length := by
      by_contra h; push Not at h; rw [List.getElem?_eq_none h] at hv; exact absurd hv (by simp)
    have hlt : m * 2 ^ k + (c : ℕ) < l.length * 2 ^ k := by
      have := c.isLt
      calc m * 2 ^ k + (c : ℕ) < m * 2 ^ k + 2 ^ k := by omega
        _ = (m + 1) * 2 ^ k := by ring
        _ ≤ l.length * 2 ^ k := Nat.mul_le_mul_right _ hm'
    have hlt' : ((m * 2 ^ k + (c : ℕ) : ℕ) : ℤ) < ((l.length * 2 ^ k : ℕ) : ℤ) := by exact_mod_cast hlt
    have : (0 : ℤ) ≤ ((m * 2 ^ k + (c : ℕ) : ℕ) : ℤ) := by positivity
    rw [hm _ (by omega) (by omega)]; exact hT m v hv c
  · intro i hi
    have : (i : ℤ) < 4 * (p₀ : ℤ) + 1 := by exact_mod_cast hi
    have : (0 : ℤ) ≤ (i : ℤ) := by positivity
    rw [hm _ (by omega) (by omega)]; exact hF i hi

lemma eval_call (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (k L p₀ : ℕ)
    (hL : 1 ≤ L) (τ : ℝ) (hτ : 0 < τ) (l : List (EuclideanSpace ℝ (Fin (2 ^ k)))) (hl : l.Nodup)
    (hl0 : ∀ v ∈ l, v ≠ 0) (Hb Db t0 : ℤ) (hHD : Hb + ((2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ Db)
    (hDt : Db + ((l.length * 2 ^ k : ℕ) : ℤ) ≤ t0) (hH0 : 0 ≤ Hb) (kk : ℕ) (hkk : kk < L * 2 ^ k)
    (ξ : Fin L → Fin (2 ^ k) → Bool) (ret : ℤ) (hret : ret = 0 ∨ ret = 1) (s : State)
    (hpc : s.core.pc = off + 206) (hh : s.halted = false) (hc : Ctx k L p₀ τ l Hb Db t0 s)
    (h48 : s.core.ptrs 48 = kk) (h50 : s.core.ptrs 50 = ret) (hS : SignsAt s.core.mem L k ξ) :
    ∃ t, t ≤ evalB l.length (2 ^ k) L p₀ ∧
      (ret = 0 → (run Q s detTape t).core.pc = off + 194) ∧
      (ret = 1 → (run Q s detTape t).core.pc = off + 198) ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.regs 13 =
        lemma62Expr (sylvester k) L τ p₀ l.toFinset (prefixMask L (2 ^ k) (kk + 1)) ξ ∧
      Ctx k L p₀ τ l Hb Db t0 (run Q s detTape t) ∧ SignsAt (run Q s detTape t).core.mem L k ξ ∧
      (run Q s detTape t).core.ptrs 48 = s.core.ptrs 48 ∧
      (run Q s detTape t).core.ptrs 49 = s.core.ptrs 49 ∧
      (run Q s detTape t).core.regs 12 = s.core.regs 12 ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t := by
  have hc' := hc
  obtain ⟨a0, a1, a3, a14, a15, a24, a26, a27, a36, a37, a39, a40, a41, a42, a43, a44, a45, a46, _,
    b5, b6, b7, _, hcol, hT, hF⟩ := hc'
  obtain ⟨t, ht, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ :=
    eval_spec Q off q hE k L p₀ kk hL hkk τ hτ l hl hl0 ξ Hb Db t0 ret hHD hDt hH0 hret s hpc hh
      a0 a1 a3 a14 a15 a24 a26 a27 a36 a37 a39 a40 a41 a42 a43 a44 a45 a46 h48 h50 b5 b6 b7 hcol hT hF
      hS
  have hd0 : (0 : ℤ) ≤ ((2 ^ k * 2 ^ k : ℕ) : ℤ) := by positivity
  have hl0' : (0 : ℤ) ≤ ((l.length * 2 ^ k : ℕ) : ℤ) := by positivity
  have hK : (0 : ℤ) ≤ (p₀ : ℤ) := by positivity
  have ht0 : 0 ≤ t0 := by omega
  refine ⟨t, ht, e1, e2, e3, e4, ctx_of hH0 hHD hDt hc
    (fun y hy => e5 y (by unfold CritP at hy; omega) (by unfold CritP at hy; omega)
      (by unfold CritP at hy; omega) (by unfold CritP at hy; omega) (by unfold CritP at hy; omega)
      (by unfold CritP at hy; omega) (by unfold CritP at hy; omega) (by unfold CritP at hy; omega)
      (by unfold CritP at hy; omega) (by unfold CritP at hy; omega) (by unfold CritP at hy; omega))
    (fun y a b => e6 y (by omega) (by omega) (by omega))
    (fun z _ hz => e7 z (Or.inl hz)),
    signsAt_of hS (fun z hz => e7 z (Or.inl (by omega))),
    e5 48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by omega),
    e5 49 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by omega),
    e6 12 (by decide) (by decide) (by omega), e8, e9⟩

lemma greedy_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (k L p₀ : ℕ)
    (hL : 1 ≤ L) (τ : ℝ) (hτ : 0 < τ) (l : List (EuclideanSpace ℝ (Fin (2 ^ k)))) (hl : l.Nodup)
    (hl0 : ∀ v ∈ l, v ≠ 0) (Hb Db t0 : ℤ) (hHD : Hb + ((2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ Db)
    (hDt : Db + ((l.length * 2 ^ k : ℕ) : ℤ) ≤ t0) (hH0 : 0 ≤ Hb) :
    ∀ (kk k' : ℕ) (s : State), k' + kk = L * 2 ^ k → s.core.pc = off + 189 → s.halted = false →
      Ctx k L p₀ τ l Hb Db t0 s → s.core.ptrs 48 = k' →
      SignsAt s.core.mem L k (greedySigns (lemma62Expr (sylvester k) L τ p₀ l.toFinset) k') →
      ∃ t, t ≤ kk * (2 * evalB l.length (2 ^ k) L p₀ + 14) + 3 ∧
        (run Q s detTape t).halted = true ∧
        SignsAt (run Q s detTape t).core.mem L k
          (greedySigns (lemma62Expr (sylvester k) L τ p₀ l.toFinset) (L * 2 ^ k)) ∧
        (run Q s detTape t).integerMemory 0 = L ∧
        (∀ z, z ≠ 0 → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (run Q s detTape t).work = s.work + t := by
  have hd0 : (0 : ℤ) ≤ ((2 ^ k * 2 ^ k : ℕ) : ℤ) := by positivity
  have hl0' : (0 : ℤ) ≤ ((l.length * 2 ^ k : ℕ) : ℤ) := by positivity
  have hpk : (0 : ℤ) < 2 ^ k := by positivity
  intro kk
  induction kk with
  | zero =>
    intro k' s hk hpc hh hc h48 hS
    obtain ⟨a0, _, _, a14, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a47, _⟩ := hc
    obtain ⟨g1, g2, _, _, g5, g6, g7, g8, _⟩ :=
      g_done Q off q hE s hpc hh (by rw [a47, h48]; exact_mod_cast (by omega : L * 2 ^ k ≤ k'))
    set s1 := run Q s detTape 2 with hs1
    obtain ⟨u1, u2, u3, u4⟩ := pre_halt Q off q hE s1 g1 g2
    refine ⟨2 + 1, by omega, ?_⟩
    rw [run_add, ← hs1]
    have hk' : k' = L * 2 ^ k := by omega
    subst hk'
    refine ⟨u1, by rw [u2, g5]; exact hS, by rw [u3, ← a0, g6, a14], fun z hz => by
      rw [u3, g7 z (by rw [a0]; exact hz)], by rw [u4, g8]⟩
  | succ kk ih =>
    intro k' s hk hpc hh hc h48 hS
    set F := lemma62Expr (sylvester k) L τ p₀ l.toFinset with hF
    set ξ := greedySigns F k' with hξ
    have hkk : k' < L * 2 ^ k := by omega
    have hk0 : (0 : ℤ) ≤ k' := by positivity
    have hc0 := hc
    obtain ⟨_, _, _, _, a15, _, _, _, _, _, _, _, _, _, _, _, _, _, a47, _, _, b7, b8, _⟩ := hc0
    have hcell : s.core.ptrs 15 - s.core.ptrs 48 = -(2 ^ k : ℤ) - 1 - k' := by
      rw [a15, h48]; push_cast; ring
    -- sign k' := +1, first call
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
      g_call Q off q hE s hpc hh (by rw [a47, h48]; exact_mod_cast hkk)
    set s1 := run Q s detTape 5 with hs1
    rw [hcell] at g3 g7 g8
    have hS1 : SignsAt s1.core.mem L k (setSignAt k' true ξ) :=
      signsAt_set k' true hS (by rw [g7, b7]; simp [signOf]) g8
    have hc1 : Ctx k L p₀ τ l Hb Db t0 s1 :=
      ctx_of hH0 hHD hDt hc (fun y hy => g5 y (by unfold CritP at hy; omega) (by unfold CritP at hy; omega))
        (fun y _ _ => by rw [g6]) (fun z hz _ => g8 z (by omega))
    obtain ⟨t2, ht2, e1, _, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ :=
      eval_call Q off q hE k L p₀ hL τ hτ l hl hl0 Hb Db t0 hHD hDt hH0 k' hkk
        (setSignAt k' true ξ) 0 (Or.inl rfl) s1 g1 g2 hc1 (by rw [g5 48 (by decide) (by decide), h48])
        g4 hS1
    set s2 := run Q s1 detTape t2 with hs2
    have p2 := e1 rfl
    -- save E(+1), sign k' := -1, second call
    have hc2 := e5
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, c6, _, c8, _⟩ := hc2
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, _⟩ := r0 Q off q hE s2 p2 e3
    set s3 := run Q s2 detTape 4 with hs3
    have h49 : s2.core.ptrs 49 = -(2 ^ k : ℤ) - 1 - k' := by rw [e8, g3]
    rw [h49] at r7 r8
    have hS3 : SignsAt s3.core.mem L k (setSignAt k' false ξ) := by
      rw [← setSignAt_twice k' false true ξ]
      exact signsAt_set k' false e6 (by rw [r7, c8]; simp [signOf]) r8
    have hc3 : Ctx k L p₀ τ l Hb Db t0 s3 :=
      ctx_of hH0 hHD hDt e5 (fun y hy => r4 y (by unfold CritP at hy; omega))
        (fun y _ _ => r6 y (by omega)) (fun z hz _ => r8 z (by omega))
    have h48s2 : s2.core.ptrs 48 = k' := by rw [e7, g5 48 (by decide) (by decide), h48]
    obtain ⟨t4, ht4, _, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ :=
      eval_call Q off q hE k L p₀ hL τ hτ l hl hl0 Hb Db t0 hHD hDt hH0 k' hkk
        (setSignAt k' false ξ) 1 (Or.inr rfl) s3 r1 r2 hc3
        (by rw [r4 48 (by decide), h48s2]) r3 hS3
    set s4 := run Q s3 detTape t4 with hs4
    have p4 := f2 rfl
    have hr12 : s4.core.regs 12 = F (prefixMask L (2 ^ k) (k' + 1)) (setSignAt k' true ξ) := by
      rw [f9, r5, e4, c6]; ring
    have h49' : s4.core.ptrs 49 = -(2 ^ k : ℤ) - 1 - k' := by
      rw [f8, r4 49 (by decide), h49]
    have h48' : s4.core.ptrs 48 = k' := by rw [f7, r4 48 (by decide), h48s2]
    have hc4 := f5
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, d7, _, _⟩ := hc4
    -- compare and continue
    have hstep : (run Q s4 detTape 5).core.pc = off + 189 ∧
        (run Q s4 detTape 5).halted = false ∧
        Ctx k L p₀ τ l Hb Db t0 (run Q s4 detTape 5) ∧
        (run Q s4 detTape 5).core.ptrs 48 = k' + 1 ∧
        SignsAt (run Q s4 detTape 5).core.mem L k (greedySigns F (k' + 1)) ∧
        (run Q s4 detTape 5).integerMemory = s4.integerMemory ∧
        (run Q s4 detTape 5).work = s4.work + 5 := by
      by_cases hcmp : F (prefixMask L (2 ^ k) (k' + 1)) (setSignAt k' true ξ) ≤
          F (prefixMask L (2 ^ k) (k' + 1)) (setSignAt k' false ξ)
      · obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, _⟩ :=
          r1_set Q off q hE s4 p4 f3 (by rw [hr12, f4]; linarith)
        rw [h49'] at w7 w8
        refine ⟨w1, w2, ctx_of hH0 hHD hDt f5 (fun y hy => w4 y (by unfold CritP at hy; omega))
          (fun y _ _ => w6 y (by omega)) (fun z hz _ => w8 z (by omega)), by rw [w3, h48'], ?_, w9, w10⟩
        have : greedySigns F (k' + 1) = setSignAt k' true ξ := by
          simp only [greedySigns]; rw [if_pos hcmp]
        rw [this, ← setSignAt_twice k' true false ξ]
        exact signsAt_set k' true f6 (by rw [w7, d7]; simp [signOf]) w8
      · obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, _⟩ :=
          r1_keep Q off q hE s4 p4 f3 (by rw [hr12, f4]; push Not at hcmp; linarith)
        refine ⟨w1, w2, ctx_of hH0 hHD hDt f5 (fun y hy => w4 y (by unfold CritP at hy; omega))
          (fun y _ _ => w6 y (by omega)) (fun z _ _ => by rw [w7]), by rw [w3, h48'], ?_, w8, w9⟩
        have : greedySigns F (k' + 1) = setSignAt k' false ξ := by
          simp only [greedySigns]; rw [if_neg hcmp]
        rw [this, w7]; exact f6
    obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := hstep
    set s5 := run Q s4 detTape 5 with hs5
    obtain ⟨t6, ht6, x1, x2, x3, x4, x5⟩ := ih (k' + 1) s5 (by omega) v1 v2 v3 v4 v5
    refine ⟨5 + t2 + 4 + t4 + 5 + t6, ?_, ?_⟩
    · have : (kk + 1) * (2 * evalB l.length (2 ^ k) L p₀ + 14) =
          kk * (2 * evalB l.length (2 ^ k) L p₀ + 14) + 2 * evalB l.length (2 ^ k) L p₀ + 14 := by ring
      omega
    have e : run Q s detTape (5 + t2 + 4 + t4 + 5 + t6) = run Q s5 detTape t6 := by
      rw [run_add, run_add, run_add, run_add, run_add, ← hs1, ← hs2, ← hs3, ← hs4, ← hs5]
    rw [e]
    exact ⟨x1, x2, x3, fun z hz => by rw [x4 z hz, v6, f10, r9, e10, g9],
      by rw [x5, v7, f11, r10, e11, g10]; ring⟩

end DetANN.Supplement.Thm32

-- ===== T32_PreSegA =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

/-- Empty table at `top`. -/
lemma dd_init (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 67) (hh : s.halted = false) :
    (run Q s detTape 5).core.pc = off + 72 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 10 = 0 ∧
      (run Q s detTape 5).core.ptrs 26 = s.core.ptrs 23 ∧
      (run Q s detTape 5).core.ptrs 27 = s.core.ptrs 23 ∧
      (run Q s detTape 5).core.ptrs 28 = 0 ∧
      (run Q s detTape 5).core.ptrs 29 = 1 ∧
      (∀ x, x ≠ 10 → x ≠ 26 → x ≠ 27 → x ≠ 28 → x ≠ 29 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- All pairs done; `top = Dend`. -/
lemma di_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 72) (hh : s.halted = false)
    (hb0 : s.core.ptrs 22 ≤ s.core.ptrs 10) :
    (run Q s detTape 2).core.pc = off + 115 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 23 = s.core.ptrs 27 ∧
      (∀ x, x ≠ 23 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma di_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 72) (hh : s.halted = false)
    (hb0 : s.core.ptrs 10 < s.core.ptrs 22) :
    (run Q s detTape 4).core.pc = off + 76 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 20 = s.core.ptrs 10 + 1 ∧
      (run Q s detTape 4).core.ptrs 30 = s.core.ptrs 29 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 20 → x ≠ 30 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma dj_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 76) (hh : s.halted = false)
    (hb0 : s.core.ptrs 22 ≤ s.core.ptrs 20) :
    (run Q s detTape 4).core.pc = off + 72 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 10 = s.core.ptrs 10 + 1 ∧
      (run Q s detTape 4).core.ptrs 29 = s.core.ptrs 29 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 10 → x ≠ 29 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma dj_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 76) (hh : s.halted = false)
    (hb0 : s.core.ptrs 20 < s.core.ptrs 22) :
    (run Q s detTape 2).core.pc = off + 78 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 31 = 0 ∧
      (∀ x, x ≠ 31 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- One coordinate of `P_i - P_j` at `Dend`. -/
lemma w_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (x y : ℝ) (s : State)
    (hpc : s.core.pc = off + 78) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 29 + s.core.ptrs 31) = x)
    (fr1 : s.core.mem (s.core.ptrs 30 + s.core.ptrs 31) = y)
    (hb0 : s.core.ptrs 31 < s.core.ptrs 3) :
    (run Q s detTape 10).core.pc = off + 78 ∧
      (run Q s detTape 10).halted = false ∧
      (run Q s detTape 10).core.ptrs 11 = s.core.ptrs 27 + s.core.ptrs 31 ∧
      (run Q s detTape 10).core.ptrs 31 = s.core.ptrs 31 + 1 ∧
      (∀ x, x ≠ 11 → x ≠ 31 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 10).core.regs 0 = (x - y) ∧
      (run Q s detTape 10).core.regs 1 = y ∧
      (∀ x, x ≠ 0 → x ≠ 1 → (run Q s detTape 10).core.regs x = s.core.regs x) ∧
      (run Q s detTape 10).core.mem (s.core.ptrs 27 + s.core.ptrs 31) = (x - y) ∧
      (∀ z, z ≠ s.core.ptrs 27 + s.core.ptrs 31 → (run Q s detTape 10).core.mem z = s.core.mem z) ∧
      (run Q s detTape 10).integerMemory = s.integerMemory ∧
      (run Q s detTape 10).work = s.work + 10 ∧
      ∀ c ∈ cellsWritten Q s 10, c = (true, s.core.ptrs 27 + s.core.ptrs 31) := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 29 + ptrs 31 → mem z = x := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 30 + ptrs 31 → mem z = y := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma w_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 78) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 31) :
    (run Q s detTape 2).core.pc = off + 89 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 32 = s.core.ptrs 26 ∧
      (∀ x, x ≠ 32 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- Not found: append. -/
lemma e_new (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 89) (hh : s.halted = false)
    (hb0 : s.core.ptrs 27 ≤ s.core.ptrs 32) :
    (run Q s detTape 6).core.pc = off + 76 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 20 = s.core.ptrs 20 + 1 ∧
      (run Q s detTape 6).core.ptrs 27 = s.core.ptrs 27 + s.core.ptrs 3 ∧
      (run Q s detTape 6).core.ptrs 28 = s.core.ptrs 28 + 1 ∧
      (run Q s detTape 6).core.ptrs 30 = s.core.ptrs 30 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 20 → x ≠ 27 → x ≠ 28 → x ≠ 30 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma e_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 89) (hh : s.halted = false)
    (hb0 : s.core.ptrs 32 < s.core.ptrs 27) :
    (run Q s detTape 2).core.pc = off + 91 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 31 = 0 ∧
      (∀ x, x ≠ 31 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- Equal: a duplicate. -/
lemma c_dup (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 91) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 31) :
    (run Q s detTape 4).core.pc = off + 76 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 20 = s.core.ptrs 20 + 1 ∧
      (run Q s detTape 4).core.ptrs 30 = s.core.ptrs 30 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 20 → x ≠ 30 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma c_mis1 (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (a b : ℝ) (s : State)
    (hpc : s.core.pc = off + 91) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 32 + s.core.ptrs 31) = a)
    (fr1 : s.core.mem (s.core.ptrs 27 + s.core.ptrs 31) = b)
    (hb0 : s.core.ptrs 31 < s.core.ptrs 3)
    (hb1 : ¬ (a - b) ≤ 0) :
    (run Q s detTape 10).core.pc = off + 89 ∧
      (run Q s detTape 10).halted = false ∧
      (run Q s detTape 10).core.ptrs 11 = s.core.ptrs 27 + s.core.ptrs 31 ∧
      (run Q s detTape 10).core.ptrs 32 = s.core.ptrs 32 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 11 → x ≠ 32 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 10).core.regs 0 = a ∧
      (run Q s detTape 10).core.regs 1 = b ∧
      (run Q s detTape 10).core.regs 2 = (a - b) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → (run Q s detTape 10).core.regs x = s.core.regs x) ∧
      (run Q s detTape 10).core.mem = s.core.mem ∧
      (run Q s detTape 10).integerMemory = s.integerMemory ∧
      (run Q s detTape 10).work = s.work + 10 ∧
      cellsWritten Q s 10 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 32 + ptrs 31 → mem z = a := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 27 + ptrs 31 → mem z = b := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma c_mis2 (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (a b : ℝ) (s : State)
    (hpc : s.core.pc = off + 91) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 32 + s.core.ptrs 31) = a)
    (fr1 : s.core.mem (s.core.ptrs 27 + s.core.ptrs 31) = b)
    (hb0 : s.core.ptrs 31 < s.core.ptrs 3)
    (hb1 : (a - b) ≤ 0)
    (hb2 : ¬ (b - a) ≤ 0) :
    (run Q s detTape 12).core.pc = off + 89 ∧
      (run Q s detTape 12).halted = false ∧
      (run Q s detTape 12).core.ptrs 11 = s.core.ptrs 27 + s.core.ptrs 31 ∧
      (run Q s detTape 12).core.ptrs 32 = s.core.ptrs 32 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 11 → x ≠ 32 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 12).core.regs 0 = a ∧
      (run Q s detTape 12).core.regs 1 = b ∧
      (run Q s detTape 12).core.regs 2 = (b - a) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → (run Q s detTape 12).core.regs x = s.core.regs x) ∧
      (run Q s detTape 12).core.mem = s.core.mem ∧
      (run Q s detTape 12).integerMemory = s.integerMemory ∧
      (run Q s detTape 12).work = s.work + 12 ∧
      cellsWritten Q s 12 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 32 + ptrs 31 → mem z = a := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 27 + ptrs 31 → mem z = b := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma c_eq (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (a b : ℝ) (s : State)
    (hpc : s.core.pc = off + 91) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 32 + s.core.ptrs 31) = a)
    (fr1 : s.core.mem (s.core.ptrs 27 + s.core.ptrs 31) = b)
    (hb0 : s.core.ptrs 31 < s.core.ptrs 3)
    (hb1 : (a - b) ≤ 0)
    (hb2 : (b - a) ≤ 0) :
    (run Q s detTape 11).core.pc = off + 91 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 11 = s.core.ptrs 27 + s.core.ptrs 31 ∧
      (run Q s detTape 11).core.ptrs 31 = s.core.ptrs 31 + 1 ∧
      (∀ x, x ≠ 11 → x ≠ 31 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs 0 = a ∧
      (run Q s detTape 11).core.regs 1 = b ∧
      (run Q s detTape 11).core.regs 2 = (b - a) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → (run Q s detTape 11).core.regs x = s.core.regs x) ∧
      (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).integerMemory = s.integerMemory ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      cellsWritten Q s 11 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 32 + ptrs 31 → mem z = a := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 27 + ptrs 31 → mem z = b := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

end DetANN.Supplement.Thm32

-- ===== T32_DedupMath =====
namespace DetANN.Supplement.Thm32

variable {d : ℕ}

lemma ddStep_mem {l : List (EuclideanSpace ℝ (Fin d))} {v w : EuclideanSpace ℝ (Fin d)} :
    w ∈ ddStep l v ↔ w ∈ l ∨ w = v := by
  unfold ddStep
  split_ifs with h
  · constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | rfl); exact hw; exact h
  · simp [List.mem_append]

lemma ddStep_nodup {l : List (EuclideanSpace ℝ (Fin d))} (hl : l.Nodup) (v : EuclideanSpace ℝ (Fin d)) :
    (ddStep l v).Nodup := by
  unfold ddStep
  split_ifs with h
  · exact hl
  · exact List.nodup_append.2 ⟨hl, List.nodup_singleton v, by
      intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact h ha⟩

lemma ddStep_length_le (l : List (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d)) :
    l.length ≤ (ddStep l v).length ∧ (ddStep l v).length ≤ l.length + 1 := by
  unfold ddStep; split_ifs <;> simp

lemma ddJ_mem (x : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    ∀ (kk j : ℕ) (l : List (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d)),
      w ∈ ddJ x i j kk l ↔ w ∈ l ∨ ∃ j', j ≤ j' ∧ j' < j + kk ∧ w = x i - x j' := by
  intro kk
  induction kk with
  | zero => intro j l w; simp only [ddJ]; constructor; exact Or.inl; rintro (h | ⟨_, h1, h2, _⟩); exact h; omega
  | succ kk ih =>
    intro j l w
    simp only [ddJ]
    rw [ih, ddStep_mem]
    constructor
    · rintro ((h | h) | ⟨j', h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, le_rfl, by omega, h⟩
      · exact Or.inr ⟨j', by omega, by omega, h3⟩
    · rintro (h | ⟨j', h1, h2, h3⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.eq_or_lt_of_le h1 with e | e
        · subst e; exact Or.inl (Or.inr h3)
        · exact Or.inr ⟨j', by omega, by omega, h3⟩

lemma ddI_mem (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ∀ (kk i : ℕ) (l : List (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d)),
      w ∈ ddI x n i kk l ↔
        w ∈ l ∨ ∃ i' j', i ≤ i' ∧ i' < i + kk ∧ i' < j' ∧ j' < n ∧ w = x i' - x j' := by
  intro kk
  induction kk with
  | zero =>
    intro i l w; simp only [ddI]
    constructor; exact Or.inl; rintro (h | ⟨_, _, h1, h2, _⟩); exact h; omega
  | succ kk ih =>
    intro i l w
    simp only [ddI]
    rw [ih, ddJ_mem]
    constructor
    · rintro ((h | ⟨j', h1, h2, h3⟩) | ⟨i', j', h1, h2, h3, h4, h5⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, j', le_rfl, by omega, by omega, by omega, h3⟩
      · exact Or.inr ⟨i', j', by omega, by omega, h3, h4, h5⟩
    · rintro (h | ⟨i', j', h1, h2, h3, h4, h5⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.eq_or_lt_of_le h1 with e | e
        · subst e; exact Or.inl (Or.inr ⟨j', by omega, by omega, h5⟩)
        · exact Or.inr ⟨i', j', by omega, by omega, h3, h4, h5⟩

lemma ddJ_nodup (x : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    ∀ (kk j : ℕ) (l : List (EuclideanSpace ℝ (Fin d))), l.Nodup → (ddJ x i j kk l).Nodup := by
  intro kk
  induction kk with
  | zero => intro j l h; exact h
  | succ kk ih => intro j l h; exact ih _ _ (ddStep_nodup h _)

lemma ddI_nodup (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ∀ (kk i : ℕ) (l : List (EuclideanSpace ℝ (Fin d))), l.Nodup → (ddI x n i kk l).Nodup := by
  intro kk
  induction kk with
  | zero => intro i l h; exact h
  | succ kk ih => intro i l h; exact ih _ _ (ddJ_nodup x i _ _ _ h)

lemma ddJ_length (x : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    ∀ (kk j : ℕ) (l : List (EuclideanSpace ℝ (Fin d))),
      l.length ≤ (ddJ x i j kk l).length ∧ (ddJ x i j kk l).length ≤ l.length + kk := by
  intro kk
  induction kk with
  | zero => intro j l; simp [ddJ]
  | succ kk ih =>
    intro j l
    have h1 := ddStep_length_le l (x i - x j)
    have h2 := ih (j + 1) (ddStep l (x i - x j))
    simp only [ddJ]; omega

lemma ddI_length (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ∀ (kk i : ℕ) (l : List (EuclideanSpace ℝ (Fin d))),
      l.length ≤ (ddI x n i kk l).length ∧ (ddI x n i kk l).length ≤ l.length + kk * n := by
  intro kk
  induction kk with
  | zero => intro i l; simp [ddI]
  | succ kk ih =>
    intro i l
    have h1 := ddJ_length x i (n - (i + 1)) (i + 1) l
    have h2 := ih (i + 1) (ddJ x i (i + 1) (n - (i + 1)) l)
    simp only [ddI]
    have : n - (i + 1) ≤ n := Nat.sub_le _ _
    constructor
    · omega
    · have e : (kk + 1) * n = kk * n + n := by ring
      omega

lemma ddList_nodup (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : (ddList x n).Nodup :=
  ddI_nodup x n n 0 [] List.nodup_nil

lemma ddList_mem (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) (w : EuclideanSpace ℝ (Fin d)) :
    w ∈ ddList x n ↔ ∃ i j, i < j ∧ j < n ∧ w = x i - x j := by
  unfold ddList
  rw [ddI_mem]
  constructor
  · rintro (h | ⟨i, j, _, _, h3, h4, h5⟩)
    · simp at h
    · exact ⟨i, j, h3, h4, h5⟩
  · rintro ⟨i, j, h3, h4, h5⟩; exact Or.inr ⟨i, j, by omega, by omega, h3, h4, h5⟩

lemma ddList_length (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : (ddList x n).length ≤ n * n := by
  have := (ddI_length x n n 0 []).2; simpa [ddList] using this

/-- **The dedupe table as the set `𝒟` of `theorem_3_2_greedy`.** For injective `P`, the finset of the
table has no zero vector, contains `x - y` or `y - x` for all distinct points `x, y`, has as many
elements as the table has entries, and is nonempty when `n ≥ 2`. -/
theorem ddList_props {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin d)) (hP : Function.Injective P) :
    (∀ v ∈ (ddList (ptSeq P) n).toFinset, v ≠ 0) ∧
    (∀ y ∈ Finset.univ.image P, ∀ z ∈ Finset.univ.image P, y ≠ z →
      y - z ∈ (ddList (ptSeq P) n).toFinset ∨ z - y ∈ (ddList (ptSeq P) n).toFinset) ∧
    (ddList (ptSeq P) n).toFinset.card = (ddList (ptSeq P) n).length ∧
    (2 ≤ n → 1 ≤ (ddList (ptSeq P) n).toFinset.card) := by
  have hmem := ddList_mem (ptSeq P) n
  have pt : ∀ i (h : i < n), ptSeq P i = P ⟨i, h⟩ := fun i h => by simp [ptSeq, h]
  refine ⟨?_, ?_, List.toFinset_card_of_nodup (ddList_nodup _ n), ?_⟩
  · intro v hv
    rw [List.mem_toFinset, hmem] at hv
    obtain ⟨i, j, hij, hj, rfl⟩ := hv
    rw [pt i (by omega), pt j hj, sub_ne_zero]
    intro e; have := hP e; simp [Fin.ext_iff] at this; omega
  · intro y hy z hz hyz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy hz
    obtain ⟨a, rfl⟩ := hy; obtain ⟨b, rfl⟩ := hz
    simp only [List.mem_toFinset, hmem]
    have hab : (a : ℕ) ≠ b := fun e => hyz (by rw [Fin.ext e])
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · left; exact ⟨a, b, h, b.isLt, by rw [pt a a.isLt, pt b b.isLt]⟩
    · right; exact ⟨b, a, h, a.isLt, by rw [pt a a.isLt, pt b b.isLt]⟩
  · intro hn
    apply Finset.card_pos.2
    refine ⟨ptSeq P 0 - ptSeq P 1, ?_⟩
    rw [List.mem_toFinset, hmem]
    exact ⟨0, 1, by omega, by omega, rfl⟩

end DetANN.Supplement.Thm32

-- ===== T32_PreDedup =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

variable {d : ℕ}

lemma w_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (i j : ℕ)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (Dend : ℤ) (m0 : ℤ → ℝ)
    (hxi : ∀ c : Fin d, m0 ((1 + i * d + c : ℕ) : ℤ) = x i c)
    (hxj : ∀ c : Fin d, m0 ((1 + j * d + c : ℕ) : ℤ) = x j c)
    (hpi : ((1 + i * d + d : ℕ) : ℤ) ≤ Dend) (hpj : ((1 + j * d + d : ℕ) : ℤ) ≤ Dend) :
    ∀ (kk c : ℕ) (s : State), c + kk = d → s.core.pc = off + 78 → s.halted = false →
      s.core.ptrs 31 = c → s.core.ptrs 3 = d → s.core.ptrs 29 = ((1 + i * d : ℕ) : ℤ) →
      s.core.ptrs 30 = ((1 + j * d : ℕ) : ℤ) → s.core.ptrs 27 = Dend →
      (∀ c' : Fin d, (c' : ℕ) < c → s.core.mem (Dend + (c' : ℕ)) = (x i - x j) c') →
      (∀ z, (z < Dend ∨ Dend + c ≤ z) → s.core.mem z = m0 z) →
      ∃ t, t ≤ 10 * kk + 2 ∧ (run Q s detTape t).core.pc = off + 89 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 32 = s.core.ptrs 26 ∧
        (∀ y, y ≠ 11 → y ≠ 31 → y ≠ 32 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        (∀ c' : Fin d, (run Q s detTape t).core.mem (Dend + (c' : ℕ)) = (x i - x j) c') ∧
        (∀ z, (z < Dend ∨ Dend + d ≤ z) → (run Q s detTape t).core.mem z = m0 z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro c s hck hpc hh h31 h3 h29 h30 h27 hw hout
    have hc : c = d := by omega
    subst hc
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ := w_exit Q off q hE s hpc hh (by rw [h3, h31])
    exact ⟨2, by omega, g1, g2, g3, fun y _ _ y32 => g4 y y32, fun y _ _ => by rw [g5],
      fun c' => by rw [g6]; exact hw c' c'.isLt, fun z hz => by rw [g6]; exact hout z hz, g7, g8⟩
  | succ kk ih =>
    intro c s hck hpc hh h31 h3 h29 h30 h27 hw hout
    have hc : c < d := by omega
    have a0 : s.core.ptrs 29 + s.core.ptrs 31 = ((1 + i * d + c : ℕ) : ℤ) := by
      rw [h29, h31]; push_cast; ring
    have a1 : s.core.ptrs 30 + s.core.ptrs 31 = ((1 + j * d + c : ℕ) : ℤ) := by
      rw [h30, h31]; push_cast; ring
    have b0 : ((1 + i * d + c : ℕ) : ℤ) < Dend := by
      have : ((1 + i * d + c : ℕ) : ℤ) < ((1 + i * d + d : ℕ) : ℤ) := by exact_mod_cast (by omega)
      omega
    have b1 : ((1 + j * d + c : ℕ) : ℤ) < Dend := by
      have : ((1 + j * d + c : ℕ) : ℤ) < ((1 + j * d + d : ℕ) : ℤ) := by exact_mod_cast (by omega)
      omega
    have e0 : s.core.mem (s.core.ptrs 29 + s.core.ptrs 31) = x i ⟨c, hc⟩ := by
      rw [a0, hout _ (Or.inl b0)]; exact hxi ⟨c, hc⟩
    have e1 : s.core.mem (s.core.ptrs 30 + s.core.ptrs 31) = x j ⟨c, hc⟩ := by
      rw [a1, hout _ (Or.inl b1)]; exact hxj ⟨c, hc⟩
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
      w_step Q off q hE _ _ s hpc hh e0 e1 (by rw [h31, h3]; exact_mod_cast hc)
    set s1 := run Q s detTape 10 with hs1
    rw [h27, h31] at g9 g10
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih (c + 1) s1 (by omega) g1 g2 (by rw [g4, h31]; push_cast; ring)
        (by rw [g5 3 (by decide) (by decide), h3]) (by rw [g5 29 (by decide) (by decide), h29])
        (by rw [g5 30 (by decide) (by decide), h30]) (by rw [g5 27 (by decide) (by decide), h27])
        (by
          intro c' hc'
          rcases Nat.lt_or_ge (c' : ℕ) c with h | h
          · rw [g10 _ (by intro e; have := add_left_cancel e; omega)]; exact hw c' h
          · have e : c' = ⟨c, hc⟩ := Fin.ext (show (c' : ℕ) = c by omega)
            subst e; rw [g9]; simp)
        (by
          intro z hz
          rw [g10 z (by intro e; subst e; rcases hz with hz | hz <;> push_cast at hz <;> omega)]
          exact hout z (by rcases hz with hz | hz
                           · left; exact hz
                           · right; push_cast at hz; omega))
    refine ⟨10 + t2, by omega, ?_⟩
    rw [run_add, ← hs1]
    exact ⟨q1, q2, by rw [q3, g5 26 (by decide) (by decide)],
      fun y a b e => by rw [q4 y a b e, g5 y a b], fun y a b => by rw [q5 y a b, g8 y a b], q6, q7,
      by rw [q8, g11], by rw [q9, g12]; ring⟩

lemma c_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off)
    (e Dend : ℤ) (u w : EuclideanSpace ℝ (Fin d)) :
    ∀ (kk c : ℕ) (s : State), c + kk = d → s.core.pc = off + 91 → s.halted = false →
      s.core.ptrs 31 = c → s.core.ptrs 3 = d → s.core.ptrs 32 = e → s.core.ptrs 27 = Dend →
      (∀ c' : Fin d, s.core.mem (e + (c' : ℕ)) = u c') →
      (∀ c' : Fin d, s.core.mem (Dend + (c' : ℕ)) = w c') →
      (∀ c' : Fin d, (c' : ℕ) < c → u c' = w c') →
      ∃ t, t ≤ 12 * kk + 4 ∧ (run Q s detTape t).halted = false ∧
        ((u = w ∧ (run Q s detTape t).core.pc = off + 76 ∧
            (run Q s detTape t).core.ptrs 20 = s.core.ptrs 20 + 1 ∧
            (run Q s detTape t).core.ptrs 30 = s.core.ptrs 30 + d ∧
            (run Q s detTape t).core.ptrs 32 = e) ∨
          (u ≠ w ∧ (run Q s detTape t).core.pc = off + 89 ∧
            (run Q s detTape t).core.ptrs 20 = s.core.ptrs 20 ∧
            (run Q s detTape t).core.ptrs 30 = s.core.ptrs 30 ∧
            (run Q s detTape t).core.ptrs 32 = e + d)) ∧
        (∀ y, y ≠ 11 → y ≠ 20 → y ≠ 30 → y ≠ 31 → y ≠ 32 →
          (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro c s hck hpc hh h31 h3 h32 h27 hu hw heq
    have hc : c = d := by omega
    subst hc
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ := c_dup Q off q hE s hpc hh (by rw [h3, h31])
    have huw : u = w := by
      ext c'; exact heq c' c'.isLt
    exact ⟨4, by omega, g2, Or.inl ⟨huw, g1, g3, by rw [g4, h3], by rw [g5 32 (by decide) (by decide), h32]⟩,
      fun y _ a _ _ _ => g5 y a (by assumption), fun y _ _ _ => by rw [g6], g7, g8, g9⟩
  | succ kk ih =>
    intro c s hck hpc hh h31 h3 h32 h27 hu hw heq
    have hc : c < d := by omega
    have ea : s.core.mem (s.core.ptrs 32 + s.core.ptrs 31) = u ⟨c, hc⟩ := by
      rw [h32, h31]; exact hu ⟨c, hc⟩
    have eb : s.core.mem (s.core.ptrs 27 + s.core.ptrs 31) = w ⟨c, hc⟩ := by
      rw [h27, h31]; exact hw ⟨c, hc⟩
    have hcd : s.core.ptrs 31 < s.core.ptrs 3 := by rw [h31, h3]; exact_mod_cast hc
    by_cases d1 : u ⟨c, hc⟩ - w ⟨c, hc⟩ ≤ 0
    · by_cases d2 : w ⟨c, hc⟩ - u ⟨c, hc⟩ ≤ 0
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
          c_eq Q off q hE _ _ s hpc hh ea eb hcd d1 d2
        set s1 := run Q s detTape 11 with hs1
        obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7⟩ :=
          ih (c + 1) s1 (by omega) g1 g2 (by rw [g4, h31]; push_cast; ring)
            (by rw [g5 3 (by decide) (by decide), h3]) (by rw [g5 32 (by decide) (by decide), h32])
            (by rw [g5 27 (by decide) (by decide), h27]) (fun c' => by rw [g10]; exact hu c')
            (fun c' => by rw [g10]; exact hw c')
            (by
              intro c' hc'
              rcases Nat.lt_or_ge (c' : ℕ) c with h | h
              · exact heq c' h
              · have e : c' = ⟨c, hc⟩ := Fin.ext (show (c' : ℕ) = c by omega)
                subst e; linarith)
        refine ⟨11 + t2, by omega, ?_⟩
        rw [run_add, ← hs1]
        refine ⟨q1, ?_, fun y a b c' e f => by rw [q3 y a b c' e f, g5 y a e],
          fun y a b c' => by rw [q4 y a b c', g9 y a b c'], by rw [q5, g10], by rw [q6, g11],
          by rw [q7, g12]; ring⟩
        rcases q2 with ⟨r1, r2, r3, r4, r5⟩ | ⟨r1, r2, r3, r4, r5⟩
        · exact Or.inl ⟨r1, r2, by rw [r3, g5 20 (by decide) (by decide)],
            by rw [r4, g5 30 (by decide) (by decide)], r5⟩
        · exact Or.inr ⟨r1, r2, by rw [r3, g5 20 (by decide) (by decide)],
            by rw [r4, g5 30 (by decide) (by decide)], r5⟩
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
          c_mis2 Q off q hE _ _ s hpc hh ea eb hcd d1 d2
        have hne : u ≠ w := fun e => by rw [e] at d2; simp at d2
        exact ⟨12, by omega, g2, Or.inr ⟨hne, g1, by rw [g5 20 (by decide) (by decide)],
          by rw [g5 30 (by decide) (by decide)], by rw [g4, h32, h3]⟩,
          fun y a _ _ _ b => g5 y a b, fun y a b c' => g9 y a b c', g10, g11, g12⟩
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
        c_mis1 Q off q hE _ _ s hpc hh ea eb hcd d1
      have hne : u ≠ w := fun e => by rw [e] at d1; simp at d1
      exact ⟨10, by omega, g2, Or.inr ⟨hne, g1, by rw [g5 20 (by decide) (by decide)],
        by rw [g5 30 (by decide) (by decide)], by rw [g4, h32, h3]⟩,
        fun y a _ _ _ b => g5 y a b, fun y a b c' => g9 y a b c', g10, g11, g12⟩

lemma table_step {mem : ℤ → ℝ} {Db Dend : ℤ} {l : List (EuclideanSpace ℝ (Fin d))}
    {w : EuclideanSpace ℝ (Fin d)} (hT : TableAt mem Db l) (hD : Dend = Db + ((l.length * d : ℕ) : ℤ))
    (hw : ∀ c : Fin d, mem (Dend + (c : ℕ)) = w c) : TableAt mem Db (ddStep l w) := by
  unfold ddStep
  split_ifs with h
  · exact hT
  · intro m v hv c
    rcases Nat.lt_or_ge m l.length with hm | hm
    · rw [List.getElem?_append_left hm] at hv; exact hT m v hv c
    · rw [List.getElem?_append_right hm] at hv
      have e : m - l.length = 0 := by
        by_contra hne
        have : (m - l.length) ≥ 1 := Nat.one_le_iff_ne_zero.2 hne
        rw [List.getElem?_eq_none (by simp; omega)] at hv; exact absurd hv (by simp)
      rw [e] at hv
      simp at hv; subst hv
      have hm' : m = l.length := by omega
      rw [hm', ← hw c, hD]; push_cast; ring_nf

lemma e_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (Db : ℤ) (l : List (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d)) :
    ∀ (kk m : ℕ) (s : State), m + kk = l.length → s.core.pc = off + 89 → s.halted = false →
      s.core.ptrs 32 = Db + ((m * d : ℕ) : ℤ) → s.core.ptrs 3 = d →
      s.core.ptrs 27 = Db + ((l.length * d : ℕ) : ℤ) → s.core.ptrs 28 = l.length →
      TableAt s.core.mem Db l →
      (∀ c : Fin d, s.core.mem (Db + ((l.length * d : ℕ) : ℤ) + (c : ℕ)) = w c) →
      (∀ m' : ℕ, m' < m → l[m']? ≠ some w) →
      ∃ t, t ≤ kk * (12 * d + 8) + 6 ∧ (run Q s detTape t).core.pc = off + 76 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 20 = s.core.ptrs 20 + 1 ∧
        (run Q s detTape t).core.ptrs 30 = s.core.ptrs 30 + d ∧
        (run Q s detTape t).core.ptrs 27 = Db + (((ddStep l w).length * d : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 28 = (ddStep l w).length ∧
        (∀ y, y ≠ 11 → y ≠ 20 → y ≠ 27 → y ≠ 28 → y ≠ 30 → y ≠ 31 → y ≠ 32 →
          (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro m s hmk hpc hh h32 h3 h27 h28 hT hw hne
    have hm : m = l.length := by omega
    subst hm
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, _⟩ :=
      e_new Q off q hE s hpc hh (by rw [h27, h32])
    have hnot : w ∉ l := by
      intro hw'
      obtain ⟨m', hm', e⟩ := List.getElem_of_mem hw'
      exact hne m' hm' (by rw [List.getElem?_eq_getElem hm', e])
    have hstep : ddStep l w = l ++ [w] := by simp [ddStep, hnot]
    refine ⟨6, by omega, g1, g2, g3, by rw [g6, h3], ?_, ?_, fun y a b c e f _ _ => g7 y b c e f,
      fun y _ _ _ => by rw [g8], g9, g10, g11⟩
    · rw [g4, h27, h3, hstep]; push_cast; simp; ring
    · rw [g5, h28, hstep]; push_cast; simp
  | succ kk ih =>
    intro m s hmk hpc hh h32 h3 h27 h28 hT hw hne
    have hm : m < l.length := by omega
    have hlt : s.core.ptrs 32 < s.core.ptrs 27 := by
      rw [h32, h27]
      have : m * d < l.length * d := Nat.mul_lt_mul_of_pos_right hm (by omega)
      have h' : ((m * d : ℕ) : ℤ) < ((l.length * d : ℕ) : ℤ) := by exact_mod_cast this
      omega
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ := e_head Q off q hE s hpc hh hlt
    set s1 := run Q s detTape 2 with hs1
    set u := l[m]'hm with hu
    obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7⟩ :=
      c_loop Q off q hE (Db + ((m * d : ℕ) : ℤ)) (Db + ((l.length * d : ℕ) : ℤ)) u w d 0 s1 (by omega)
        g1 g2 g3 (by rw [g4 3 (by decide), h3]) (by rw [g4 32 (by decide), h32])
        (by rw [g4 27 (by decide), h27])
        (fun c' => by
          rw [g6, show Db + ((m * d : ℕ) : ℤ) + ((c' : ℕ) : ℤ) = Db + ((m * d + c' : ℕ) : ℤ) by
            push_cast; ring]
          exact hT m u (List.getElem?_eq_getElem hm) c')
        (fun c' => by rw [g6]; exact hw c') (fun c' h => absurd h (Nat.not_lt_zero _))
    set s2 := run Q s1 detTape t2 with hs2
    rcases p2 with ⟨r1, r2, r3, r4, r5⟩ | ⟨r1, r2, r3, r4, r5⟩
    · -- found
      have hin : w ∈ l := by rw [← r1]; exact List.getElem_mem hm
      have hstep : ddStep l w = l := by simp [ddStep, hin]
      refine ⟨2 + t2, by
          have : (kk + 1) * (12 * d + 8) = kk * (12 * d + 8) + 12 * d + 8 := by ring
          omega, ?_⟩
      rw [run_add, ← hs1]
      refine ⟨r2, p1, by rw [r3, g4 20 (by decide)], by rw [r4, g4 30 (by decide)], ?_, ?_,
        fun y a b c e f g' h => by rw [p3 y a b f g' h, g4 y g'], fun y a b c => by rw [p4 y a b c, g5],
        by rw [p5, g6], by rw [p6, g7], by rw [p7, g8]; ring⟩
      · rw [hstep, p3 27 (by decide) (by decide) (by decide) (by decide) (by decide), g4 27 (by decide), h27]
      · rw [hstep, p3 28 (by decide) (by decide) (by decide) (by decide) (by decide), g4 28 (by decide), h28]
    · -- not this one: next
      obtain ⟨T3, hT3, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
        ih (m + 1) s2 (by omega) r2 p1 (by rw [r5]; push_cast; ring)
          (by rw [p3 3 (by decide) (by decide) (by decide) (by decide) (by decide), g4 3 (by decide), h3])
          (by rw [p3 27 (by decide) (by decide) (by decide) (by decide) (by decide), g4 27 (by decide), h27])
          (by rw [p3 28 (by decide) (by decide) (by decide) (by decide) (by decide), g4 28 (by decide), h28])
          (by rw [p5, g6]; exact hT) (fun c => by rw [p5, g6]; exact hw c)
          (by
            intro m' hm'
            rcases Nat.lt_or_ge m' m with h | h
            · exact hne m' h
            · have : m' = m := by omega
              subst this
              rw [List.getElem?_eq_getElem hm]
              intro e; exact r1 (Option.some_injective _ e))
      refine ⟨2 + t2 + T3, by
          have : (kk + 1) * (12 * d + 8) = kk * (12 * d + 8) + 12 * d + 8 := by ring
          omega, ?_⟩
      have e2 : run Q s detTape (2 + t2) = s2 := by rw [run_add, ← hs1]
      rw [run_add, e2]
      refine ⟨q1, q2, by rw [q3, r3, g4 20 (by decide)], by rw [q4, r4, g4 30 (by decide)], q5, q6,
        fun y a b c e f g' h => by rw [q7 y a b c e f g' h, p3 y a b f g' h, g4 y g'],
        fun y a b c => by rw [q8 y a b c, p4 y a b c, g5], by rw [q9, p5, g6], by rw [q10, p6, g7],
        by rw [q11, p7, g8]; ring⟩

lemma pair_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (n i j Lm : ℕ) (hi : i < n) (hj : j < n) (x : ℕ → EuclideanSpace ℝ (Fin d)) (m0 : ℤ → ℝ)
    (hx : ∀ i' : ℕ, i' < n → ∀ c : Fin d, m0 ((1 + i' * d + c : ℕ) : ℤ) = x i' c)
    (Db : ℤ) (hDb : ((1 + n * d : ℕ) : ℤ) ≤ Db) (l : List (EuclideanSpace ℝ (Fin d)))
    (hLm : l.length ≤ Lm) (s : State) (hpc : s.core.pc = off + 76) (hh : s.halted = false)
    (h20 : s.core.ptrs 20 = j) (h22 : s.core.ptrs 22 = n) (h3 : s.core.ptrs 3 = d)
    (h29 : s.core.ptrs 29 = ((1 + i * d : ℕ) : ℤ)) (h30 : s.core.ptrs 30 = ((1 + j * d : ℕ) : ℤ))
    (h26 : s.core.ptrs 26 = Db) (h27 : s.core.ptrs 27 = Db + ((l.length * d : ℕ) : ℤ))
    (h28 : s.core.ptrs 28 = l.length) (hT : TableAt s.core.mem Db l)
    (hm0 : ∀ z, z < Db → s.core.mem z = m0 z) :
    ∃ t, t ≤ pairB d Lm ∧ (run Q s detTape t).core.pc = off + 76 ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 20 = j + 1 ∧
      (run Q s detTape t).core.ptrs 30 = ((1 + (j + 1) * d : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 27 = Db + (((ddStep l (x i - x j)).length * d : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 28 = (ddStep l (x i - x j)).length ∧
      (∀ y, y ≠ 11 → y ≠ 20 → y ≠ 27 → y ≠ 28 → y ≠ 30 → y ≠ 31 → y ≠ 32 →
        (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
      TableAt (run Q s detTape t).core.mem Db (ddStep l (x i - x j)) ∧
      (∀ z, z < Db → (run Q s detTape t).core.mem z = m0 z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t := by
  set Dend : ℤ := Db + ((l.length * d : ℕ) : ℤ) with hDend
  have hDD : Db ≤ Dend := by
    have : (0 : ℤ) ≤ ((l.length * d : ℕ) : ℤ) := by positivity
    simp only [hDend]; omega
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ :=
    dj_head Q off q hE s hpc hh (by rw [h20, h22]; exact_mod_cast hj)
  set s1 := run Q s detTape 2 with hs1
  have hleDb : ∀ i' : ℕ, i' < n → ((1 + i' * d + d : ℕ) : ℤ) ≤ Db := by
    intro i' hi'
    have : 1 + i' * d + d ≤ 1 + n * d := by
      have := Nat.mul_le_mul_right d (show i' + 1 ≤ n by omega); nlinarith
    have : ((1 + i' * d + d : ℕ) : ℤ) ≤ ((1 + n * d : ℕ) : ℤ) := by exact_mod_cast this
    omega
  have hle : ∀ i' : ℕ, i' < n → ((1 + i' * d + d : ℕ) : ℤ) ≤ Dend :=
    fun i' hi' => le_trans (hleDb i' hi') hDD
  have hpt : ∀ i' : ℕ, i' < n → ∀ c : Fin d, s1.core.mem ((1 + i' * d + c : ℕ) : ℤ) = x i' c := by
    intro i' hi' c
    rw [g6, hm0 _ (by
      have := hleDb i' hi'
      have : ((1 + i' * d + (c : ℕ) : ℕ) : ℤ) < ((1 + i' * d + d : ℕ) : ℤ) := by exact_mod_cast (by omega)
      omega)]
    exact hx i' hi' c
  obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ :=
    w_loop Q off q hE i j x Dend s1.core.mem (hpt i hi) (hpt j hj) (hle i hi) (hle j hj) d 0 s1
      (by omega) g1 g2 g3 (by rw [g4 3 (by decide), h3]) (by rw [g4 29 (by decide), h29])
      (by rw [g4 30 (by decide), h30]) (by rw [g4 27 (by decide), h27])
      (fun c' h => absurd h (Nat.not_lt_zero _)) (fun z _ => rfl)
  set s2 := run Q s1 detTape t2 with hs2
  have f2 : ∀ y, y ≠ 11 → y ≠ 31 → y ≠ 32 → s2.core.ptrs y = s.core.ptrs y :=
    fun y a b c => by rw [p4 y a b c, g4 y b]
  have hT2 : TableAt s2.core.mem Db l := by
    intro m v hv c
    have hm : m < l.length := by
      by_contra h; push Not at h; rw [List.getElem?_eq_none h] at hv; exact absurd hv (by simp)
    have : m * d + (c : ℕ) < l.length * d := by
      have := c.isLt
      calc m * d + (c : ℕ) < m * d + d := by omega
        _ = (m + 1) * d := by ring
        _ ≤ l.length * d := Nat.mul_le_mul_right _ hm
    have h' : ((m * d + (c : ℕ) : ℕ) : ℤ) < ((l.length * d : ℕ) : ℤ) := by exact_mod_cast this
    rw [p7 _ (Or.inl (by simp only [hDend]; omega)), g6]
    exact hT m v hv c
  obtain ⟨T3, hT3, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
    e_loop Q off q hE hd1 Db l (x i - x j) l.length 0 s2 (by omega) p1 p2
      (by rw [p3, g4 26 (by decide), h26]; simp)
      (by rw [f2 3 (by decide) (by decide) (by decide), h3])
      (by rw [f2 27 (by decide) (by decide) (by decide), h27])
      (by rw [f2 28 (by decide) (by decide) (by decide), h28]) hT2 (fun c => p6 c)
      (fun m' h => absurd h (Nat.not_lt_zero _))
  set s3 := run Q s2 detTape T3 with hs3
  refine ⟨2 + t2 + T3, ?_, ?_⟩
  · unfold pairB
    have : l.length * (12 * d + 8) ≤ Lm * (12 * d + 8) := Nat.mul_le_mul_right _ hLm
    omega
  have e3 : run Q s detTape (2 + t2 + T3) = s3 := by
    rw [run_add, run_add, ← hs1, ← hs2, ← hs3]
  rw [e3]
  refine ⟨q1, q2, by rw [q3, f2 20 (by decide) (by decide) (by decide), h20],
    by rw [q4, f2 30 (by decide) (by decide) (by decide), h30]; push_cast; ring, q5, q6,
    fun y a b c e f g' h => by rw [q7 y a b c e f g' h, f2 y a g' h],
    fun y a b c => by rw [q8 y a b c, p5 y a b, g5], ?_, ?_, by rw [q10, p8, g7],
    by rw [q11, p9, g8]; ring⟩
  · rw [q9]; exact table_step hT2 rfl (fun c => p6 c)
  · intro z hz
    rw [q9, p7 z (Or.inl (by omega)), g6]; exact hm0 z hz

lemma dj_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (n i Lm : ℕ) (hi : i < n) (x : ℕ → EuclideanSpace ℝ (Fin d)) (m0 : ℤ → ℝ)
    (hx : ∀ i' : ℕ, i' < n → ∀ c : Fin d, m0 ((1 + i' * d + c : ℕ) : ℤ) = x i' c)
    (Db : ℤ) (hDb : ((1 + n * d : ℕ) : ℤ) ≤ Db) :
    ∀ (kk j : ℕ) (l : List (EuclideanSpace ℝ (Fin d))) (s : State), j + kk = n →
      (ddJ x i j kk l).length ≤ Lm → s.core.pc = off + 76 → s.halted = false →
      s.core.ptrs 20 = j → s.core.ptrs 22 = n → s.core.ptrs 3 = d → s.core.ptrs 10 = i →
      s.core.ptrs 29 = ((1 + i * d : ℕ) : ℤ) → s.core.ptrs 30 = ((1 + j * d : ℕ) : ℤ) →
      s.core.ptrs 26 = Db → s.core.ptrs 27 = Db + ((l.length * d : ℕ) : ℤ) →
      s.core.ptrs 28 = l.length → TableAt s.core.mem Db l → (∀ z, z < Db → s.core.mem z = m0 z) →
      ∃ t, t ≤ kk * pairB d Lm + 4 ∧ (run Q s detTape t).core.pc = off + 72 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 10 = i + 1 ∧
        (run Q s detTape t).core.ptrs 29 = ((1 + (i + 1) * d : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 27 = Db + (((ddJ x i j kk l).length * d : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 28 = (ddJ x i j kk l).length ∧
        (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 27 → y ≠ 28 → y ≠ 29 → y ≠ 30 → y ≠ 31 → y ≠ 32 →
          (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        TableAt (run Q s detTape t).core.mem Db (ddJ x i j kk l) ∧
        (∀ z, z < Db → (run Q s detTape t).core.mem z = m0 z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro j l s hjk hL hpc hh h20 h22 h3 h10 h29 h30 h26 h27 h28 hT hm0
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
      dj_exit Q off q hE s hpc hh (by rw [h22, h20]; exact_mod_cast (by omega : n ≤ j))
    refine ⟨4, by omega, g1, g2, by rw [g3, h10], by rw [g4, h29, h3]; push_cast; ring,
      by rw [g5 27 (by decide) (by decide), h27]; rfl, by rw [g5 28 (by decide) (by decide), h28]; rfl,
      fun y a _ _ _ _ b _ _ _ => g5 y a b, fun y _ _ _ => by rw [g6], by rw [g7]; exact hT,
      fun z hz => by rw [g7]; exact hm0 z hz, g8, g9⟩
  | succ kk ih =>
    intro j l s hjk hL hpc hh h20 h22 h3 h10 h29 h30 h26 h27 h28 hT hm0
    have hj : j < n := by omega
    have hl1 : l.length ≤ Lm := by
      have a := (ddJ_length x i kk (j + 1) (ddStep l (x i - x j))).1
      have b := (ddStep_length_le l (x i - x j)).1
      simp only [ddJ] at hL; omega
    obtain ⟨t1, ht1, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ :=
      pair_step Q off q hE hd1 n i j Lm hi hj x m0 hx Db hDb l hl1 s hpc hh h20 h22 h3 h29 h30 h26 h27
        h28 hT hm0
    set s1 := run Q s detTape t1 with hs1
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
      ih (j + 1) (ddStep l (x i - x j)) s1 (by omega) (by simp only [ddJ] at hL; exact hL) p1 p2 p3
        (by rw [p7 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h22])
        (by rw [p7 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h3])
        (by rw [p7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h10])
        (by rw [p7 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h29]) p4
        (by rw [p7 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h26]) p5 p6 p9 p10
    refine ⟨t1 + t2, by
        have : (kk + 1) * pairB d Lm = kk * pairB d Lm + pairB d Lm := by ring
        omega, ?_⟩
    rw [run_add, ← hs1]
    exact ⟨q1, q2, q3, q4, q5, q6, fun y a b c e f g' h i' j' => by
        rw [q7 y a b c e f g' h i' j', p7 y b c e f h i' j'],
      fun y a b c => by rw [q8 y a b c, p8 y a b c], q9, q10, by rw [q11, p11],
      by rw [q12, p12]; ring⟩

lemma di_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (n Lm : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (m0 : ℤ → ℝ)
    (hx : ∀ i' : ℕ, i' < n → ∀ c : Fin d, m0 ((1 + i' * d + c : ℕ) : ℤ) = x i' c)
    (Db : ℤ) (hDb : ((1 + n * d : ℕ) : ℤ) ≤ Db) :
    ∀ (kk i : ℕ) (l : List (EuclideanSpace ℝ (Fin d))) (s : State), i + kk = n →
      (ddI x n i kk l).length ≤ Lm → s.core.pc = off + 72 → s.halted = false →
      s.core.ptrs 10 = i → s.core.ptrs 22 = n → s.core.ptrs 3 = d →
      s.core.ptrs 29 = ((1 + i * d : ℕ) : ℤ) →
      s.core.ptrs 26 = Db → s.core.ptrs 27 = Db + ((l.length * d : ℕ) : ℤ) →
      s.core.ptrs 28 = l.length → TableAt s.core.mem Db l → (∀ z, z < Db → s.core.mem z = m0 z) →
      ∃ t, t ≤ kk * (n * pairB d Lm + 8) + 2 ∧ (run Q s detTape t).core.pc = off + 115 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 23 = Db + (((ddI x n i kk l).length * d : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 28 = (ddI x n i kk l).length ∧
        (run Q s detTape t).core.ptrs 26 = Db ∧
        (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 23 → y ≠ 27 → y ≠ 28 → y ≠ 29 → y ≠ 30 → y ≠ 31 →
          y ≠ 32 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        TableAt (run Q s detTape t).core.mem Db (ddI x n i kk l) ∧
        (∀ z, z < Db → (run Q s detTape t).core.mem z = m0 z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        (run Q s detTape t).core.ptrs 27 = Db + (((ddI x n i kk l).length * d : ℕ) : ℤ) := by
  intro kk
  induction kk with
  | zero =>
    intro i l s hik hL hpc hh h10 h22 h3 h29 h26 h27 h28 hT hm0
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ :=
      di_exit Q off q hE s hpc hh (by rw [h22, h10]; exact_mod_cast (by omega : n ≤ i))
    refine ⟨2, by omega, g1, g2, by rw [g3, h27]; rfl, by rw [g4 28 (by decide), h28]; rfl,
      by rw [g4 26 (by decide), h26], fun y _ _ _ a _ _ _ _ _ _ => g4 y a, fun y _ _ _ => by rw [g5],
      by rw [g6]; exact hT, fun z hz => by rw [g6]; exact hm0 z hz, g7, g8,
      by rw [g4 27 (by decide), h27]; rfl⟩
  | succ kk ih =>
    intro i l s hik hL hpc hh h10 h22 h3 h29 h26 h27 h28 hT hm0
    have hi : i < n := by omega
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
      di_head Q off q hE s hpc hh (by rw [h10, h22]; exact_mod_cast hi)
    set s1 := run Q s detTape 4 with hs1
    have hLJ : (ddJ x i (i + 1) (n - (i + 1)) l).length ≤ Lm := by
      have := (ddI_length x n kk (i + 1) (ddJ x i (i + 1) (n - (i + 1)) l)).1
      simp only [ddI] at hL; omega
    obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ :=
      dj_loop Q off q hE hd1 n i Lm hi x m0 hx Db hDb (n - (i + 1)) (i + 1) l s1 (by omega) hLJ g1 g2
        (by rw [g3, h10]; push_cast; ring) (by rw [g5 22 (by decide) (by decide), h22])
        (by rw [g5 3 (by decide) (by decide), h3]) (by rw [g5 10 (by decide) (by decide), h10])
        (by rw [g5 29 (by decide) (by decide), h29])
        (by rw [g4, h29, h3]; push_cast; ring) (by rw [g5 26 (by decide) (by decide), h26])
        (by rw [g5 27 (by decide) (by decide), h27]) (by rw [g5 28 (by decide) (by decide), h28])
        (by rw [g7]; exact hT) (fun z hz => by rw [g7]; exact hm0 z hz)
    set s2 := run Q s1 detTape t2 with hs2
    have f2 : ∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 27 → y ≠ 28 → y ≠ 29 → y ≠ 30 → y ≠ 31 → y ≠ 32 →
        s2.core.ptrs y = s.core.ptrs y :=
      fun y a b c e f g' h i' j' => by rw [p7 y a b c e f g' h i' j', g5 y c h]
    obtain ⟨T3, hT3, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
      ih (i + 1) (ddJ x i (i + 1) (n - (i + 1)) l) s2 (by omega) (by simp only [ddI] at hL; exact hL)
        p1 p2 p3
        (by rw [f2 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), h22])
        (by rw [f2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), h3]) p4
        (by rw [f2 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), h26]) p5 p6 p9 p10
    refine ⟨4 + t2 + T3, by
        have h1 : (n - (i + 1)) * pairB d Lm ≤ n * pairB d Lm := Nat.mul_le_mul_right _ (by omega)
        have h2 : (kk + 1) * (n * pairB d Lm + 8) = kk * (n * pairB d Lm + 8) + n * pairB d Lm + 8 := by
          ring
        omega, ?_⟩
    have e2 : run Q s detTape (4 + t2) = s2 := by rw [run_add, ← hs1]
    rw [run_add, e2]
    exact ⟨q1, q2, q3, q4, q5, fun y a b c e f g' h i' j' l' => by
        rw [q6 y a b c e f g' h i' j' l', f2 y a b c f g' h i' j' l'],
      fun y a b c => by rw [q7 y a b c, p8 y a b c, g6], q8, q9, by rw [q10, p11, g8],
      by rw [q11, p12, g9]; ring, q12⟩

/-- **The dedupe.** From `off + 67` with `top = Db ≥ 1 + n·d` and the points `x i` at
`1 + i·d`, `pre` reaches `off + 115` with the table of `ddList x n` at `Db`, `Dc = |ddList x n|`
in pointer `28` and `top = Db + |ddList x n|·d`. -/
lemma pre_dedup (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (Db : ℤ) (hDb : ((1 + n * d : ℕ) : ℤ) ≤ Db)
    (s : State) (hpc : s.core.pc = off + 67) (hh : s.halted = false)
    (h22 : s.core.ptrs 22 = n) (h3 : s.core.ptrs 3 = d) (h23 : s.core.ptrs 23 = Db)
    (hx : ∀ i' : ℕ, i' < n → ∀ c : Fin d, s.core.mem ((1 + i' * d + c : ℕ) : ℤ) = x i' c) :
    ∃ t, t ≤ n * (n * pairB d (n * n) + 8) + 7 ∧ (run Q s detTape t).core.pc = off + 115 ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 23 = Db + (((ddList x n).length * d : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 28 = (ddList x n).length ∧
      (run Q s detTape t).core.ptrs 26 = Db ∧
      (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 23 → y ≠ 26 → y ≠ 27 → y ≠ 28 → y ≠ 29 → y ≠ 30 →
        y ≠ 31 → y ≠ 32 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
      TableAt (run Q s detTape t).core.mem Db (ddList x n) ∧
      (∀ z, z < Db → (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t ∧
      (run Q s detTape t).core.ptrs 27 = Db + (((ddList x n).length * d : ℕ) : ℤ) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ := dd_init Q off q hE s hpc hh
  set s1 := run Q s detTape 5 with hs1
  have hx' : ∀ i' : ℕ, i' < n → ∀ c : Fin d, s.core.mem ((1 + i' * d + c : ℕ) : ℤ) = x i' c := hx
  obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ :=
    di_loop Q off q hE hd1 n (n * n) x s.core.mem hx' Db hDb n 0 [] s1 (by omega)
      (ddList_length x n) g1 g2 g3
      (by rw [g8 22 (by decide) (by decide) (by decide) (by decide) (by decide), h22])
      (by rw [g8 3 (by decide) (by decide) (by decide) (by decide) (by decide), h3])
      (by rw [g7]; simp) (by rw [g4, h23]) (by rw [g5, h23]; simp) (by rw [g6]; simp)
      (fun m v hv => by simp at hv) (fun z _ => by rw [g10])
  refine ⟨5 + t2, by omega, ?_⟩
  rw [run_add, ← hs1]
  exact ⟨p1, p2, p3, p4, p5, fun y a b c e f g' h i' j' l' m' => by
      rw [p6 y a b c e g' h i' j' l' m', g8 y a f g' h i'],
    fun y a b c => by rw [p7 y a b c, g9], p8, fun z hz => by rw [p9 z hz], by rw [p10, g11],
    by rw [p11, g12]; ring, p12⟩

end DetANN.Supplement.Thm32

-- ===== T32_Assembly =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

lemma flat_getD' (m : ℕ) : ∀ (N : ℕ) (Y : Fin N → Fin m → ℝ) (g : ℕ) (hg : g < N) (j : ℕ) (hj : j < m),
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
      have := ih (fun i => Y i.succ) g (by omega) j hj
      rw [show (g + 1) * m + j - m = g * m + j by rw [Nat.add_mul]; omega, this]
      rfl

section Input

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

lemma inp_im0 : (inputState Y δ).integerMemory 0 = N := by
  simp [inputState, PNormReg.initState]

lemma inp_im1 : (inputState Y δ).integerMemory 1 = m := by
  simp [inputState, PNormReg.initState]

lemma inp_mem0 : (inputState Y δ).core.mem 0 = δ := by
  simp [inputState, PNormReg.initState]

lemma inp_pts (g : Fin N) (j : Fin m) :
    (inputState Y δ).core.mem (1 + (g : ℤ) * m + j) = Y g j := by
  have hz : (1 + (g : ℤ) * m + j) = ((g * m + j + 1 : ℕ) : ℤ) := by push_cast; ring
  simp only [inputState, PNormReg.initState]
  rw [if_pos (by positivity), hz, Int.toNat_natCast, List.getD_cons_succ]
  exact flat_getD' m N (fun i j => Y i j) g g.isLt j j.isLt

lemma inp_pc : (inputState Y δ).core.pc = 0 := rfl

lemma inp_halted : (inputState Y δ).halted = false := rfl

lemma inp_ptrs : (inputState Y δ).core.ptrs = fun _ => 0 := rfl

lemma inp_work : (inputState Y δ).work = 0 := rfl

end Input

lemma idx_lt {r j D : ℕ} (hr : r < D) (hj : j < D) : r * D + j < D * D := by
  have : (r + 1) * D ≤ D * D := Nat.mul_le_mul_right _ hr
  nlinarith

lemma idx_lt2 {m c D M : ℕ} (hm : m < M) (hc : c < D) : m * D + c < M * D :=
  calc m * D + c < m * D + D := by omega
    _ = (m + 1) * D := by ring
    _ ≤ M * D := Nat.mul_le_mul_right _ hm

/-- Cells below `b` with `0 ≤ z` lie in both frames of `pre_params_spec`. -/
lemma frame_ok {z t0 K d1 : ℤ} (hz0 : 0 ≤ z) (hz : z < t0) (hd : 0 ≤ d1) :
    (z < t0 ∨ t0 + K ≤ z) ∧ (-d1 - 1 < z) := ⟨Or.inl hz, by omega⟩

lemma emb_self (Q : Program) : Embeds Q Q 0 := fun i x h => by simpa using h

/-- The step bound of the whole construction run. -/
def preT (n k N m p₀ : ℕ) : ℕ :=
  (25 + 4 * n + 6 * k + 4 * 2 ^ k + 2 ^ k * (k * (10 * 2 ^ k + 8) + 5 * 2 ^ k + 14)) +
  (n * (n * pairB (2 ^ k) (n * n) + 8) + 7) +
  (48 + 4 * N + 40 * (N * 2 ^ k) + 6 * m + 40 * p₀ + 4 * 2 ^ m + 5 * (2 ^ m * 2 ^ k)) + 1 +
  (2 ^ m * 2 ^ k * (2 * evalB N (2 ^ k) (2 ^ m) p₀ + 14) + 3)

lemma pre_run (q : ℚ) (k n : ℕ) (hn : 2 ^ k ≤ n) (P : Fin n → EuclideanSpace ℝ (Fin (2 ^ k)))
    (hP : Function.Injective P) (τ : ℝ) (hτ : 0 < τ) :
    ∃ t m, (run (pre q 0) (inputState P τ) detTape t).halted = true ∧
      ((run (pre q 0) (inputState P τ) detTape t).work : ℕ) = t ∧
      t ≤ preT n k (ddList (ptSeq P) n).length m (momentOrder (ddList (ptSeq P) n).length (2 ^ k)) ∧
      ((q : ℚ) : ℝ) * (momentOrder (ddList (ptSeq P) n).length (2 ^ k) : ℝ) ≤ 2 ^ m * (τ * τ) ∧
      (∀ m' : ℕ, m' < m →
        2 ^ m' * (τ * τ) < ((q : ℚ) : ℝ) * (momentOrder (ddList (ptSeq P) n).length (2 ^ k) : ℝ)) ∧
      (run (pre q 0) (inputState P τ) detTape t).integerMemory 0 = ((2 ^ m : ℕ) : ℤ) ∧
      (run (pre q 0) (inputState P τ) detTape t).integerMemory 1 = ((2 ^ k : ℕ) : ℤ) ∧
      SignsAt (run (pre q 0) (inputState P τ) detTape t).core.mem (2 ^ m) k
        (greedySigns (lemma62Expr (sylvester k) (2 ^ m) τ
          (momentOrder (ddList (ptSeq P) n).length (2 ^ k)) (ddList (ptSeq P) n).toFinset)
          (2 ^ m * 2 ^ k)) := by
  set Q := pre q 0 with hQ
  have hE : Embeds Q (pre q 0) 0 := emb_self Q
  set s0 := inputState P τ with hs0
  have hd1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  set x := ptSeq P with hx
  set l := ddList x n with hl
  set N := l.length with hN
  set p₀ := momentOrder N (2 ^ k) with hp₀
  -- setup
  obtain ⟨t1, ht1, a1, a2, a3, a4, _, a6, _, a8, a9, a10, _, a12, a13, a14, a15, _, _, a18, a19, a20,
    a21⟩ :=
    pre_setup_spec Q 0 q hE n k τ s0 (by rw [inp_pc]) (inp_halted P τ) (by rw [inp_ptrs])
      (by rw [inp_im0]) (by rw [inp_im1]) (by rw [inp_mem0])
  set s1 := run Q s0 detTape t1 with hs1
  set Hb : ℤ := ((1 + n * 2 ^ k : ℕ) : ℤ) with hHb
  set Db : ℤ := ((1 + n * 2 ^ k + 2 ^ k * 2 ^ k : ℕ) : ℤ) with hDb
  have hHD : Hb + ((2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ Db := by simp only [hHb, hDb]; push_cast; omega
  have hH0 : 0 ≤ Hb := by positivity
  -- dedupe
  have hpts : ∀ i' : ℕ, i' < n → ∀ c : Fin (2 ^ k),
      s1.core.mem ((1 + i' * 2 ^ k + c : ℕ) : ℤ) = x i' c := by
    intro i' hi' c
    have hlt : 1 + i' * 2 ^ k + (c : ℕ) < 1 + n * 2 ^ k := by
      have := c.isLt
      have : (i' + 1) * 2 ^ k ≤ n * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have hlt' : ((1 + i' * 2 ^ k + (c : ℕ) : ℕ) : ℤ) < Hb := by simp only [hHb]; exact_mod_cast hlt
    rw [a20 _ (Or.inl hlt')]
    have := inp_pts P τ ⟨i', hi'⟩ c
    simp only [hx, ptSeq, dif_pos hi']
    rw [show ((1 + i' * 2 ^ k + (c : ℕ) : ℕ) : ℤ) =
      1 + (((⟨i', hi'⟩ : Fin n) : ℕ) : ℤ) * ((2 ^ k : ℕ) : ℤ) + ((c : ℕ) : ℤ) by push_cast; ring]
    exact this
  obtain ⟨t2, ht2, b1, b2, b23, b28, b26, bfr, brf, bT, bmf, bim, bw, b27⟩ :=
    pre_dedup Q 0 q hE hd1 n x Db (by simp only [hDb]; exact_mod_cast Nat.le_add_right _ _) s1 a1 a2
      (by rw [a8]) (by rw [a6]) (by rw [a9]) hpts
  set s2 := run Q s1 detTape t2 with hs2
  set t0 : ℤ := Db + ((N * 2 ^ k : ℕ) : ℤ) with ht0
  have hDt : Db + ((l.length * 2 ^ k : ℕ) : ℤ) ≤ t0 := le_rfl
  have ht00 : 0 ≤ t0 := by positivity
  -- parameters
  obtain ⟨t3, m, c1, c2, chq, chm, ct, c14, c34, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46,
    c23, c15, c47, cfr, c9, c10, c11, crf, cfact, csg, cmf, cim, cw⟩ :=
    pre_params_spec Q 0 q hE N (2 ^ k) t0 τ ht00 hτ s2 b1 b2 (by rw [b28]) (by
      rw [bfr 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), a6]) b23
      (by rw [brf 5 (by decide) (by decide) (by decide), a12])
      (by rw [brf 7 (by decide) (by decide) (by decide), a14])
      (by rw [brf 8 (by decide) (by decide) (by decide), a15])
  set s3 := run Q s2 detTape t3 with hs3
  -- greedy
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ := g_init Q 0 q hE s3 c1 c2
  -- g3: ptrs 48 = 0, g4: frame, g5: regs, g6: mem, g7: im, g8: work
  set s4 := run Q s3 detTape 1 with hs4
  have f23 : ∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 23 → y ≠ 26 → y ≠ 27 → y ≠ 28 → y ≠ 29 →
      y ≠ 30 → y ≠ 31 → y ≠ 32 → y ≠ 14 → y ≠ 15 → y < 33 → y ≠ 48 →
      s4.core.ptrs y = s1.core.ptrs y :=
    fun y a b c e f g' h i j k' l' u v w z => by
      rw [g4 y z, cfr y a b u v e (Or.inl w), bfr y a b c e f g' h i j k' l']
  have reg4 : ∀ y, 5 ≤ y → y ≤ 8 → s4.core.regs y = s1.core.regs y := fun y a b => by
    rw [g5, crf y (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      brf y (by omega) (by omega) (by omega)]
  have hL : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hlen : ∀ (m' : ℕ) (v : EuclideanSpace ℝ (Fin (2 ^ k))), l[m']? = some v → m' < l.length := by
    intro m' v hv
    by_contra h; push Not at h; rw [List.getElem?_eq_none h] at hv; exact absurd hv (by simp)
  have hc : Ctx k (2 ^ m) p₀ τ l Hb Db t0 s4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [f23 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        a3]
    · rw [f23 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        a4]
    · rw [f23 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        a6]
    · rw [g4 14 (by decide), c14]
    · rw [g4 15 (by decide), c15]
    · rw [f23 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        a10]
    · rw [g4 26 (by decide), cfr 26 (by decide) (by decide) (by decide) (by decide) (by decide)
        (Or.inl (by decide)), b26]
    · rw [g4 27 (by decide), cfr 27 (by decide) (by decide) (by decide) (by decide) (by decide)
        (Or.inl (by decide)), b27]
    · rw [g4 36 (by decide), c36]
    · rw [g4 37 (by decide), c37]
    · rw [g4 39 (by decide), c39]
    · rw [g4 40 (by decide), c40]
    · rw [g4 41 (by decide), c41]
    · rw [g4 42 (by decide), c42]
    · rw [g4 43 (by decide), c43]
    · rw [g4 44 (by decide), c44]
    · rw [g4 45 (by decide), c45]
    · rw [g4 46 (by decide), c46]
    · rw [g4 47 (by decide), c47]
    · rw [reg4 5 (by omega) (by omega), a12]
    · rw [reg4 6 (by omega) (by omega), a13]
    · rw [reg4 7 (by omega) (by omega), a14]
    · rw [reg4 8 (by omega) (by omega), a15]
    · intro r j
      have hlt' : (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ) < ((2 ^ k * 2 ^ k : ℕ) : ℤ) := by
        exact_mod_cast idx_lt r.isLt j.isLt
      have h0 : (0 : ℤ) ≤ (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ) := by positivity
      have hNd : (0 : ℤ) ≤ ((N * 2 ^ k : ℕ) : ℤ) := by positivity
      have hzD : Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ) < Db := by
        have := hHD; linarith
      have hz0 : 0 ≤ Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ) := by linarith
      have hzt : Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ) < t0 := by simp only [ht0]; linarith
      obtain ⟨f1, f2⟩ := frame_ok (K := ((4 * p₀ + 1 : ℕ) : ℤ)) hz0 hzt
        (show (0 : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) by positivity)
      rw [g6, cmf _ f1 (Or.inl f2), bmf _ hzD]
      exact a19 r j
    · intro m' v hv c
      have hm' := hlen m' v hv
      have hlt' : ((m' * 2 ^ k + (c : ℕ) : ℕ) : ℤ) < ((N * 2 ^ k : ℕ) : ℤ) := by
        exact_mod_cast idx_lt2 hm' c.isLt
      have h0 : (0 : ℤ) ≤ ((m' * 2 ^ k + (c : ℕ) : ℕ) : ℤ) := by positivity
      have hD0 : 0 ≤ Db := by positivity
      have hz0 : 0 ≤ Db + ((m' * 2 ^ k + (c : ℕ) : ℕ) : ℤ) := by linarith
      have hzt : Db + ((m' * 2 ^ k + (c : ℕ) : ℕ) : ℤ) < t0 := by simp only [ht0]; linarith
      obtain ⟨f1, f2⟩ := frame_ok (K := ((4 * p₀ + 1 : ℕ) : ℤ)) hz0 hzt
        (show (0 : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) by positivity)
      rw [g6, cmf _ f1 (Or.inl f2)]
      exact bT m' v hv c
    · intro i' hi'; rw [g6]; exact cfact i' hi'
  have hS : SignsAt s4.core.mem (2 ^ m) k
      (greedySigns (lemma62Expr (sylvester k) (2 ^ m) τ p₀ l.toFinset) 0) := by
    intro ℓ r
    have hlt : (ℓ : ℕ) * 2 ^ k + r < 2 ^ m * 2 ^ k := idx_lt2 ℓ.isLt r.isLt
    have := csg _ hlt
    rw [g6, show -(2 ^ k : ℤ) - 1 - ((ℓ : ℤ) * 2 ^ k + r) =
      -((2 ^ k : ℕ) : ℤ) - 1 - (((ℓ : ℕ) * 2 ^ k + r : ℕ) : ℤ) by push_cast; ring, this]
    simp [greedySigns, signOf]
  have hl0 : ∀ v ∈ l, v ≠ 0 := fun v hv => (ddList_props P hP).1 v (List.mem_toFinset.2 hv)
  obtain ⟨t5, ht5, e1, e2, e3, e4, e5⟩ :=
    greedy_loop Q 0 q hE k (2 ^ m) p₀ hL τ hτ l (ddList_nodup x n) hl0 Hb Db t0 hHD hDt hH0
      (2 ^ m * 2 ^ k) 0 s4 (by omega) g1 g2 hc g3 hS
  refine ⟨t1 + t2 + t3 + 1 + t5, m, ?_⟩
  have e : run Q s0 detTape (t1 + t2 + t3 + 1 + t5) = run Q s4 detTape t5 := by
    rw [run_add, run_add, run_add, run_add, ← hs1, ← hs2, ← hs3, ← hs4]
  rw [e]
  refine ⟨e1, by rw [e5, g8, cw, bw, a21, inp_work]; ring, ?_, chq, chm, e3, ?_, e2⟩
  · rw [← hp₀] at ct; rw [← hN] at ht5
    unfold preT; omega
  rw [e4 1 (by decide), g7, cim, bim, a18 1 (by norm_num), inp_im1]

end DetANN.Supplement.Thm32

-- ===== T32_Final =====
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

lemma log_two_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

lemma k_le_log {k n : ℕ} (h : 2 ^ k ≤ n) : (k : ℝ) ≤ 2 * Real.log n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (Nat.two_pow_pos k) h
  have h1 : (k : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h)
  have h2 := log_two_half
  have : (0 : ℝ) ≤ k := by positivity
  nlinarith

lemma p0_le {N d n : ℕ} (hn : 1 ≤ n) (hN : N ≤ n * n) (hd : d ≤ n) :
    (momentOrder N d : ℝ) ≤ 3 * (1 + Real.log n) := by
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  unfold momentOrder
  by_cases h0 : 8 * (N : ℝ) * d ≤ 1
  · have : Real.logb 4 (8 * N * d) ≤ 0 :=
      Real.logb_nonpos (by norm_num) (by positivity) h0
    rw [Nat.ceil_eq_zero.2 this]; push_cast; linarith
  · push Not at h0
    have hpos : 0 < 8 * (N : ℝ) * d := by linarith
    have hl0 : 0 ≤ Real.logb 4 (8 * N * d) := Real.logb_nonneg (by norm_num) h0.le
    have hc := Nat.ceil_lt_add_one hl0
    have hNn : (N : ℝ) ≤ n * n := by exact_mod_cast hN
    have hdn : (d : ℝ) ≤ n := by exact_mod_cast hd
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hb : 8 * (N : ℝ) * d ≤ 8 * (n : ℝ) ^ 3 := by
      have : (0 : ℝ) ≤ N := by positivity
      have : (0 : ℝ) ≤ d := by positivity
      nlinarith
    have hlb : Real.logb 4 (8 * N * d) ≤ Real.logb 4 (8 * (n : ℝ) ^ 3) :=
      Real.logb_le_logb_of_le (by norm_num) hpos hb
    have hl2 := log_two_half
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have e4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hv : Real.logb 4 (8 * (n : ℝ) ^ 3) ≤ 3 / 2 + 3 * Real.log n := by
      rw [Real.logb, Real.log_mul (by norm_num) (by positivity), Real.log_pow, e8, e4,
        div_le_iff₀ (by linarith)]
      push_cast
      nlinarith
    linarith

lemma preT_le (n k N m p₀ Z : ℕ) (hZ : 1 ≤ Z) (hn : n ≤ Z) (hd : 2 ^ k ≤ Z) (hk : k ≤ Z)
    (hN : N ≤ Z ^ 2) (hp : p₀ ≤ 6 * Z) (hL : 2 ^ m ≤ Z ^ 3) (hm : m ≤ Z ^ 3) :
    preT n k N m p₀ ≤ 35123696 * Z ^ 13 := by
  have hZ0 : 0 < Z := hZ
  have z2 : Z ≤ Z ^ 2 := by nlinarith
  have p12 : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ hZ0
  have z23 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ0 (by norm_num)
  have z34 : Z ^ 3 ≤ Z ^ 4 := Nat.pow_le_pow_right hZ0 (by norm_num)
  have z45 : Z ^ 4 ≤ Z ^ 5 := Nat.pow_le_pow_right hZ0 (by norm_num)
  have z59 : Z ^ 5 ≤ Z ^ 9 := Nat.pow_le_pow_right hZ0 (by norm_num)
  have z913 : Z ^ 9 ≤ Z ^ 13 := Nat.pow_le_pow_right hZ0 (by norm_num)
  -- EVAL
  have hE : evalB N (2 ^ k) (2 ^ m) p₀ ≤ 17561600 * Z ^ 9 := by
    unfold evalB
    have e1 : N + 1 ≤ 2 * Z ^ 2 := by omega
    have e2 : 2 ^ k + 1 ≤ 2 * Z := by omega
    have e3 : 2 ^ m + 1 ≤ 2 * Z ^ 3 := by omega
    have e4 : 2 ^ k + 4 * p₀ + 3 ≤ 28 * Z := by omega
    calc 100 * (N + 1) * (2 ^ k + 1) * (2 ^ m + 1) * (2 ^ k + 4 * p₀ + 3) ^ 3
        ≤ 100 * (2 * Z ^ 2) * (2 * Z) * (2 * Z ^ 3) * (28 * Z) ^ 3 := by gcongr
      _ = 17561600 * Z ^ 9 := by ring
  have hG : 2 ^ m * 2 ^ k * (2 * evalB N (2 ^ k) (2 ^ m) p₀ + 14) + 3 ≤ 35123217 * Z ^ 13 := by
    have h1 : 2 * evalB N (2 ^ k) (2 ^ m) p₀ + 14 ≤ 35123214 * Z ^ 9 := by omega
    calc 2 ^ m * 2 ^ k * (2 * evalB N (2 ^ k) (2 ^ m) p₀ + 14) + 3
        ≤ Z ^ 3 * Z * (35123214 * Z ^ 9) + 3 := by gcongr
      _ = 35123214 * Z ^ 13 + 3 := by ring
      _ ≤ 35123217 * Z ^ 13 := by omega
  -- dedupe
  have hpB : pairB (2 ^ k) (n * n) ≤ 40 * Z ^ 3 := by
    unfold pairB
    calc 10 * 2 ^ k + 10 + n * n * (12 * 2 ^ k + 8) ≤ 10 * Z + 10 + Z * Z * (12 * Z + 8) := by gcongr
      _ = 10 * Z + 10 + 12 * Z ^ 3 + 8 * Z ^ 2 := by ring
      _ ≤ 40 * Z ^ 3 := by omega
  have hD : n * (n * pairB (2 ^ k) (n * n) + 8) + 7 ≤ 55 * Z ^ 5 := by
    calc n * (n * pairB (2 ^ k) (n * n) + 8) + 7 ≤ Z * (Z * (40 * Z ^ 3) + 8) + 7 := by gcongr
      _ = 40 * Z ^ 5 + 8 * Z + 7 := by ring
      _ ≤ 55 * Z ^ 5 := by omega
  -- setup
  have hS : 25 + 4 * n + 6 * k + 4 * 2 ^ k + 2 ^ k * (k * (10 * 2 ^ k + 8) + 5 * 2 ^ k + 14) ≤
      76 * Z ^ 3 := by
    calc 25 + 4 * n + 6 * k + 4 * 2 ^ k + 2 ^ k * (k * (10 * 2 ^ k + 8) + 5 * 2 ^ k + 14)
        ≤ 25 + 4 * Z + 6 * Z + 4 * Z + Z * (Z * (10 * Z + 8) + 5 * Z + 14) := by gcongr
      _ = 25 + 28 * Z + 13 * Z ^ 2 + 10 * Z ^ 3 := by ring
      _ ≤ 76 * Z ^ 3 := by omega
  -- parameters
  have hP : 48 + 4 * N + 40 * (N * 2 ^ k) + 6 * m + 40 * p₀ + 4 * 2 ^ m + 5 * (2 ^ m * 2 ^ k) ≤
      347 * Z ^ 4 := by
    calc 48 + 4 * N + 40 * (N * 2 ^ k) + 6 * m + 40 * p₀ + 4 * 2 ^ m + 5 * (2 ^ m * 2 ^ k)
        ≤ 48 + 4 * Z ^ 2 + 40 * (Z ^ 2 * Z) + 6 * Z ^ 3 + 40 * (6 * Z) + 4 * Z ^ 3 + 5 * (Z ^ 3 * Z) := by
          gcongr
      _ = 48 + 4 * Z ^ 2 + 50 * Z ^ 3 + 240 * Z + 5 * Z ^ 4 := by ring
      _ ≤ 347 * Z ^ 4 := by omega
  unfold preT
  omega

lemma b_le {m n : ℕ} (hn : 1 ≤ n) {τ qr p0 : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (hq : 0 ≤ qr)
    (hp0 : 0 ≤ p0) (hp : p0 ≤ 3 * (1 + Real.log n))
    (hmin : ∀ m' : ℕ, m' < m → 2 ^ m' * (τ * τ) < qr * p0) :
    (2 : ℝ) ^ m ≤ (1 + 6 * qr) * τ⁻¹ ^ 2 * (1 + Real.log n) := by
  have h := reps_spec.2.2 m (qr * p0) τ hτ hmin
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hA : 1 ≤ τ⁻¹ ^ 2 := one_le_pow₀ (one_le_inv₀ hτ |>.2 hτ1.le)
  have hB : 1 ≤ 1 + Real.log n := by linarith
  have hX : 2 * (qr * p0) / (τ * τ) = 2 * qr * p0 * τ⁻¹ ^ 2 := by field_simp
  have hX0 : 0 ≤ 2 * qr * p0 * τ⁻¹ ^ 2 := by positivity
  have hmax : max 1 (2 * (qr * p0) / (τ * τ)) ≤ 1 + 2 * qr * p0 * τ⁻¹ ^ 2 := by
    rw [hX]; exact max_le (by linarith) (by linarith)
  have h1 : 2 * qr * p0 * τ⁻¹ ^ 2 ≤ 6 * qr * (1 + Real.log n) * τ⁻¹ ^ 2 := by
    have : 2 * qr * p0 ≤ 6 * qr * (1 + Real.log n) := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h2 : 1 ≤ τ⁻¹ ^ 2 * (1 + Real.log n) := by nlinarith
  nlinarith

lemma p0_le_nat {N d n : ℕ} (hn : 1 ≤ n) (hN : N ≤ n * n) (hd : d ≤ n) : momentOrder N d ≤ 3 * n := by
  have h := p0_le hn hN hd
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by exact_mod_cast hn)
  have : (momentOrder N d : ℝ) ≤ 3 * n := by linarith
  exact_mod_cast this

lemma cube_le {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : a * b * (c * c) ≤ (a * b * c) ^ 3 := by
  have h1 : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2 : 1 ≤ a * b * c := Nat.one_le_iff_ne_zero.2 (by positivity)
  have : a * b * (c * c) ≤ (a * b * c) * (a * b * c) := by
    have : a * b * (c * c) = (a * b * c) * c := by ring
    rw [this]; exact Nat.mul_le_mul_left _ (le_trans (by nlinarith) (Nat.le_mul_of_pos_left c (by positivity)))
  calc a * b * (c * c) ≤ (a * b * c) * (a * b * c) := this
    _ ≤ (a * b * c) * (a * b * c) * (a * b * c) := Nat.le_mul_of_pos_right _ (by positivity)
    _ = (a * b * c) ^ 3 := by ring

lemma L_le_cube (Q n T m p₀ : ℕ) (τ : ℝ) (hτ : 0 < τ) (hn1 : 1 ≤ n) (hT1 : 1 ≤ T)
    (hTi : τ⁻¹ ≤ T) (hp3 : p₀ ≤ 3 * n)
    (hmin : ∀ m' : ℕ, m' < m → 2 ^ m' * (τ * τ) < (Q : ℝ) * p₀) :
    2 ^ m ≤ ((1 + 6 * Q) * n * T) ^ 3 := by
  have hr := reps_spec.2.2 m ((Q : ℝ) * p₀) τ hτ hmin
  have hp3r : (p₀ : ℝ) ≤ 3 * n := by exact_mod_cast hp3
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hp0 : (0 : ℝ) ≤ p₀ := by positivity
  have hti : (0 : ℝ) ≤ τ⁻¹ := by positivity
  have hX : 2 * ((Q : ℝ) * p₀) / (τ * τ) ≤ 6 * Q * n * (T * T) := by
    have e : 2 * ((Q : ℝ) * p₀) / (τ * τ) = (2 * ((Q : ℝ) * p₀)) * (τ⁻¹ * τ⁻¹) := by field_simp
    rw [e]
    have h1 : 2 * ((Q : ℝ) * p₀) ≤ 6 * Q * n := by nlinarith
    have h2 : τ⁻¹ * τ⁻¹ ≤ (T : ℝ) * T := mul_le_mul hTi hTi hti (by positivity)
    calc (2 * ((Q : ℝ) * p₀)) * (τ⁻¹ * τ⁻¹) ≤ (6 * Q * n) * (T * T) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 6 * Q * n * (T * T) := by ring
  have hnT : (1 : ℝ) ≤ n * (T * T) := by
    have a : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have b : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    have : (1 : ℝ) ≤ T * T := by nlinarith
    nlinarith
  have hr2 : (2 : ℝ) ^ m ≤ (((1 + 6 * Q) * n * (T * T) : ℕ) : ℝ) := by
    push_cast
    calc (2 : ℝ) ^ m ≤ max 1 (2 * ((Q : ℝ) * p₀) / (τ * τ)) := hr
      _ ≤ 1 + 6 * Q * n * (T * T) := max_le (by nlinarith) (by linarith)
      _ = 1 + 6 * (Q : ℝ) * (n * (T * T)) := by ring
      _ ≤ n * (T * T) + 6 * (Q : ℝ) * (n * (T * T)) := by linarith
      _ = (1 + 6 * Q) * n * (T * T) := by ring
  have : 2 ^ m ≤ (1 + 6 * Q) * n * (T * T) := by exact_mod_cast hr2
  exact le_trans this (cube_le (by omega) hn1 hT1)

lemma Z_le (Q n T k : ℕ) (τ : ℝ) (hτ : 0 < τ) (hTr : (T : ℝ) ≤ 2 * τ⁻¹) :
    (((1 + 6 * Q) * n * T : ℕ) : ℝ) ≤ 2 * (1 + 6 * Q) * ((n : ℝ) * (2 ^ k : ℕ) / τ) := by
  push_cast
  have hd1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hti : (0 : ℝ) ≤ 2 * τ⁻¹ := by positivity
  have h1 : (n : ℝ) * T ≤ n * (2 * τ⁻¹) := mul_le_mul_of_nonneg_left hTr hn0
  have h2 : (n : ℝ) * (2 * τ⁻¹) ≤ n * 2 ^ k * (2 * τ⁻¹) := by
    have : (n : ℝ) ≤ n * 2 ^ k := le_mul_of_one_le_right hn0 hd1
    exact mul_le_mul_of_nonneg_right this hti
  have hQ : (0 : ℝ) ≤ 1 + 6 * Q := by positivity
  calc (1 + 6 * (Q : ℝ)) * n * T = (1 + 6 * Q) * (n * T) := by ring
    _ ≤ (1 + 6 * Q) * (n * 2 ^ k * (2 * τ⁻¹)) := mul_le_mul_of_nonneg_left (h1.trans h2) hQ
    _ = 2 * (1 + 6 * Q) * (n * 2 ^ k / τ) := by rw [div_eq_mul_inv]; ring

lemma time_le (Q n k m N p₀ t : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hn1 : 1 ≤ n)
    (hdn : 2 ^ k ≤ n) (hNn : N ≤ n * n) (hp3 : p₀ ≤ 3 * n)
    (hmin : ∀ m' : ℕ, m' < m → 2 ^ m' * (τ * τ) < (Q : ℝ) * p₀) (ht : t ≤ preT n k N m p₀) :
    (t : ℝ) ≤ (35123696 * (2 * (1 + 6 * Q)) ^ 13 : ℕ) * ((n : ℝ) * (2 ^ k : ℕ) / τ) ^ 13 := by
  set T : ℕ := ⌈τ⁻¹⌉₊ with hT
  have hτi : 1 < τ⁻¹ := (one_lt_inv₀ hτ).2 hτ1
  have hTi : τ⁻¹ ≤ T := Nat.le_ceil _
  have hT1 : 1 ≤ T := by
    have : (1 : ℝ) < T := lt_of_lt_of_le hτi hTi
    exact_mod_cast this.le
  have hTr : (T : ℝ) ≤ 2 * τ⁻¹ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ τ⁻¹ by positivity); rw [← hT] at this; linarith
  set Z : ℕ := (1 + 6 * Q) * n * T with hZ
  have hnZ : n ≤ Z := by
    simp only [hZ]
    calc n = 1 * n * 1 := by ring
      _ ≤ (1 + 6 * Q) * n * T := by gcongr <;> omega
  have hZ1 : 1 ≤ Z := le_trans hn1 hnZ
  have hLZ := L_le_cube Q n T m p₀ τ hτ hn1 hT1 hTi hp3 hmin
  have hNZ : N ≤ Z ^ 2 := by
    have : n * n ≤ Z ^ 2 := by rw [sq]; exact Nat.mul_le_mul hnZ hnZ
    omega
  have hB := preT_le n k N m p₀ Z hZ1 hnZ (le_trans hdn hnZ)
    (le_trans (Nat.lt_two_pow_self).le (le_trans hdn hnZ)) hNZ (by omega) hLZ
    (le_trans (Nat.lt_two_pow_self).le hLZ)
  have hZr := Z_le Q n T k τ hτ hTr
  rw [← hZ] at hZr
  have ht' : (t : ℝ) ≤ 35123696 * (Z : ℝ) ^ 13 := by exact_mod_cast le_trans ht hB
  have hZ0 : (0 : ℝ) ≤ Z := by positivity
  have hpow : (Z : ℝ) ^ 13 ≤ (2 * (1 + 6 * Q)) ^ 13 * ((n : ℝ) * (2 ^ k : ℕ) / τ) ^ 13 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hZ0 (by linarith) 13
  calc (t : ℝ) ≤ 35123696 * (Z : ℝ) ^ 13 := ht'
    _ ≤ 35123696 * ((2 * (1 + 6 * Q)) ^ 13 * ((n : ℝ) * (2 ^ k : ℕ) / τ) ^ 13) := by gcongr
    _ = (35123696 * (2 * (1 + 6 * Q)) ^ 13 : ℕ) * ((n : ℝ) * (2 ^ k : ℕ) / τ) ^ 13 := by
      push_cast; ring

/-- The constant of Theorem 3.2. -/
def cst (Q : ℕ) : ℕ := 35123696 * (2 * (1 + 6 * Q)) ^ 13 + 164 + (1 + 6 * Q)

lemma cst_ge (Q : ℕ) : 35123696 * (2 * (1 + 6 * Q)) ^ 13 ≤ cst Q ∧ 164 ≤ cst Q ∧ 1 + 6 * Q ≤ cst Q := by
  unfold cst; omega

/-- The constant `C₀*` of `theorem_3_2_greedy`. -/
noncomputable def C0s : ℝ := Classical.choose theorem_3_2_greedy

lemma balanced (k m n : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin (2 ^ k))) (hP : Function.Injective P)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hq : ((⌈C0s⌉₊ : ℕ) : ℝ) * (momentOrder (ddList (ptSeq P) n).length (2 ^ k) : ℝ) ≤ 2 ^ m * (τ * τ)) :
    IsBalancedBlockSystem τ (Finset.univ.image P) (signedBlocks (sylvester k) (2 ^ m)
      (greedySigns (lemma62Expr (sylvester k) (2 ^ m) τ
        (momentOrder (ddList (ptSeq P) n).length (2 ^ k)) (ddList (ptSeq P) n).toFinset)
        (2 ^ m * 2 ^ k))) := by
  have hL : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  by_cases hn2 : 2 ≤ n
  · obtain ⟨_, hgr⟩ := Classical.choose_spec theorem_3_2_greedy
    obtain ⟨h0, hpair, hcard, hne⟩ := ddList_props P hP
    have hN1 : 1 ≤ (ddList (ptSeq P) n).length := by rw [← hcard]; exact hne hn2
    have hp : 0 < momentOrder (ddList (ptSeq P) n).length (2 ^ k) := by
      unfold momentOrder
      apply Nat.ceil_pos.2
      apply Real.logb_pos (by norm_num)
      have : (1 : ℝ) ≤ (ddList (ptSeq P) n).length := by exact_mod_cast hN1
      have : (1 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
      nlinarith
    set p₀ := momentOrder (ddList (ptSeq P) n).length (2 ^ k) with hp₀
    have hC : C0s ≤ ((2 ^ m : ℕ) : ℝ) * τ ^ 2 / p₀ :=
      le_trans (Nat.le_ceil _) (reps_spec.2.1 (2 ^ m) p₀ τ _ hp (by push_cast; exact hq))
    have hnr := reps_spec.1 (2 ^ m) p₀ τ hτ hp
    have hb := (hgr _ hC (2 ^ k) Nat.one_le_two_pow (sylvester k) (sylvester_hadamard k).1
      (sylvester_hadamard k).2.1 τ hτ hτ1 (Finset.univ.image P) (ddList (ptSeq P) n).toFinset h0 hpair
      (by rw [hcard]; exact hN1)).2.2
    rw [hcard, ← hp₀, hnr] at hb
    exact hb
  · refine ⟨fun z => (parseval_signed_blocks (sylvester k) (sylvester_hadamard k).2.1 (2 ^ m) hL _ z).2,
      ?_⟩
    intro x hx y hy i
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have : a = b := Fin.ext (by have := a.isLt; have := b.isLt; omega)
    subst this
    simp

lemma eval_part (k m : ℕ) (ξ : Fin (2 ^ m) → Fin (2 ^ k) → Bool) (s : State)
    (h4 : s.integerMemory 0 = ((2 ^ m : ℕ) : ℤ)) (h5 : s.integerMemory 1 = ((2 ^ k : ℕ) : ℤ))
    (h6 : SignsAt s.core.mem (2 ^ m) k ξ) (z : EuclideanSpace ℝ (Fin (2 ^ k))) :
    ∃ t', (run (ev 0) (queryState (2 ^ k) s z) detTape t').halted = true ∧
      ((run (ev 0) (queryState (2 ^ k) s z) detTape t').work : ℝ) ≤
        82 * (((2 ^ m : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) * (1 + k)) ∧
      ∀ (j : Fin (2 ^ k)) (ℓ : Fin (2 ^ m)),
        (run (ev 0) (queryState (2 ^ k) s z) detTape t').core.mem ((j : ℤ) * ((2 ^ m : ℕ) : ℤ) + (ℓ : ℤ)) =
          signedBlocks (sylvester k) (2 ^ m) ξ j z ℓ := by
  have hsg : ∀ (ℓ : Fin (2 ^ m)) (r : Fin (2 ^ k)),
      (queryState (2 ^ k) s z).core.mem (-(2 ^ k : ℤ) - 1 - ((ℓ : ℤ) * 2 ^ k + r)) = signOf (ξ ℓ r) := by
    intro ℓ r
    simp only [queryState]
    rw [dif_neg]
    · exact h6 ℓ r
    · intro ⟨_, h2⟩
      have : (0 : ℤ) ≤ (ℓ : ℤ) * 2 ^ k + r := by positivity
      have e : (-1 - (-(2 ^ k : ℤ) - 1 - ((ℓ : ℤ) * 2 ^ k + r))) = 2 ^ k + ((ℓ : ℤ) * 2 ^ k + r) := by ring
      rw [e] at h2
      have h3 : ((2 ^ k : ℤ) + ((ℓ : ℤ) * 2 ^ k + r)).toNat = 2 ^ k + ((ℓ : ℕ) * 2 ^ k + r) := by
        rw [show (2 ^ k : ℤ) + ((ℓ : ℤ) * 2 ^ k + r) = ((2 ^ k + ((ℓ : ℕ) * 2 ^ k + r) : ℕ) : ℤ) by
          push_cast; ring, Int.toNat_natCast]
      rw [h3] at h2
      omega
  have hz : ∀ r : Fin (2 ^ k), (queryState (2 ^ k) s z).core.mem (-1 - (r : ℤ)) = z r := by
    intro r
    simp only [queryState]
    have h1 : -1 - (r : ℤ) < 0 := by have : (0 : ℤ) ≤ r := by positivity
                                     omega
    have h2 : (-1 - (-1 - (r : ℤ))).toNat < 2 ^ k := by
      rw [show (-1 - (-1 - (r : ℤ))) = ((r : ℕ) : ℤ) by ring, Int.toNat_natCast]; exact r.isLt
    rw [dif_pos ⟨h1, h2⟩]
    have e : (⟨(-1 - (-1 - (r : ℤ))).toNat, h2⟩ : Fin (2 ^ k)) = r :=
      Fin.ext (by
        show (-1 - (-1 - (r : ℤ))).toNat = (r : ℕ)
        rw [show (-1 - (-1 - (r : ℤ))) = ((r : ℕ) : ℤ) by ring, Int.toNat_natCast])
    rw [e]
  obtain ⟨t', ht', e1, e2, e3⟩ := ev_block (ev 0) 0 (emb_self _) k (2 ^ m) Nat.one_le_two_pow ξ z
    (queryState (2 ^ k) s z) rfl rfl rfl (by simp only [queryState]; rw [h4]) (by
      simp only [queryState]; rw [h5]; push_cast; rfl) hsg hz
  -- e3 : the output cells
  refine ⟨t', e1, ?_, fun j ℓ => by rw [← e3 j ℓ]⟩
  rw [e2]
  have : (queryState (2 ^ k) s z).work = 0 := rfl
  rw [this, zero_add]
  have : ((t' : ℕ) : ℝ) ≤ ((82 * (2 ^ m * 2 ^ k * (1 + k)) : ℕ) : ℝ) := by exact_mod_cast ht'
  push_cast at this ⊢; linarith

theorem thm32 :
    ∃ Pre Ev : PNormReg.Program, DetProgram Pre ∧ DetProgram Ev ∧
      ∃ C K : ℕ, ∀ d n : ℕ, (∃ k : ℕ, d = 2 ^ k) → d ≤ n →
        ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
          ∀ τ : ℝ, 0 < τ → τ < 1 →
            IsBlockConstruction Pre Ev P τ
              ((C : ℝ) * ((n : ℝ) * d / τ) ^ K)
              ((C : ℝ) * τ⁻¹ ^ 2 * (1 + Real.log n))
              (fun b => (C : ℝ) * b * d * (1 + Real.log n)) := by
  refine ⟨pre ((⌈C0s⌉₊ : ℕ) : ℚ) 0, ev 0, det_pre _ 0, det_ev 0, cst ⌈C0s⌉₊, 13, ?_⟩
  rintro d n ⟨k, rfl⟩ hdn P hP τ hτ hτ1
  obtain ⟨t, m, h1, h2, h3, hq, hmin, h4, h5, h6⟩ := pre_run ((⌈C0s⌉₊ : ℕ) : ℚ) k n hdn P hP τ hτ
  have hqr : (((⌈C0s⌉₊ : ℕ) : ℚ) : ℝ) = ((⌈C0s⌉₊ : ℕ) : ℝ) := by push_cast; rfl
  rw [hqr] at hq hmin
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hdn
  have hNn := ddList_length (ptSeq P) n
  have hp3 := p0_le_nat (d := 2 ^ k) hn1 hNn hdn
  obtain ⟨c1, c2, c3⟩ := cst_ge ⌈C0s⌉₊
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  refine ⟨t, h1, ?_, 2 ^ m, ?_, h4, _, balanced k m n P hP τ hτ hτ1 hq, ?_⟩
  · rw [h2]
    have ht := time_le ⌈C0s⌉₊ n k m _ _ t τ hτ hτ1 hn1 hdn hNn hp3 hmin h3
    have hX0 : (0 : ℝ) ≤ ((n : ℝ) * ((2 ^ k : ℕ) : ℝ) / τ) ^ 13 := by positivity
    have hc : ((35123696 * (2 * (1 + 6 * ⌈C0s⌉₊)) ^ 13 : ℕ) : ℝ) ≤ (cst ⌈C0s⌉₊ : ℝ) := by
      exact_mod_cast c1
    calc (t : ℝ) ≤ _ := ht
      _ ≤ (cst ⌈C0s⌉₊ : ℝ) * ((n : ℝ) * ((2 ^ k : ℕ) : ℝ) / τ) ^ 13 :=
        mul_le_mul_of_nonneg_right hc hX0
  · have h := b_le hn1 hτ hτ1 (by positivity) (by positivity) (p0_le hn1 hNn hdn) hmin
    have hc : (1 + 6 * ((⌈C0s⌉₊ : ℕ) : ℝ)) ≤ (cst ⌈C0s⌉₊ : ℝ) := by exact_mod_cast c3
    have hA : (0 : ℝ) ≤ τ⁻¹ ^ 2 * (1 + Real.log n) := by positivity
    push_cast
    calc (2 : ℝ) ^ m ≤ (1 + 6 * ((⌈C0s⌉₊ : ℕ) : ℝ)) * τ⁻¹ ^ 2 * (1 + Real.log n) := h
      _ = (1 + 6 * ((⌈C0s⌉₊ : ℕ) : ℝ)) * (τ⁻¹ ^ 2 * (1 + Real.log n)) := by ring
      _ ≤ (cst ⌈C0s⌉₊ : ℝ) * (τ⁻¹ ^ 2 * (1 + Real.log n)) := mul_le_mul_of_nonneg_right hc hA
      _ = (cst ⌈C0s⌉₊ : ℝ) * τ⁻¹ ^ 2 * (1 + Real.log n) := by ring
  · intro z
    obtain ⟨t', e1, e2, e3⟩ := eval_part k m _ _ h4 h5 h6 z
    refine ⟨t', e1, ?_, e3⟩
    have hk := k_le_log hdn
    have hc : (164 : ℝ) ≤ (cst ⌈C0s⌉₊ : ℝ) := by exact_mod_cast c2
    have hLd : (0 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) := by positivity
    calc ((run (ev 0) _ detTape t').work : ℝ) ≤ 82 * (((2 ^ m : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) * (1 + k)) := e2
      _ ≤ 164 * (((2 ^ m : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) * (1 + Real.log n)) := by nlinarith
      _ ≤ (cst ⌈C0s⌉₊ : ℝ) * (((2 ^ m : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) * (1 + Real.log n)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (cst ⌈C0s⌉₊ : ℝ) * ((2 ^ m : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) * (1 + Real.log n) := by ring

end DetANN.Supplement.Thm32

namespace DetANN

namespace Supplement

theorem _root_.solution :
    ∃ Pre Ev : PNormReg.Program, DetProgram Pre ∧ DetProgram Ev ∧
      ∃ C K : ℕ, ∀ d n : ℕ, (∃ k : ℕ, d = 2 ^ k) → d ≤ n →
        ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
          ∀ τ : ℝ, 0 < τ → τ < 1 →
            IsBlockConstruction Pre Ev P τ
              ((C : ℝ) * ((n : ℝ) * d / τ) ^ K)
              ((C : ℝ) * τ⁻¹ ^ 2 * (1 + Real.log n))
              (fun b => (C : ℝ) * b * d * (1 + Real.log n)) :=
  DetANN.Supplement.Thm32.thm32

end Supplement

end DetANN
