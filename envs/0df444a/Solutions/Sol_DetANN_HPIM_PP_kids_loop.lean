-- Prove2me | solution 1 for DetANN.HPIM.PP.kids_loop
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T09:27:30.060707+00:00
-- url     : https://prove2.me/submissions/32fb9115-f8d8-4a49-b6ee-edb0de65909c

import Mathlib
import Definitions.Def_DetANN_HPIMPreProg
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks
import Theorems.Thm_DetANN_HPIM_median_threshold

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

/-- One step changes real cell `z` only if it stores to it. -/
lemma step_mem (P : Program) (ω : ℕ → Bool) (s : State) (z : ℤ)
    (h : writtenCell P s ≠ some (true, z)) : (step P ω s).core.mem z = s.core.mem z := by
  unfold writtenCell at h
  by_cases hh : s.halted = true
  · simp [step, hh]
  · simp only [Bool.not_eq_true] at hh
    rcases hP : P[s.core.pc]? with _ | ins
    · simp [step, hh, hP]
    · rw [step_eq_exec P ω s ins hh hP]
      simp only [hh, hP] at h
      cases ins with
      | core i =>
        cases i <;> simp only [exec, coreExec] <;> try rfl
        case store q r =>
          simp only [Bool.false_eq_true, if_false, ne_eq, Option.some.injEq, Prod.mk.injEq, true_and] at h
          rw [Function.update_of_ne (Ne.symm h)]
        all_goals (split_ifs <;> rfl)
      | _ => simp [exec]

/-- One step changes integer cell `z` only if it stores to it. -/
lemma step_im (P : Program) (ω : ℕ → Bool) (s : State) (z : ℤ)
    (h : writtenCell P s ≠ some (false, z)) : (step P ω s).integerMemory z = s.integerMemory z := by
  unfold writtenCell at h
  by_cases hh : s.halted = true
  · simp [step, hh]
  · simp only [Bool.not_eq_true] at hh
    rcases hP : P[s.core.pc]? with _ | ins
    · simp [step, hh, hP]
    · rw [step_eq_exec P ω s ins hh hP]
      simp only [hh, hP] at h
      cases ins with
      | integerStore a b =>
        simp only [Bool.false_eq_true, if_false, ne_eq, Option.some.injEq, Prod.mk.injEq, true_and] at h
        simp only [exec]; rw [Function.update_of_ne (Ne.symm h)]
      | core i => simp [exec]
      | _ => simp [exec]

lemma run_succ' (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ) :
    run P s ω (t + 1) = step P ω (run P s ω t) := by
  rw [run_add, run_succ, run_zero]

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

/-- A real cell that is never written keeps its value. -/
lemma run_mem_unwritten (P : Program) (s : State) (z : ℤ) :
    ∀ t, (true, z) ∉ cellsWritten P s t → (run P s detTape t).core.mem z = s.core.mem z := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    rw [cellsWritten_add] at h
    simp only [Finset.mem_union, not_or] at h
    rw [run_succ', step_mem]
    · exact ih h.1
    · intro h'; apply h.2
      simp [cellsWritten, run_zero, h']

/-- An integer cell that is never written keeps its value. -/
lemma run_im_unwritten (P : Program) (s : State) (z : ℤ) :
    ∀ t, (false, z) ∉ cellsWritten P s t →
      (run P s detTape t).integerMemory z = s.integerMemory z := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    rw [cellsWritten_add] at h
    simp only [Finset.mem_union, not_or] at h
    rw [run_succ', step_im]
    · exact ih h.1
    · intro h'; apply h.2
      simp [cellsWritten, run_zero, h']

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

lemma emb14 (hB : B.WF) : Embeds (Blocks.prog B) (seg14 B.o14 B.lbl_NODE) (B.o14) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  skip
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8 ++ B.bal B.o9 ++ seg10 B.o10 B.lbl_LK ++ B.comps B.o11 ++ seg12 B.o12 ++ B.comps B.o13) (seg14 B.o14 B.lbl_NODE)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

end DetANN.HPIM.PP

-- ===== PP_Sem =====
namespace DetANN.HPIM.PP

open DetANN.HPIM

variable {m : ℕ}

section Comp

variable {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ)

lemma thrReach_refl (i : Fin n) : thrReach P d i i := SimpleGraph.Reachable.refl _

lemma thrReach_symm {i j : Fin n} (h : thrReach P d i j) : thrReach P d j i :=
  SimpleGraph.Reachable.symm h

lemma thrReach_trans {i j k : Fin n} (h : thrReach P d i j) (h' : thrReach P d j k) :
    thrReach P d i k := SimpleGraph.Reachable.trans h h'

open Classical in
/-- The component of `i`, as a finset of local indices. -/
noncomputable def compSet (i : Fin n) : Finset (Fin n) := Finset.univ.filter (thrReach P d i)

lemma mem_compSet {i j : Fin n} : j ∈ compSet P d i ↔ thrReach P d i j := by
  classical
  simp [compSet]

lemma compSet_eq {i j : Fin n} (h : thrReach P d i j) : compSet P d i = compSet P d j := by
  ext k; rw [mem_compSet, mem_compSet]
  exact ⟨fun h' => thrReach_trans P d (thrReach_symm P d h) h', fun h' => thrReach_trans P d h h'⟩

lemma compMin_eq_min' (i : Fin n) :
    compMin P d i = ((compSet P d i).min' ⟨i, (mem_compSet P d).2 (thrReach_refl P d i)⟩ : ℕ) := by
  classical
  unfold compMin compSet
  rfl

lemma compMin_lt (i : Fin n) : compMin P d i < n := by
  rw [compMin_eq_min']; exact Fin.isLt _

/-- The component minimum as a local index. -/
noncomputable def compMinF (i : Fin n) : Fin n := ⟨compMin P d i, compMin_lt P d i⟩

lemma compMinF_mem (i : Fin n) : compMinF P d i ∈ compSet P d i := by
  have h := Finset.min'_mem (compSet P d i) ⟨i, (mem_compSet P d).2 (thrReach_refl P d i)⟩
  convert h using 1
  ext; simp [compMinF, compMin_eq_min']

lemma compMin_le (i : Fin n) : compMin P d i ≤ i := by
  rw [compMin_eq_min']
  exact_mod_cast Finset.min'_le _ _ ((mem_compSet P d).2 (thrReach_refl P d i))

lemma reach_compMin (i : Fin n) : thrReach P d i (compMinF P d i) :=
  (mem_compSet P d).1 (compMinF_mem P d i)

lemma compMin_eq_of_reach {i j : Fin n} (h : thrReach P d i j) : compMin P d i = compMin P d j := by
  rw [compMin_eq_min', compMin_eq_min']
  congr 1
  simp only [compSet_eq P d h]

lemma reach_of_compMin_eq {i j : Fin n} (h : compMin P d i = compMin P d j) : thrReach P d i j := by
  have hi := reach_compMin P d i
  have hj := reach_compMin P d j
  have : compMinF P d i = compMinF P d j := Fin.ext h
  rw [this] at hi
  exact thrReach_trans P d hi (thrReach_symm P d hj)

lemma compMin_eq_iff (i j : Fin n) : compMin P d i = compMin P d j ↔ thrReach P d i j :=
  ⟨reach_of_compMin_eq P d, compMin_eq_of_reach P d⟩

/-- `j` is in the component whose minimum is `i` iff its component minimum is `i`. -/
lemma reach_iff_compMin {i j : Fin n} (hi : compMin P d i = i) :
    thrReach P d i j ↔ compMin P d j = i := by
  rw [← compMin_eq_iff, hi]; exact ⟨fun h => h.symm, fun h => h.symm⟩

end Comp

/-- A strictly increasing enumeration of `T` is `T.orderEmbOfFin`. -/
lemma eq_orderEmbOfFin {N k : ℕ} (T : Finset (Fin N)) (hk : T.card = k) (f : Fin k → Fin N)
    (hmem : ∀ x, f x ∈ T) (hmono : StrictMono f) : ∀ x, f x = T.orderEmbOfFin hk x := by
  intro x
  have := Finset.orderEmbOfFin_unique hk hmem hmono
  rw [this]

section Ladder

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

end Ladder

end DetANN.HPIM.PP

-- ===== PP_Ret =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The ten cells of a call frame at `F`: code, `v`, `i`, `n`, `S`, `Znode`, `Kids`, `vr`, `FP`,
`ZRnode`. -/
def FrameAt (s : State) (F : ℤ) (fr : Fin 10 → ℤ) : Prop := ∀ k : Fin 10, s.integerMemory (F + k) = fr k

/-- The frame registers, in frame order after the code. -/
def frameRegs : Fin 10 → ℕ := ![0, 2, 3, 11, 10, 20, 19, 21, 8, 28]

/-- Code `≥ 1`: restore `v, i, n, S, Znode, Kids, vr, ZRnode, FP` and jump to `KN`. -/
lemma ret_resume (Q : Program) (off KN : ℕ) (hE : Embeds Q (seg14 off KN) off) (s : State)
    (hpc : s.core.pc = off + 82) (hh : s.halted = false) (fr : Fin 10 → ℤ)
    (hF : FrameAt s (s.core.ptrs 8) fr) (hc : 1 ≤ fr 0) :
    (run Q s detTape 24).core.pc = off + 76 ∧ (run Q s detTape 24).halted = false ∧
      (∀ k : Fin 10, k ≠ 0 → (run Q s detTape 24).core.ptrs (frameRegs k) = fr k) ∧
      (∀ x, x ∉ [2, 3, 11, 10, 20, 19, 21, 8, 28, 6, 27, 9] →
        (run Q s detTape 24).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 24).core.regs = s.core.regs ∧
      (run Q s detTape 24).integerMemory = s.integerMemory ∧
      (run Q s detTape 24).core.mem = s.core.mem ∧ (run Q s detTape 24).work = s.work + 24 := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hF; subst hpc hh
  have f0 : im (ptrs 8) = fr 0 := by simpa using hF 0
  have f1 : im (ptrs 8 + 1) = fr 1 := hF 1
  have f2 : im (ptrs 8 + 2) = fr 2 := hF 2
  have f3 : im (ptrs 8 + 3) = fr 3 := hF 3
  have f4 : im (ptrs 8 + 4) = fr 4 := hF 4
  have f5 : im (ptrs 8 + 5) = fr 5 := hF 5
  have f6 : im (ptrs 8 + 6) = fr 6 := hF 6
  have f7 : im (ptrs 8 + 7) = fr 7 := hF 7
  have f8 : im (ptrs 8 + 8) = fr 8 := hF 8
  have f9 : im (ptrs 8 + 9) = fr 9 := hF 9
  (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
  rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Function.update_apply]
  rw [if_neg (by simp [f0]; omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
  (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
  rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec]
  rw [if_pos le_rfl, run_zero]
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro k hk
    fin_cases k
    · exact absurd rfl hk
    all_goals
      simp (config := {decide := true}) only [frameRegs, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val, Function.update_apply, if_true, if_false, add_assoc, Int.reduceAdd,
        add_sub_assoc, Int.reduceSub]
      first | exact f1 | exact f2 | exact f3 | exact f4 | exact f5 | exact f6 | exact f7 | exact f8 | exact f9
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h2, h3, h11, h10, h20, h19, h21, h8, h28, h6, h27, h9⟩ := hx
    simp only [Function.update_apply, h2, h3, h11, h10, h20, h19, h21, h8, h28, h6, h27, h9,
      if_false]

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

-- ===== PP_Env =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- `NodeEnv` survives a segment that keeps the relevant registers, the tables, the S list and the
input points. -/
lemma NodeEnv.transfer {S : Finset (Fin N)} {v Sa Zn ZRn : ℤ} {s s' : State}
    (h : NodeEnv Y δ T0 v0 S v Sa Zn ZRn s)
    (hp : ∀ x ∈ [1, 2, 10, 11, 12, 20, 23, 28], s'.core.ptrs x = s.core.ptrs x)
    (hr : ∀ x ∈ [0, 1, 2, 20, 21, 22], s'.core.regs x = s.core.regs x)
    (hIM : ∀ z, (0 ≤ z ∧ z < Hbase N T0) ∨ (Sa ≤ z ∧ z < Sa + S.card) →
      s'.integerMemory z = s.integerMemory z)
    (hmem : ∀ z : ℤ, 0 ≤ z → z < 1 + (N : ℤ) * m → s'.core.mem z = s.core.mem z) :
    NodeEnv Y δ T0 v0 S v Sa Zn ZRn s' := by
  have g := h.g
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, h.sa⟩
  · rw [hp 1 (by simp)]; exact g.pm
  · rw [hp 12 (by simp)]; exact g.pPA
  · rw [hp 23 (by simp)]; exact g.pN
  · rw [hr 0 (by simp)]; exact g.r0
  · rw [hr 1 (by simp)]; exact g.r1
  · rw [hr 2 (by simp)]; exact g.r2
  · rw [hr 20 (by simp)]; exact g.r20
  · rw [hr 21 (by simp)]; exact g.r21
  · rw [hr 22 (by simp)]; exact g.r22
  · rw [hIM 1 (Or.inl ⟨by norm_num, by unfold Hbase; omega⟩)]; exact g.i1
  · rw [hIM 2 (Or.inl ⟨by norm_num, by unfold Hbase; omega⟩)]; exact g.i2
  · rw [hIM 3 (Or.inl ⟨by norm_num, by unfold Hbase; omega⟩)]; exact g.i3
  · intro gg
    rw [hIM _ (Or.inl ⟨by positivity, by unfold Hbase; have := gg.isLt; omega⟩)]; exact g.pa gg
  · intro t ht
    rw [hIM _ (Or.inl ⟨by positivity, by unfold Hbase; omega⟩)]; exact g.pow t ht
  · intro gg j
    have h1 : (gg : ℤ) * m + j < N * m := by
      have : (gg : ℤ) + 1 ≤ N := by exact_mod_cast gg.isLt
      have : (j : ℤ) < m := by exact_mod_cast j.isLt
      nlinarith
    rw [hmem _ (by positivity) (by linarith)]; exact g.pts gg j
  · rw [hp 2 (by simp)]; exact h.p2
  · rw [hp 10 (by simp)]; exact h.p10
  · rw [hp 11 (by simp)]; exact h.p11
  · rw [hp 20 (by simp)]; exact h.p20
  · rw [hp 28 (by simp)]; exact h.p28
  · intro i
    rw [hIM _ (Or.inr ⟨by omega, by have := i.isLt; omega⟩)]; exact h.slist i

end DetANN.HPIM.PP

-- ===== PP_Size =====
namespace DetANN.HPIM.PP

open DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m))

lemma ptsOf_inj (hY : Function.Injective Y) (S : Finset (Fin N)) : Function.Injective (ptsOf Y S) :=
  fun _ _ h => (S.orderEmbOfFin rfl).injective (hY h)

lemma compBot_card_le (hY : Function.Injective Y) (S : Finset (Fin N)) (hS : 2 ≤ S.card)
    (i : Fin S.card) : (compBotOf Y S i).card ≤ S.card / 2 := by
  obtain ⟨_, hpos, hsmall⟩ := (median_threshold (ptsOf Y S)).2.2.2 hS (ptsOf_inj Y hY S)
  unfold compBotOf
  rw [Finset.card_map]
  apply hsmall
  unfold rmedOf; linarith

end DetANN.HPIM.PP

-- ===== PP_Lists =====
namespace DetANN.HPIM.PP

open DetANN.HPIM

lemma filter_range_mem {n : ℕ} {p : ℕ → Bool} {x : ℕ} :
    x ∈ (List.range n).filter p ↔ x < n ∧ p x = true := by
  simp [List.mem_filter, List.mem_range]

lemma filter_range_lt {n : ℕ} (p : ℕ → Bool) {k k' : ℕ} (hk : k < ((List.range n).filter p).length)
    (hk' : k' < ((List.range n).filter p).length) (h : k < k') :
    ((List.range n).filter p)[k] < ((List.range n).filter p)[k'] := by
  have hP : ((List.range n).filter p).Pairwise (· < ·) := (List.pairwise_lt_range).filter _
  exact List.pairwise_iff_getElem.1 hP k k' hk hk' h

lemma filter_range_map {n : ℕ} (q : Fin n → Prop) [DecidablePred q] (p : ℕ → Bool)
    (hp : ∀ j (hj : j < n), p j = true ↔ q ⟨j, hj⟩) :
    ((List.range n).filter p).length = (Finset.univ.filter q).card := by
  have hnd : ((List.range n).filter p).Nodup := (List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  have : ((List.range n).filter p).toFinset = (Finset.univ.filter q).map Fin.valEmbedding := by
    ext x
    simp only [List.mem_toFinset, filter_range_mem, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h1⟩, (hp x h1).1 h2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.isLt, (hp y y.isLt).2 hy⟩
  rw [this, Finset.card_map]

/-- **The bridge.** `T` is the image of `{j | q j}` under the order embedding `e`; the filtered list
`L` enumerates `T` in order. -/
lemma filter_range_orderEmb {N n : ℕ} (e : Fin n ↪o Fin N) (q : Fin n → Prop) [DecidablePred q]
    (p : ℕ → Bool) (hp : ∀ j (hj : j < n), p j = true ↔ q ⟨j, hj⟩) :
    ((List.range n).filter p).length = ((Finset.univ.filter q).map e.toEmbedding).card ∧
    ∀ k (hk : k < ((List.range n).filter p).length),
      ∃ hj : ((List.range n).filter p)[k] < n,
        ((Finset.univ.filter q).map e.toEmbedding).orderEmbOfFin rfl
          ⟨k, by rw [Finset.card_map, ← filter_range_map q p hp]; exact hk⟩ =
        e ⟨((List.range n).filter p)[k], hj⟩ := by
  set L := (List.range n).filter p with hL
  set T := (Finset.univ.filter q).map e.toEmbedding with hT
  have hlen : L.length = T.card := by rw [hT, Finset.card_map]; exact filter_range_map q p hp
  have hmemL : ∀ k (hk : k < L.length), L[k] < n ∧ p L[k] = true :=
    fun k hk => filter_range_mem.1 (List.getElem_mem hk)
  refine ⟨hlen, fun k hk => ⟨(hmemL k hk).1, ?_⟩⟩
  have hx : ∀ x : Fin T.card, (x : ℕ) < L.length := fun x => by rw [hlen]; exact x.isLt
  let f : Fin T.card → Fin N := fun x => e ⟨L[(x : ℕ)]'(hx x), (hmemL x (hx x)).1⟩
  have hf : ∀ x, f x ∈ T := by
    intro x
    simp only [hT, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨_, (hp _ _).1 (hmemL x (hx x)).2, rfl⟩
  have hmono : StrictMono f := by
    intro x y hxy
    simp only [f]
    apply e.strictMono
    show L[(x : ℕ)]'_ < L[(y : ℕ)]'_
    exact filter_range_lt p _ _ hxy
  have := eq_orderEmbOfFin T rfl f hf hmono ⟨k, by rw [← hlen]; exact hk⟩
  rw [← this]

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m))

/-- The selection list of the kids loop: members `j ≥ i` with label `i`. -/
def selK (lab : ℕ → ℤ) (i n : ℕ) : List ℕ :=
  (List.range n).filter (fun j => decide (i ≤ j ∧ lab j = (i : ℤ)))

lemma slist_of_list {s : State} {a : ℤ} {T : Finset (Fin N)} {L : List ℕ} {vals : ℕ → ℤ}
    (hlen : L.length = T.card)
    (hval : ∀ k (hk : k < L.length), vals L[k] = ((T.orderEmbOfFin rfl ⟨k, hlen ▸ hk⟩ : Fin N) : ℕ))
    (hst : ∀ k (hk : k < L.length), s.integerMemory (a + k) = vals L[k]) : SList s a T := by
  intro i
  have hi : (i : ℕ) < L.length := by rw [hlen]; exact i.isLt
  rw [hst i hi, hval i hi]

lemma slist_comp (S : Finset (Fin N)) {s : State} {a : ℤ} (lab vals : ℕ → ℤ) (i0 : ℕ)
    (hi0 : i0 < S.card)
    (hlab : ∀ j (hj : j < S.card), lab j = compMin (ptsOf Y S) (2 * (rmedOf Y S / 2)) ⟨j, hj⟩)
    (hrep : compMin (ptsOf Y S) (2 * (rmedOf Y S / 2)) ⟨i0, hi0⟩ = i0)
    (hvals : ∀ j (hj : j < S.card), vals j = ((S.orderEmbOfFin rfl ⟨j, hj⟩ : Fin N) : ℕ))
    (hst : ∀ k (hk : k < (selK lab i0 S.card).length),
      s.integerMemory (a + k) = vals (selK lab i0 S.card)[k]) :
    (selK lab i0 S.card).length = (compBotOf Y S ⟨i0, hi0⟩).card ∧
      SList s a (compBotOf Y S ⟨i0, hi0⟩) := by
  have hp : ∀ j (hj : j < S.card), decide (i0 ≤ j ∧ lab j = (i0 : ℤ)) = true ↔
      thrReach (ptsOf Y S) (2 * (rmedOf Y S / 2)) ⟨i0, hi0⟩ ⟨j, hj⟩ := by
    intro j hj
    rw [decide_eq_true_iff, reach_iff_compMin _ _ hrep, hlab j hj]
    have hle : compMin (ptsOf Y S) (2 * (rmedOf Y S / 2)) ⟨j, hj⟩ ≤ j :=
      compMin_le (ptsOf Y S) (2 * (rmedOf Y S / 2)) ⟨j, hj⟩
    constructor
    · rintro ⟨_, h⟩; exact_mod_cast h
    · intro h
      have h' : compMin (ptsOf Y S) (2 * (rmedOf Y S / 2)) ⟨j, hj⟩ = i0 := h
      exact ⟨by omega, by rw [h']⟩
  obtain ⟨hlen, hget⟩ := filter_range_orderEmb (S.orderEmbOfFin rfl)
    (thrReach (ptsOf Y S) (2 * (rmedOf Y S / 2)) ⟨i0, hi0⟩) _ hp
  have hlen' : (selK lab i0 S.card).length = (compBotOf Y S ⟨i0, hi0⟩).card := hlen
  refine ⟨hlen', slist_of_list hlen' (fun k hk => ?_) hst⟩
  obtain ⟨hj, he⟩ := hget k hk
  exact (hvals _ hj).trans (congrArg (fun x : Fin N => ((x : ℕ) : ℤ)) he.symm)

end DetANN.HPIM.PP

-- ===== PP_KLoops =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

lemma selK_succ (lab : ℕ → ℤ) (i j : ℕ) :
    selK lab i (j + 1) = selK lab i j ++ (if i ≤ j ∧ lab j = (i : ℤ) then [j] else []) := by
  unfold selK
  rw [List.range_succ, List.filter_append]
  by_cases h : i ≤ j ∧ lab j = (i : ℤ)
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp only [List.filter_cons, List.filter_nil]; simp [h]

lemma selK_len_mono (lab : ℕ → ℤ) (i : ℕ) {j j' : ℕ} (h : j ≤ j') :
    (selK lab i j).length ≤ (selK lab i j').length :=
  ((List.range_sublist.2 h).filter _).length_le

lemma selK_len_le (lab : ℕ → ℤ) (i j : ℕ) : (selK lab i j).length ≤ j := by
  have := List.length_filter_le (fun k : ℕ => decide (i ≤ k ∧ lab k = (i : ℤ))) (List.range j)
  simpa [selK] using this

set_option maxHeartbeats 1000000 in
lemma k1_loop (Q : Program) (off NODE : ℕ) (hE : Embeds Q (seg14 off NODE) off) (n i : ℕ)
    (lab vals : ℕ → ℤ) (Zn Sa Lo : ℤ) (hZn : Zn ≤ 0) (hLo : Sa + n ≤ Lo) (hSa : 0 ≤ Sa) :
    ∀ d j, j + d = n → i ≤ j → ∀ s : State, s.core.pc = off + 10 → s.halted = false →
      s.core.ptrs 11 = n → s.core.ptrs 22 = j → s.core.ptrs 3 = i → s.core.ptrs 20 = Zn →
      s.core.ptrs 10 = Sa → s.core.ptrs 25 = Lo → s.core.ptrs 24 = (selK lab i j).length →
      (∀ k : ℕ, k < n → s.integerMemory (Zn - 1 - k) = lab k) →
      (∀ k : ℕ, k < n → s.integerMemory (Sa + k) = vals k) →
      (∀ k (hk : k < (selK lab i j).length), s.integerMemory (Lo + k) = vals ((selK lab i j)[k])) →
      ∃ t, t ≤ 13 * d + 1 ∧ (run Q s detTape t).core.pc = off + 25 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 24 = (selK lab i n).length ∧
        (∀ k (hk : k < (selK lab i n).length),
          (run Q s detTape t).integerMemory (Lo + k) = vals ((selK lab i n)[k])) ∧
        (∀ z, (z < Lo ∨ Lo + n ≤ z) → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ x, x ∉ [6, 7, 22, 24, 31] → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).work = s.work + t ∧
        (∀ c ∈ cellsWritten Q s t, c.1 = false ∧ Lo ≤ c.2 ∧ c.2 < Lo + (selK lab i n).length) := by
  intro d
  induction d with
  | zero =>
    intro j hj _ s hpc hh h11 h22 _ _ _ _ h24 _ _ hw
    simp only [Nat.add_zero] at hj; subst hj
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h22 h24 hw; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h22]), run_zero, cw_zero]
    exact ⟨rfl, rfl, h24, hw, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, by simp⟩
  | succ d ih =>
    intro j hj hij s hpc hh h11 h22 h3 h20 h10 h25 h24 hlab hval hw
    have hjn : j < n := by omega
    have hlen := selK_len_le lab i j
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h22 h3 h20 h10 h25 h24 hlab hval hw; subst hpc hh
    have hl : im (ptrs 20 - (j : ℤ) - 1) = lab j := by
      rw [h20, show Zn - (j : ℤ) - 1 = Zn - 1 - j by ring]; exact hlab j hjn
    have hv : im (ptrs 10 + (j : ℤ)) = vals j := by rw [h10]; exact hval j hjn
    have step : ∃ u, u ≤ 13 ∧
        (run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.pc = off + 10 ∧
        (run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).halted = false ∧
        (run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.ptrs 22 = (j + 1 : ℕ) ∧
        (run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.ptrs 24 =
          (selK lab i (j + 1)).length ∧
        (run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).integerMemory =
          (if lab j = (i : ℤ) then Function.update im (Lo + (selK lab i j).length) (vals j) else im) ∧
        (∀ x, x ∉ [6, 7, 22, 24, 31] →
          (run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.ptrs x = ptrs x) ∧
        (run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.regs = regs ∧
        (run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.mem = mem ∧
        (run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).work = w + u ∧
        (∀ c ∈ cellsWritten Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ u,
          c = (false, Lo + (selK lab i j).length) ∧ lab j = (i : ℤ)) := by
      have hlen1 : ((selK lab i (j + 1)).length : ℤ) =
          (selK lab i j).length + (if lab j = (i : ℤ) then 1 else 0) := by
        rw [selK_succ, List.length_append]
        by_cases h : lab j = (i : ℤ)
        · rw [if_pos ⟨hij, h⟩, if_pos h]; simp
        · rw [if_neg (fun h' => h h'.2), if_neg h]; simp
      rcases lt_trichotomy (lab j) (i : ℤ) with hlt | heq | hgt
      · -- `lab j < i`: two tests, skip
        refine ⟨9, by omega, ?_⟩
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]
        rw [if_neg (by rw [h11, h22]; push_cast; omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, h22, h3, hl]
        rw [if_pos hlt.le]
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, h22, h3, hl]
        rw [if_neg (by omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]; rw [if_pos le_rfl, run_zero, cw_zero]
        clear hE
        refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, by simp⟩
        · simp [h22]
        · simp [h24, hlen1, hlt.ne]
        · rw [if_neg hlt.ne]
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp (config := {decide := true}) [Function.update_apply, hx]
      · -- `lab j = i`: select
        refine ⟨13, le_rfl, ?_⟩
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]
        rw [if_neg (by rw [h11, h22]; push_cast; omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, h22, h3, hl]
        rw [if_pos heq.le]
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, h22, h3, hl]
        rw [if_pos heq.ge]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]; rw [if_pos le_rfl, run_zero, cw_zero]
        clear hE
        refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
        · simp [h22]
        · simp [h24, hlen1, heq]
        · rw [if_pos heq]; simp [h25, h24, h10, h22, hval j hjn]
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp (config := {decide := true}) [Function.update_apply, hx]
        · intro c hc
          simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
            Finset.mem_union, Finset.mem_singleton] at hc
          subst hc; exact ⟨by simp [h25, h24], heq⟩
      · -- `lab j > i`: one test, skip
        refine ⟨8, by omega, ?_⟩
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]
        rw [if_neg (by rw [h11, h22]; push_cast; omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, h22, h3, hl]
        rw [if_neg (by omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]; rw [if_pos le_rfl, run_zero, cw_zero]
        clear hE
        refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, by simp⟩
        · simp [h22]
        · simp [h24, hlen1, hgt.ne']
        · rw [if_neg hgt.ne']
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp (config := {decide := true}) [Function.update_apply, hx]
    obtain ⟨u, hu, a1, a2, a3, a4, a5, a6, a7, a8, aw, acw⟩ := step
    set S1 := run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u with hS1
    have fr : ∀ z, z ≠ Lo + (selK lab i j).length → S1.integerMemory z = im z := by
      intro z hz; rw [a5]; split_ifs <;> simp [Function.update_apply, hz]
    obtain ⟨t2, ht2, b1, b2, b3, b4, b5, b6, b7, b8, bw, bcw⟩ := ih (j + 1) (by omega) (by omega) S1 a1 a2
      (by rw [a6 11 (by simp)]; exact h11) a3 (by rw [a6 3 (by simp)]; exact h3)
      (by rw [a6 20 (by simp)]; exact h20) (by rw [a6 10 (by simp)]; exact h10)
      (by rw [a6 25 (by simp)]; exact h25) a4
      (fun k hk => by rw [fr _ (by omega)]; exact hlab k hk)
      (fun k hk => by rw [fr _ (by omega)]; exact hval k hk)
      (by
        intro k hk
        rw [a5]
        by_cases hsel : lab j = (i : ℤ)
        · rw [if_pos hsel]
          have hs : selK lab i (j + 1) = selK lab i j ++ [j] := by rw [selK_succ, if_pos ⟨hij, hsel⟩]
          simp only [hs, List.length_append, List.length_singleton] at hk ⊢
          rcases Nat.lt_or_ge k (selK lab i j).length with h | h
          · rw [Function.update_of_ne (by omega), List.getElem_append_left h]; exact hw k h
          · have : k = (selK lab i j).length := by omega
            subst this
            rw [Function.update_self, List.getElem_append_right (le_refl _)]; simp
        · rw [if_neg hsel]
          have hs : selK lab i (j + 1) = selK lab i j := by
            rw [selK_succ, if_neg (fun h => hsel h.2), List.append_nil]
          simp only [hs] at hk ⊢
          exact hw k hk)
    refine ⟨u + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hS1]
    refine ⟨b1, b2, b3, b4, fun z hz => ?_, fun x hx => by rw [b6 x hx, a6 x hx], by rw [b7, a7],
      by rw [b8, a8], by rw [bw, aw]; ring, ?_⟩
    · rw [b5 z hz, fr z (by omega)]
    · intro c hc
      rcases Finset.mem_union.1 hc with h | h
      · obtain ⟨hc, hsel⟩ := acw c h
        have hm : (selK lab i (j + 1)).length ≤ (selK lab i n).length := selK_len_mono lab i (by omega)
        have hs : selK lab i (j + 1) = selK lab i j ++ [j] := by rw [selK_succ, if_pos ⟨hij, hsel⟩]
        rw [hs, List.length_append] at hm
        subst hc; simp only [List.length_singleton] at hm; simp; omega
      · exact bcw c h

set_option maxHeartbeats 1000000 in
lemma k2_loop (Q : Program) (off NODE : ℕ) (hE : Embeds Q (seg14 off NODE) off) (n i : ℕ)
    (lab : ℕ → ℤ) (Zn Kd u : ℤ) (hZn : Zn ≤ 0) (hKd : 0 ≤ Kd) :
    ∀ d j, j + d = n → i ≤ j → ∀ s : State, s.core.pc = off + 35 → s.halted = false →
      s.core.ptrs 11 = n → s.core.ptrs 22 = j → s.core.ptrs 3 = i → s.core.ptrs 20 = Zn →
      s.core.ptrs 19 = Kd → s.core.ptrs 26 = u →
      (∀ k : ℕ, k < n → s.integerMemory (Zn - 1 - k) = lab k) →
      ∃ t, t ≤ 10 * d + 1 ∧ (run Q s detTape t).core.pc = off + 47 ∧
        (run Q s detTape t).halted = false ∧
        (∀ k : ℕ, j ≤ k → k < n → (run Q s detTape t).integerMemory (Kd + k) =
          if lab k = (i : ℤ) then u else s.integerMemory (Kd + k)) ∧
        (∀ z, (z < Kd + j ∨ Kd + n ≤ z) → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ x, x ∉ [6, 22, 31] → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).work = s.work + t ∧
        (∀ c ∈ cellsWritten Q s t, c.1 = false ∧ Kd + j ≤ c.2 ∧ c.2 < Kd + n) := by
  intro d
  induction d with
  | zero =>
    intro j hj _ s hpc hh h11 h22 _ _ _ _ _
    simp only [Nat.add_zero] at hj; subst hj
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h22; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h22]), run_zero, cw_zero]
    exact ⟨rfl, rfl, fun k h1 h2 => by omega, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, by simp⟩
  | succ d ih =>
    intro j hj hij s hpc hh h11 h22 h3 h20 h19 h26 hlab
    have hjn : j < n := by omega
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h22 h3 h20 h19 h26 hlab; subst hpc hh
    have hl : im (ptrs 20 - (j : ℤ) - 1) = lab j := by
      rw [h20, show Zn - (j : ℤ) - 1 = Zn - 1 - j by ring]; exact hlab j hjn
    have step : ∃ v, v ≤ 10 ∧
        (run Q ⟨⟨off + 35, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape v).core.pc = off + 35 ∧
        (run Q ⟨⟨off + 35, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape v).halted = false ∧
        (run Q ⟨⟨off + 35, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape v).core.ptrs 22 = (j + 1 : ℕ) ∧
        (run Q ⟨⟨off + 35, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape v).integerMemory =
          (if lab j = (i : ℤ) then Function.update im (Kd + j) u else im) ∧
        (∀ x, x ∉ [6, 22, 31] →
          (run Q ⟨⟨off + 35, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape v).core.ptrs x = ptrs x) ∧
        (run Q ⟨⟨off + 35, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape v).core.regs = regs ∧
        (run Q ⟨⟨off + 35, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape v).core.mem = mem ∧
        (run Q ⟨⟨off + 35, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape v).work = w + v ∧
        cellsWritten Q ⟨⟨off + 35, regs, ptrs, mem⟩, im, cur, false, w⟩ v ⊆ {(false, Kd + j)} := by
      rcases lt_trichotomy (lab j) (i : ℤ) with hlt | heq | hgt
      · refine ⟨9, by omega, ?_⟩
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]
        rw [if_neg (by rw [h11, h22]; push_cast; omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, h22, h3, hl]
        rw [if_pos hlt.le]
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, h22, h3, hl]
        rw [if_neg (by omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]; rw [if_pos le_rfl, run_zero, cw_zero]
        clear hE
        refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, by simp⟩
        · simp [h22]
        · rw [if_neg hlt.ne]
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp (config := {decide := true}) [Function.update_apply, hx]
      · refine ⟨10, le_rfl, ?_⟩
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]
        rw [if_neg (by rw [h11, h22]; push_cast; omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, h22, h3, hl]
        rw [if_pos heq.le]
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, h22, h3, hl]
        rw [if_pos heq.ge]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]; rw [if_pos le_rfl, run_zero, cw_zero]
        clear hE
        refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
        · simp [h22]
        · rw [if_pos heq]; simp [h19, h22, h26]
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp (config := {decide := true}) [Function.update_apply, hx]
        · intro c hc
          simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
            Finset.mem_union, Finset.mem_singleton] at hc
          subst hc; simp [h19, h22]
      · refine ⟨8, by omega, ?_⟩
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]
        rw [if_neg (by rw [h11, h22]; push_cast; omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, h22, h3, hl]
        rw [if_neg (by omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]; rw [if_pos le_rfl, run_zero, cw_zero]
        clear hE
        refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, by simp⟩
        · simp [h22]
        · rw [if_neg hgt.ne']
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp (config := {decide := true}) [Function.update_apply, hx]
    obtain ⟨v, hv, a1, a2, a3, a5, a6, a7, a8, aw, acw⟩ := step
    set S1 := run Q ⟨⟨off + 35, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape v with hS1
    have fr : ∀ z, z ≠ Kd + j → S1.integerMemory z = im z := by
      intro z hz; rw [a5]; split_ifs <;> simp [Function.update_apply, hz]
    obtain ⟨t2, ht2, b1, b2, b4, b5, b6, b7, b8, bw, bcw⟩ := ih (j + 1) (by omega) (by omega) S1 a1 a2
      (by rw [a6 11 (by simp)]; exact h11) a3 (by rw [a6 3 (by simp)]; exact h3)
      (by rw [a6 20 (by simp)]; exact h20) (by rw [a6 19 (by simp)]; exact h19)
      (by rw [a6 26 (by simp)]; exact h26)
      (fun k hk => by rw [fr _ (by omega)]; exact hlab k hk)
    refine ⟨v + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hS1]
    refine ⟨b1, b2, fun k hk1 hk2 => ?_, fun z hz => ?_, fun x hx => by rw [b6 x hx, a6 x hx],
      by rw [b7, a7], by rw [b8, a8], by rw [bw, aw]; ring, ?_⟩
    · rcases Nat.lt_or_ge j k with h | h
      · rw [b4 k (by omega) hk2, fr _ (by omega)]
      · have : k = j := by omega
        subst this
        rw [b5 _ (Or.inl (by push_cast; omega)), a5]
        split_ifs with hs <;> simp
    · rw [b5 z (by push_cast at hz ⊢; omega), fr z (by omega)]
    · intro c hc
      rcases Finset.mem_union.1 hc with h | h
      · have := acw h
        simp only [Finset.mem_singleton] at this
        subst this; simp; omega
      · obtain ⟨e1, e2, e3⟩ := bcw c h
        exact ⟨e1, by push_cast at e2; omega, e3⟩

end DetANN.HPIM.PP

-- ===== PP_NodeHead =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

lemma GInv.transfer {s s' : State} (g : GInv Y δ T0 v0 s)
    (hp : ∀ x ∈ [1, 12, 23], s'.core.ptrs x = s.core.ptrs x)
    (hr : ∀ x ∈ [0, 1, 2, 20, 21, 22], s'.core.regs x = s.core.regs x)
    (hIM : ∀ z, 0 ≤ z → z < Hbase N T0 → s'.integerMemory z = s.integerMemory z)
    (hmem : ∀ z : ℤ, 0 ≤ z → z < 1 + (N : ℤ) * m → s'.core.mem z = s.core.mem z) :
    GInv Y δ T0 v0 s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp 1 (by simp)]; exact g.pm
  · rw [hp 12 (by simp)]; exact g.pPA
  · rw [hp 23 (by simp)]; exact g.pN
  · rw [hr 0 (by simp)]; exact g.r0
  · rw [hr 1 (by simp)]; exact g.r1
  · rw [hr 2 (by simp)]; exact g.r2
  · rw [hr 20 (by simp)]; exact g.r20
  · rw [hr 21 (by simp)]; exact g.r21
  · rw [hr 22 (by simp)]; exact g.r22
  · rw [hIM 1 (by norm_num) (by unfold Hbase; omega)]; exact g.i1
  · rw [hIM 2 (by norm_num) (by unfold Hbase; omega)]; exact g.i2
  · rw [hIM 3 (by norm_num) (by unfold Hbase; omega)]; exact g.i3
  · intro gg
    rw [hIM _ (by positivity) (by unfold Hbase; have := gg.isLt; omega)]; exact g.pa gg
  · intro t ht
    rw [hIM _ (by positivity) (by unfold Hbase; omega)]; exact g.pow t ht
  · intro gg j
    have h1 : (gg : ℤ) * m + j < N * m := by
      have : (gg : ℤ) + 1 ≤ N := by exact_mod_cast gg.isLt
      have : (j : ℤ) < m := by exact_mod_cast j.isLt
      nlinarith
    rw [hmem _ (by positivity) (by linarith)]; exact g.pts gg j

end DetANN.HPIM.PP

-- ===== PP_KidPush =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

set_option maxHeartbeats 2000000 in
/-- The frame push (offsets 47–75): ten cells at `F = Zn − n − 10`, then the call. -/
lemma kid_push (Q : Program) (off NODE : ℕ) (hE : Embeds Q (seg14 off NODE) off) (s : State)
    (hpc : s.core.pc = off + 47) (hh : s.halted = false) (Zn : ℤ) (n : ℕ)
    (r20 : s.core.ptrs 20 = Zn) (r11 : s.core.ptrs 11 = n) :
    (run Q s detTape 29).core.pc = NODE ∧ (run Q s detTape 29).halted = false ∧
      (run Q s detTape 29).core.ptrs 2 = s.core.ptrs 26 ∧
      (run Q s detTape 29).core.ptrs 13 = Zn - n - 10 ∧
      (run Q s detTape 29).core.ptrs 14 = s.core.ptrs 28 ∧
      (run Q s detTape 29).core.ptrs 8 = Zn - n - 10 ∧
      (∀ x, x ∉ [2, 6, 7, 8, 9, 13, 14, 27] → (run Q s detTape 29).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 29).core.regs = s.core.regs ∧ (run Q s detTape 29).core.mem = s.core.mem ∧
      (∀ k : Fin 10, (run Q s detTape 29).integerMemory (Zn - n - 10 + k) =
        ![1, s.core.ptrs 2, s.core.ptrs 3, s.core.ptrs 11, s.core.ptrs 10, s.core.ptrs 20,
          s.core.ptrs 19, s.core.ptrs 21, s.core.ptrs 8, s.core.ptrs 28] k) ∧
      (∀ z, (z < Zn - n - 10 ∨ Zn - n ≤ z) → (run Q s detTape 29).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 29).work = s.work + 29 ∧
      (∀ c' ∈ cellsWritten Q s 29, c'.1 = false ∧ Zn - n - 10 ≤ c'.2 ∧ c'.2 < Zn - n) := by
  obtain ⟨⟨pc, ptrs3', ptrs3, mem3⟩, im3, cur3, hlt3, w3⟩ := s
  simp only at hpc hh r20 r11; subst pc hh
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, rfl, ?_⟩
  · simp
  · simp [r20, r11]
  · simp
  · simp [r20, r11]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp (config := {decide := true}) [Function.update_apply, hx]
  · intro k
    simp only [Function.update_apply, r20, r11]
    generalize Zn - (n : ℤ) - 10 = F
    fin_cases k <;> simp [add_assoc]
  · intro z hz
    simp only [Function.update_apply, r20, r11]
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro c' hc'
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc'
    rcases hc' with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [r20, r11] <;> omega

end DetANN.HPIM.PP

-- ===== PP_KidPre =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

lemma selK_self (lab : ℕ → ℤ) (i : ℕ) : selK lab i i = [] := by
  unfold selK
  rw [List.filter_eq_nil_iff]
  intro a ha; simp only [List.mem_range] at ha; simp; omega

/-- The frame pushed for a call, from the caller's registers. -/
def frameOf (s : State) : Fin 10 → ℤ :=
  ![1, s.core.ptrs 2, s.core.ptrs 3, s.core.ptrs 11, s.core.ptrs 10, s.core.ptrs 20, s.core.ptrs 19,
    s.core.ptrs 21, s.core.ptrs 8, s.core.ptrs 28]

set_option maxHeartbeats 2000000 in
lemma kid_pre (Q : Program) (off NODE : ℕ) (hE : Embeds Q (seg14 off NODE) off) (n i : ℕ)
    (lab vals : ℕ → ℤ) (Zn Sa Kd Lo : ℤ) (s : State) (hpc : s.core.pc = off + 1)
    (hh : s.halted = false) (h3 : s.core.ptrs 3 = i) (h11 : s.core.ptrs 11 = n) (hin : i < n)
    (h20 : s.core.ptrs 20 = Zn) (h10 : s.core.ptrs 10 = Sa) (h19 : s.core.ptrs 19 = Kd)
    (h15 : s.core.ptrs 15 = Lo) (hrep : lab i = (i : ℤ))
    (hlab : ∀ k : ℕ, k < n → s.integerMemory (Zn - 1 - k) = lab k)
    (hval : ∀ k : ℕ, k < n → s.integerMemory (Sa + k) = vals k)
    (hZn : Zn ≤ 0) (hSa : 0 ≤ Sa) (hSK : Sa + n ≤ Kd) (hKL : Kd + n ≤ Lo) :
    ∃ t, t ≤ 23 * n + 49 ∧ (run Q s detTape t).core.pc = NODE ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 2 = Lo + (selK lab i n).length ∧
      (run Q s detTape t).core.ptrs 13 = Zn - n - 10 ∧
      (run Q s detTape t).core.ptrs 14 = s.core.ptrs 28 ∧
      (run Q s detTape t).core.ptrs 8 = Zn - n - 10 ∧
      (run Q s detTape t).core.ptrs 15 = Lo + (selK lab i n).length + 8 ∧
      (∀ x, x ∉ [2, 6, 7, 8, 9, 13, 14, 15, 22, 24, 25, 26, 27, 30, 31] →
        (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (∀ k (hk : k < (selK lab i n).length),
        (run Q s detTape t).integerMemory (Lo + k) = vals ((selK lab i n)[k])) ∧
      (run Q s detTape t).integerMemory (Lo + (selK lab i n).length + 3) = Lo ∧
      (run Q s detTape t).integerMemory (Lo + (selK lab i n).length + 7) = (selK lab i n).length ∧
      (∀ k : ℕ, i ≤ k → k < n → (run Q s detTape t).integerMemory (Kd + k) =
        if lab k = (i : ℤ) then Lo + (selK lab i n).length else s.integerMemory (Kd + k)) ∧
      FrameAt (run Q s detTape t) (Zn - n - 10) (frameOf s) ∧
      (∀ z, (z < Zn - n - 10 ∨ (Zn - n ≤ z ∧ z < Kd + i) ∨ (Kd + n ≤ z ∧ z < Lo) ∨ Lo + n + 8 ≤ z) →
        (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape t).work = s.work + t ∧
      (∀ c ∈ cellsWritten Q s t, c.1 = false ∧ ((Lo ≤ c.2 ∧ c.2 < Lo + (selK lab i n).length + 8) ∨
        (Kd + i ≤ c.2 ∧ c.2 < Kd + n) ∨ (Zn - n - 10 ≤ c.2 ∧ c.2 < Zn - n))) := by
  have hKd : 0 ≤ Kd := by omega
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h3 h11 h20 h10 h19 h15 hlab hval; subst pc hh
  have hl : im (ptrs 20 - (i : ℤ) - 1) = lab i := by
    rw [h20, show Zn - (i : ℤ) - 1 = Zn - 1 - i by ring]; exact hlab i hin
  -- Stage A: offsets 1–9
  set S0 := run Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 8 with hS0
  have e0 : S0.core.pc = off + 10 ∧ S0.halted = false ∧ S0.core.ptrs 22 = i ∧ S0.core.ptrs 25 = Lo ∧
      S0.core.ptrs 24 = 0 ∧ (∀ x, x ∉ [6, 22, 24, 25, 30] → S0.core.ptrs x = ptrs x) ∧
      S0.core.regs = regs ∧ S0.core.mem = mem ∧ S0.integerMemory = im ∧ S0.work = w + 8 ∧
      cellsWritten Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ 8 = ∅ := by
    rw [hS0, run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_neg (by rw [h11, h3]; push_cast; omega)]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
      if_false, h3, hl]
    rw [if_pos (by rw [hrep])]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    clear hE
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, by simp⟩
    · simp [h3]
    · simp [h15]
    · simp
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp (config := {decide := true}) [Function.update_apply, hx]
  obtain ⟨a1, a2, a22, a25, a24, aP, aR, aM, aI, aw, acw⟩ := e0
  -- K1
  obtain ⟨t1, ht1, b1, b2, b24, bL, bI, bP, bR, bM, bw, bcw⟩ :=
    k1_loop Q off NODE hE n i lab vals Zn Sa Lo hZn (by omega) hSa (n - i) i (by omega) le_rfl S0 a1 a2
      (by rw [aP 11 (by simp)]; exact h11) a22 (by rw [aP 3 (by simp)]; exact h3)
      (by rw [aP 20 (by simp)]; exact h20) (by rw [aP 10 (by simp)]; exact h10) a25
      (by rw [a24, selK_self]; rfl) (by rw [aI]; exact hlab) (by rw [aI]; exact hval)
      (by intro k hk; rw [selK_self] at hk; simp at hk)
  set c := (selK lab i n).length with hc
  have hcn : c ≤ n := selK_len_le lab i n
  generalize hS1 : run Q S0 detTape t1 = S1 at b1 b2 b24 bL bI bP bR bM bw
  obtain ⟨⟨pc1, regs1, ptrs1, mem1⟩, im1, cur1, hlt1, w1⟩ := S1
  simp only at b1 b2 b24 bL bI bP bR bM bw; subst b1 b2
  have q25 : ptrs1 25 = Lo := by rw [bP 25 (by simp)]; exact a25
  have q3 : ptrs1 3 = i := by rw [bP 3 (by simp), aP 3 (by simp)]; exact h3
  -- Stage B: offsets 25–34
  set S2 := run Q ⟨⟨off + 25, regs1, ptrs1, mem1⟩, im1, cur1, false, w1⟩ detTape 10 with hS2
  have e2 : S2.core.pc = off + 35 ∧ S2.halted = false ∧ S2.core.ptrs 26 = Lo + c ∧
      S2.core.ptrs 15 = Lo + c + 8 ∧ S2.core.ptrs 22 = i ∧
      (∀ x, x ∉ [6, 15, 22, 26, 27] → S2.core.ptrs x = ptrs1 x) ∧ S2.core.regs = regs1 ∧
      S2.core.mem = mem1 ∧
      S2.integerMemory = Function.update (Function.update im1 (Lo + c + 3) Lo) (Lo + c + 7) c ∧
      S2.work = w1 + 10 ∧
      cellsWritten Q ⟨⟨off + 25, regs1, ptrs1, mem1⟩, im1, cur1, false, w1⟩ 10 ⊆
        {(false, Lo + c + 3), (false, Lo + c + 7)} := by
    rw [hS2]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    clear hE
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl, ?_⟩
    · simp [q25, b24]
    · simp [q25, b24]
    · simp [q3]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp (config := {decide := true}) [Function.update_apply, hx]
    · simp [q25, b24]
    · intro c' hc'
      simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
        Finset.mem_union, Finset.mem_singleton] at hc'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hc' with h | h <;> subst h <;> simp [q25, b24]
  obtain ⟨d1, d2, d26, d15, d22, dP, dR, dM, dI, dw, dcw⟩ := e2
  have fI2 : ∀ z, z < Lo → S2.integerMemory z = im z := by
    intro z hz
    rw [dI, Function.update_of_ne (by omega), Function.update_of_ne (by omega), bI z (Or.inl hz), aI]
  have p2P : ∀ x, x ∉ [6, 7, 15, 22, 24, 25, 26, 27, 30, 31] → S2.core.ptrs x = ptrs x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [dP x (by simp; omega), bP x (by simp; omega), aP x (by simp; omega)]
  -- K2
  obtain ⟨t3, ht3, f1, f2, fK, fI, fP, fR, fM, fw, fcw⟩ :=
    k2_loop Q off NODE hE n i lab Zn Kd (Lo + c) hZn hKd (n - i) i (by omega) le_rfl S2 d1 d2
      (by rw [p2P 11 (by simp)]; exact h11) d22 (by rw [p2P 3 (by simp)]; exact h3)
      (by rw [p2P 20 (by simp)]; exact h20) (by rw [p2P 19 (by simp)]; exact h19) d26
      (fun k hk => by rw [fI2 _ (by omega)]; exact hlab k hk)
  generalize hS3 : run Q S2 detTape t3 = S3 at f1 f2 fK fI fP fR fM fw
  obtain ⟨⟨pc3, regs3, ptrs3, mem3⟩, im3, cur3, hlt3, w3⟩ := S3
  simp only at f1 f2 fK fI fP fR fM fw; subst f1 f2
  have p3P : ∀ x, x ∉ [6, 7, 15, 22, 24, 25, 26, 27, 30, 31] → ptrs3 x = ptrs x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [fP x (by simp; omega), p2P x (by simp; omega)]
  have r20 : ptrs3 20 = Zn := by rw [p3P 20 (by simp)]; exact h20
  have r11 : ptrs3 11 = n := by rw [p3P 11 (by simp)]; exact h11
  have r26 : ptrs3 26 = Lo + c := by rw [fP 26 (by simp)]; exact d26
  -- Stage C: offsets 47–75
  obtain ⟨g1, g2, g2', g13, g14, g8, gP, gR, gM, gF, gI, gw, gcw⟩ :=
    kid_push Q off NODE hE ⟨⟨off + 47, regs3, ptrs3, mem3⟩, im3, cur3, false, w3⟩ rfl rfl Zn n r20 r11
  simp only at g2' g14 gP gR gM gF gI gw
  set S4 := run Q ⟨⟨off + 47, regs3, ptrs3, mem3⟩, im3, cur3, false, w3⟩ detTape 29 with hS4
  refine ⟨8 + t1 + 10 + t3 + 29, by omega, ?_⟩
  have R1 : run Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape (8 + t1) =
      ⟨⟨off + 25, regs1, ptrs1, mem1⟩, im1, cur1, false, w1⟩ := by rw [run_add, ← hS0, hS1]
  have R2 : run Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape (8 + t1 + 10) = S2 := by
    rw [run_add, R1]
  have R3 : run Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape (8 + t1 + 10 + t3) =
      ⟨⟨off + 47, regs3, ptrs3, mem3⟩, im3, cur3, false, w3⟩ := by rw [run_add, R2, hS3]
  have R : run Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape (8 + t1 + 10 + t3 + 29) = S4 := by
    rw [run_add, R3]
  have CW : cellsWritten Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ (8 + t1 + 10 + t3 + 29) =
      cellsWritten Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ 8 ∪ cellsWritten Q S0 t1 ∪
        cellsWritten Q ⟨⟨off + 25, regs1, ptrs1, mem1⟩, im1, cur1, false, w1⟩ 10 ∪
        cellsWritten Q S2 t3 ∪ cellsWritten Q ⟨⟨off + 47, regs3, ptrs3, mem3⟩, im3, cur3, false, w3⟩ 29 := by
    rw [cellsWritten_add, R3, cellsWritten_add, R2, cellsWritten_add, R1, cellsWritten_add, ← hS0]
  rw [R, CW]
  have I4 : ∀ z, (z < Zn - n - 10 ∨ (Zn - n ≤ z ∧ z < Kd + i) ∨ (Kd + n ≤ z ∧ z < Lo) ∨
      Lo + n + 8 ≤ z) → S4.integerMemory z = im z := by
    intro z hz
    rw [gI z (by omega), fI z (by omega), dI, Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), bI z (by omega), aI]
  refine ⟨g1, g2, by rw [g2', r26], g13, by rw [g14, p3P 28 (by simp)], g8,
    by rw [gP 15 (by simp), fP 15 (by simp), d15], fun x hx => ?_, by rw [gR, fR, dR, bR, aR],
    by rw [gM, fM, dM, bM, aM], fun k hk => ?_, ?_, ?_, fun k hk1 hk2 => ?_, fun k => ?_, I4,
    by rw [gw, fw, dw, bw, aw]; ring, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [gP x (by simp; omega), p3P x (by simp; omega)]
  · rw [gI _ (by omega), fI _ (by omega), dI, Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact bL k hk
  · rw [gI _ (by omega), fI _ (by omega), dI, Function.update_of_ne (by omega), Function.update_self]
  · rw [gI _ (by omega), fI _ (by omega), dI, Function.update_self]
  · rw [gI _ (by omega), fK k hk1 hk2, fI2 _ (by omega)]
  · rw [gF k]
    fin_cases k <;> simp [frameOf, p3P 2 (by simp), p3P 3 (by simp), p3P 11 (by simp),
      p3P 10 (by simp), p3P 20 (by simp), p3P 19 (by simp), p3P 21 (by simp), p3P 8 (by simp),
      p3P 28 (by simp)]
  · intro c' hc'
    simp only [Finset.mem_union] at hc'
    rcases hc' with (((h | h) | h) | h) | h
    · rw [acw] at h; simp at h
    · obtain ⟨e1, e2, e3⟩ := bcw c' h; exact ⟨e1, Or.inl ⟨e2, by omega⟩⟩
    · have := dcw h
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h' <;> subst h' <;> exact ⟨rfl, Or.inl ⟨by omega, by omega⟩⟩
    · obtain ⟨e1, e2, e3⟩ := fcw c' h; exact ⟨e1, Or.inr (Or.inl ⟨e2, e3⟩)⟩
    · obtain ⟨e1, e2, e3⟩ := gcw c' h; exact ⟨e1, Or.inr (Or.inr ⟨e2, e3⟩)⟩

end DetANN.HPIM.PP

-- ===== PP_KidPost =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

lemma ret_resume_cw (Q : Program) (off KN : ℕ) (hE : Embeds Q (seg14 off KN) off) (s : State)
    (hpc : s.core.pc = off + 82) (hh : s.halted = false) (hc : 1 ≤ s.integerMemory (s.core.ptrs 8)) :
    cellsWritten Q s 24 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hc; subst hpc hh
  (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [cw_exec_at hE rfl rfl rfl]
  simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none,
    Finset.empty_union, Function.update_apply, if_true, if_false]
  rw [if_neg (by omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  (rw [cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Option.toFinset_none, Finset.empty_union, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  exact cw_zero _ _

/-- `RETURN` with a code-1 frame, then `KN: p3 += 1`, back to the loop head `off + 1`. -/
lemma kid_post (Q : Program) (off KN : ℕ) (hE : Embeds Q (seg14 off KN) off) (s : State)
    (hpc : s.core.pc = off + 82) (hh : s.halted = false) (fr : Fin 10 → ℤ)
    (hF : FrameAt s (s.core.ptrs 8) fr) (hc : fr 0 = 1) :
    (run Q s detTape 26).core.pc = off + 1 ∧ (run Q s detTape 26).halted = false ∧
      (run Q s detTape 26).core.ptrs 3 = fr 2 + 1 ∧
      (∀ k : Fin 10, k ≠ 0 → k ≠ 2 → (run Q s detTape 26).core.ptrs (frameRegs k) = fr k) ∧
      (∀ x, x ∉ [2, 3, 11, 10, 20, 19, 21, 8, 28, 6, 27, 9] →
        (run Q s detTape 26).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 26).core.regs = s.core.regs ∧
      (run Q s detTape 26).integerMemory = s.integerMemory ∧
      (run Q s detTape 26).core.mem = s.core.mem ∧ (run Q s detTape 26).work = s.work + 26 ∧
      cellsWritten Q s 26 = ∅ := by
  have hfr3 : ∀ k : Fin 10, k ≠ 2 → frameRegs k ≠ 3 := by decide
  have hc0 : 1 ≤ s.integerMemory (s.core.ptrs 8) := by
    have := hF 0; simp only [Fin.val_zero, Nat.cast_zero, add_zero] at this; rw [this, hc]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, aw⟩ := ret_resume Q off KN hE s hpc hh fr hF (by rw [hc])
  have acw := ret_resume_cw Q off KN hE s hpc hh hc0
  generalize hS1 : run Q s detTape 24 = S1 at a1 a2 a3 a4 a5 a6 a7 aw
  have R : run Q s detTape 26 = run Q S1 detTape 2 := by rw [show 26 = 24 + 2 from rfl, run_add, hS1]
  have CW : cellsWritten Q s 26 = cellsWritten Q s 24 ∪ cellsWritten Q S1 2 := by
    rw [show 26 = 24 + 2 from rfl, cellsWritten_add, hS1]
  rw [R, CW, acw]
  obtain ⟨⟨pc1, regs1, ptrs1, mem1⟩, im1, cur1, hlt1, w1⟩ := S1
  simp only at a1 a2 a3 a4 a5 a6 a7 aw; subst a1 a2
  have p3 : ptrs1 3 = fr 2 := a3 2 (by decide)
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨rfl, rfl, by simp [p3], fun k hk hk2 => ?_, fun x hx => ?_, a5, a6, a7, ?_, ?_⟩
  · have := a3 k hk
    simp only [Function.update_apply, if_neg (hfr3 k hk2), this]
  · have h3 : x ≠ 3 := by intro h; subst h; simp at hx
    simp [Function.update_apply, h3, a4 x hx]
  · rw [aw]
  · simp

/-- A non-representative index: skip it. -/
lemma kid_skip (Q : Program) (off KN : ℕ) (hE : Embeds Q (seg14 off KN) off) (s : State) (n i : ℕ)
    (lab : ℕ → ℤ) (Zn : ℤ) (hpc : s.core.pc = off + 1) (hh : s.halted = false)
    (h3 : s.core.ptrs 3 = i) (h11 : s.core.ptrs 11 = n) (hin : i < n) (h20 : s.core.ptrs 20 = Zn)
    (hl : s.integerMemory (Zn - 1 - i) = lab i) (hlt : lab i < i) :
    (run Q s detTape 8).core.pc = off + 1 ∧ (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 3 = (i + 1 : ℕ) ∧
      (∀ x, x ∉ [3, 6, 30] → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs = s.core.regs ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).work = s.work + 8 ∧
      cellsWritten Q s 8 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt', w⟩ := s
  simp only at hpc hh h3 h11 h20 hl; subst pc hh
  have hl' : im (ptrs 20 - (i : ℤ) - 1) = lab i := by
    rw [h20, show Zn - (i : ℤ) - 1 = Zn - 1 - i by ring]; exact hl
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_neg (by rw [h11, h3]; push_cast; omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
    if_false, h3, hl']
  rw [if_neg (by omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, by simp⟩
  · simp [h3]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp (config := {decide := true}) [Function.update_apply, hx]

/-- The end of the kids loop (`i = n`): the tail call on the representatives' record `vr`. -/
lemma kid_exit (Q : Program) (off KN : ℕ) (hE : Embeds Q (seg14 off KN) off) (s : State) (n : ℕ)
    (hpc : s.core.pc = off + 1) (hh : s.halted = false) (h3 : s.core.ptrs 3 = n)
    (h11 : s.core.ptrs 11 = n) :
    (run Q s detTape 5).core.pc = KN ∧ (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 2 = s.core.ptrs 21 ∧
      (run Q s detTape 5).core.ptrs 13 = s.core.ptrs 20 ∧
      (run Q s detTape 5).core.ptrs 14 = s.core.ptrs 28 ∧
      (∀ x, x ∉ [2, 13, 14] → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧ (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt', w⟩ := s
  simp only at hpc hh h3 h11; subst pc hh
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_pos (by rw [h11, h3])]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, by simp⟩
  · simp
  · simp
  · simp
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp (config := {decide := true}) [Function.update_apply, hx]

end DetANN.HPIM.PP

-- ===== PP_KidSem =====
namespace DetANN.HPIM.PP

open PNormReg DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m))

/-- The global indices of the local points. -/
noncomputable def valsOf (S : Finset (Fin N)) (j : ℕ) : ℤ :=
  if h : j < S.card then (((S.orderEmbOfFin rfl ⟨j, h⟩ : Fin N) : ℕ) : ℤ) else 0

lemma compBotOf_eq (S : Finset (Fin N)) (j : Fin S.card) :
    compBotOf Y S j = (compSet (ptsOf Y S) (dK Y S) j).map (S.orderEmbOfFin rfl).toEmbedding := rfl

lemma rep_of_compMin (S : Finset (Fin N)) (j : Fin S.card) (i : ℕ) (hi : i < S.card)
    (h : compMin (ptsOf Y S) (dK Y S) j = i) : compMin (ptsOf Y S) (dK Y S) ⟨i, hi⟩ = i := by
  have h1 := compMin_eq_of_reach (ptsOf Y S) (dK Y S) (reach_compMin (ptsOf Y S) (dK Y S) j)
  have h2 : compMinF (ptsOf Y S) (dK Y S) j = ⟨i, hi⟩ := Fin.ext h
  rw [h2] at h1; rw [← h1, h]

lemma compBotOf_of_compMin (S : Finset (Fin N)) (j : Fin S.card) (i : ℕ) (hi : i < S.card)
    (h : compMin (ptsOf Y S) (dK Y S) j = i) : compBotOf Y S j = compBotOf Y S ⟨i, hi⟩ := by
  rw [compBotOf_eq, compBotOf_eq]
  have hr := rep_of_compMin Y S j i hi h
  have : thrReach (ptsOf Y S) (dK Y S) ⟨i, hi⟩ j := (reach_iff_compMin _ _ hr).2 h
  rw [compSet_eq _ _ this]

lemma compMin_of_compBotOf (S : Finset (Fin N)) (j j' : Fin S.card)
    (h : compBotOf Y S j = compBotOf Y S j') :
    compMin (ptsOf Y S) (dK Y S) j = compMin (ptsOf Y S) (dK Y S) j' := by
  have hm : (S.orderEmbOfFin rfl) j' ∈ compBotOf Y S j := by
    rw [h, compBotOf_eq]
    exact Finset.mem_map_of_mem _ ((mem_compSet _ _).2 (thrReach_refl _ _ _))
  rw [compBotOf_eq] at hm
  obtain ⟨a, ha, hae⟩ := Finset.mem_map.1 hm
  have : a = j' := (S.orderEmbOfFin rfl).injective hae
  subst this
  exact compMin_eq_of_reach _ _ ((mem_compSet _ _).1 ha)

lemma compBotOf_card_pos (S : Finset (Fin N)) (j : Fin S.card) : 1 ≤ (compBotOf Y S j).card := by
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty,
    compBotOf_eq]
  exact ⟨_, Finset.mem_map_of_mem _ ((mem_compSet _ _).2 (thrReach_refl _ _ _))⟩

lemma compsFrom_card_end (S : Finset (Fin N)) : compsFrom Y S S.card = ∅ := by
  unfold compsFrom
  rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro j _
  have := compMin_lt (ptsOf Y S) (dK Y S) j
  omega

lemma compsFrom_succ_nonrep (S : Finset (Fin N)) (i : ℕ) (hi : i < S.card)
    (h : compMin (ptsOf Y S) (dK Y S) ⟨i, hi⟩ ≠ i) : compsFrom Y S i = compsFrom Y S (i + 1) := by
  unfold compsFrom; congr 1; ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    rcases Nat.lt_or_ge i (compMin (ptsOf Y S) (dK Y S) j) with h' | h'
    · exact h'
    · exact absurd (rep_of_compMin Y S j i hi (by omega)) h
  · intro hj; omega

lemma compsFrom_succ_rep (S : Finset (Fin N)) (i : ℕ) (hi : i < S.card)
    (h : compMin (ptsOf Y S) (dK Y S) ⟨i, hi⟩ = i) :
    compsFrom Y S i = insert (compBotOf Y S ⟨i, hi⟩) (compsFrom Y S (i + 1)) ∧
      compBotOf Y S ⟨i, hi⟩ ∉ compsFrom Y S (i + 1) := by
  constructor
  · unfold compsFrom
    ext C
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.lt_or_ge i (compMin (ptsOf Y S) (dK Y S) j) with h' | h'
      · exact Or.inr ⟨j, h', rfl⟩
      · exact Or.inl (compBotOf_of_compMin Y S j i hi (by omega))
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨⟨i, hi⟩, by rw [h], rfl⟩
      · exact ⟨j, by omega, rfl⟩
  · unfold compsFrom
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    intro j hj he
    have := compMin_of_compBotOf Y S j ⟨i, hi⟩ he
    omega

lemma card_le_treePts (f : ℕ) (C : Finset (Fin N)) : C.card ≤ treePts Y f C := by
  cases f with
  | zero => simp [treePts]
  | succ f => unfold treePts; split_ifs <;> omega

lemma dn_child (WbI n c : ℕ) (hc : 1 ≤ c) (h2 : 2 * c ≤ n) : n + 10 + Dn WbI c ≤ Dn WbI n := by
  unfold Dn
  have h1 : Nat.clog 2 c + 1 ≤ Nat.clog 2 (2 * c) := by
    set k := Nat.clog 2 (2 * c) with hk
    have hk1 : 0 < k := Nat.clog_pos (by norm_num) (by omega)
    have hp : 2 * c ≤ 2 ^ k := Nat.le_pow_clog (by norm_num) _
    have hc' : c ≤ 2 ^ (k - 1) := by
      have : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    have := Nat.clog_le_of_le_pow hc'
    omega
  have h3 : Nat.clog 2 (2 * c) ≤ Nat.clog 2 n := Nat.clog_mono_right 2 h2
  omega

end DetANN.HPIM.PP

-- ===== PP_Kids =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

set_option maxHeartbeats 4000000 in
lemma kids_loop (B : Blocks) (hB : B.WF) (KW KH KR WbI WbR f : ℕ)
    (IH : NodeOK Y δ T0 v0 B KW KH KR WbI WbR f) (hY : Function.Injective Y)
    (S : Finset (Fin N)) (hn : 2 ≤ S.card) (hnf : S.card ≤ f + 2)
    (v Sa Zn ZRn FP Kd vr : ℤ) (hHb : Hbase N T0 ≤ Sa) (hSK : Sa + S.card ≤ Kd) (hZn : Zn ≤ 0)
    (hZRn : ZRn ≤ 0) (hWb : 10 ≤ WbI) :
    ∀ d i, i + d = S.card → ∀ s : State,
      s.core.pc = B.o14 + 1 → s.halted = false → NodeEnv Y δ T0 v0 S v Sa Zn ZRn s →
      s.core.ptrs 3 = i → s.core.ptrs 19 = Kd → s.core.ptrs 21 = vr → s.core.ptrs 8 = FP →
      (∀ k : ℕ, k < S.card → s.integerMemory (Zn - 1 - k) = labOf Y S k) →
      Kd + S.card ≤ s.core.ptrs 15 → 1 + (N : ℤ) * m ≤ s.core.ptrs 16 →
      ∃ t, (run (Blocks.prog B) s detTape t).core.pc = B.lbl_NODE ∧
        (run (Blocks.prog B) s detTape t).halted = false ∧
        GInv Y δ T0 v0 (run (Blocks.prog B) s detTape t) ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 2 = vr ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 13 = Zn ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 14 = ZRn ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 8 = FP ∧
        s.core.ptrs 15 ≤ (run (Blocks.prog B) s detTape t).core.ptrs 15 ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 15 ≤ s.core.ptrs 15 + kidSumH Y f S i KH ∧
        s.core.ptrs 16 ≤ (run (Blocks.prog B) s detTape t).core.ptrs 16 ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 16 ≤ s.core.ptrs 16 + kidSum Y f S i * KR ∧
        (run (Blocks.prog B) s detTape t).work ≤ s.work + d * kidW S.card + 5 + kidSum Y f S i * KW ∧
        (∀ z, 0 ≤ z → z < s.core.ptrs 15 → (z < Kd + i ∨ Kd + S.card ≤ z) →
          (run (Blocks.prog B) s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ z, Zn - S.card ≤ z → z < 0 →
          (run (Blocks.prog B) s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ j (hj : j < S.card), compMin (ptsOf Y S) (dK Y S) ⟨j, hj⟩ < i →
          (run (Blocks.prog B) s detTape t).integerMemory (Kd + j) = s.integerMemory (Kd + j)) ∧
        (∀ z, 0 ≤ z → z < s.core.ptrs 16 →
          (run (Blocks.prog B) s detTape t).core.mem z = s.core.mem z) ∧
        (∀ j (hj : j < S.card), i ≤ compMin (ptsOf Y S) (dK Y S) ⟨j, hj⟩ → ∀ s'' : State,
          (∀ z, s.core.ptrs 15 ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 15 →
            s''.integerMemory z = (run (Blocks.prog B) s detTape t).integerMemory z) →
          (∀ z, 0 ≤ z → z < Hbase N T0 →
            s''.integerMemory z = (run (Blocks.prog B) s detTape t).integerMemory z) →
          (∀ z, s.core.ptrs 16 ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 16 →
            s''.core.mem z = (run (Blocks.prog B) s detTape t).core.mem z) →
          HTreeAt m s'' ((run (Blocks.prog B) s detTape t).integerMemory (Kd + j))
            (hpimNode Y δ f (compBotOf Y S ⟨j, hj⟩))) ∧
        (∀ c ∈ cellsWritten (Blocks.prog B) s t,
          (c.1 = false ∧ ((Kd + i ≤ c.2 ∧ c.2 < Kd + S.card) ∨
            (s.core.ptrs 15 ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 15) ∨
            (Zn - Dn WbI S.card ≤ c.2 ∧ c.2 < Zn - S.card))) ∨
          (c.1 = true ∧ ((s.core.ptrs 16 ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 16) ∨
            (ZRn - WbR ≤ c.2 ∧ c.2 < ZRn)))) := by
  have hE := emb14 B hB
  intro d
  induction d with
  | zero =>
    intro i hi s hpc hh hEnv h3 h19 h21 h8 hlab hK hR
    simp only [Nat.add_zero] at hi; subst hi
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, aw, acw⟩ :=
      kid_exit (Blocks.prog B) B.o14 B.lbl_NODE hE s S.card hpc hh h3 hEnv.p11
    refine ⟨5, a1, a2, ?_, by rw [a3, h21], by rw [a4, hEnv.p20], by rw [a5, hEnv.p28],
      by rw [a6 8 (by simp), h8], by rw [a6 15 (by simp)], ?_, by rw [a6 16 (by simp)], ?_, ?_,
      fun z _ _ _ => by rw [a8], fun z _ _ => by rw [a8], fun j _ _ => by rw [a8],
      fun z _ _ => by rw [a9], fun j hj hj' => ?_, by rw [acw]; simp⟩
    · exact GInv.transfer Y δ T0 v0 hEnv.g (fun x hx => a6 x (by simp at hx ⊢; omega))
        (fun x _ => by rw [a7]) (fun z _ _ => by rw [a8]) (fun z _ _ => by rw [a9])
    · rw [a6 15 (by simp)]; unfold kidSumH; rw [compsFrom_card_end]; simp
    · rw [a6 16 (by simp)]; unfold kidSum; rw [compsFrom_card_end]; simp
    · rw [aw]; unfold kidSum; rw [compsFrom_card_end]; simp
    · have := compMin_lt (ptsOf Y S) (dK Y S) ⟨j, hj⟩; omega
  | succ d ih =>
    intro i hi s hpc hh hEnv h3 h19 h21 h8 hlab hK hR
    have hin : i < S.card := by omega
    have hli : labOf Y S i = (compMin (ptsOf Y S) (dK Y S) ⟨i, hin⟩ : ℤ) := by
      unfold labOf; rw [dif_pos hin]
    have hle : compMin (ptsOf Y S) (dK Y S) ⟨i, hin⟩ ≤ i := compMin_le _ _ _
    by_cases hrep : compMin (ptsOf Y S) (dK Y S) ⟨i, hin⟩ = i
    · -- a representative: a new component
      have hrepZ : labOf Y S i = (i : ℤ) := by rw [hli, hrep]
      have hval : ∀ k : ℕ, k < S.card → s.integerMemory (Sa + k) = valsOf S k := by
        intro k hk; rw [show Sa + (k : ℤ) = Sa + ((⟨k, hk⟩ : Fin S.card) : ℕ) from rfl, hEnv.slist ⟨k, hk⟩]
        unfold valsOf; rw [dif_pos hk]
      have hSa0 := hEnv.sa
      have hNm : (0 : ℤ) ≤ (N : ℤ) * m := by positivity
      set Lo := s.core.ptrs 15 with hLo
      obtain ⟨t1, ht1, a1, a2, a2', a13, a14, a8, a15, aP, aR, aM, aL, a3', a7', aK, aF, aI, aw, acw⟩ :=
        kid_pre (Blocks.prog B) B.o14 B.lbl_NODE hE S.card i (labOf Y S) (valsOf S) Zn Sa Kd Lo s hpc hh
          h3 hEnv.p11 hin hEnv.p20 hEnv.p10 h19 rfl hrepZ hlab hval hZn hEnv.sa hSK hK
      set S1 := run (Blocks.prog B) s detTape t1 with hS1
      set C := compBotOf Y S ⟨i, hin⟩ with hC
      obtain ⟨hlenC, hSLC⟩ := slist_comp Y S (labOf Y S) (valsOf S) i hin
        (fun j hj => by unfold labOf; rw [dif_pos hj]; rfl) hrep
        (fun j hj => by unfold valsOf; rw [dif_pos hj]) aL
      rw [← hC] at hlenC hSLC
      set c := (selK (labOf Y S) i S.card).length with hc
      have hC1 : 1 ≤ C.card := compBotOf_card_pos Y S ⟨i, hin⟩
      have hC2 : 2 * C.card ≤ S.card := by
        have := compBot_card_le Y hY S hn ⟨i, hin⟩; rw [← hC] at this; omega
      have hTC : C.card ≤ treePts Y f C := card_le_treePts Y f C
      set F := Zn - S.card - 10 with hF
      have hDn : S.card + 10 + Dn WbI C.card ≤ Dn WbI S.card := dn_child WbI S.card C.card hC1 hC2
      have hHbK : Hbase N T0 ≤ Kd := by omega
      -- the call
      have g1 : GInv Y δ T0 v0 S1 := GInv.transfer Y δ T0 v0 hEnv.g
        (fun x hx => aP x (by simp at hx ⊢; omega)) (fun x _ => by rw [aR])
        (fun z h0 h1 => aI z (Or.inr (Or.inl ⟨by omega, by omega⟩))) (fun z _ _ => by rw [aM])
      obtain ⟨t2, c1, c2, cG, c8, c15l, c15u, c16l, c16u, cw, ccw, cS⟩ :=
        IH C hC1 (by omega) S1 (Lo + c) Lo F ZRn F (Lo + c + 8) (s.core.ptrs 16) a1 a2 g1 a2' a13
          (by rw [a14, hEnv.p28]) a8 a15 (by rw [aP 16 (by simp)]) a3' (by rw [a7', hlenC]) hSLC
          (by omega) (by rw [hlenC]) le_rfl hR (by omega) hZRn
      set S2 := run (Blocks.prog B) S1 detTape t2 with hS2
      obtain ⟨cM, cI⟩ : (∀ z, (z < s.core.ptrs 16 ∨ S2.core.ptrs 16 ≤ z) → z < ZRn - WbR ∨ ZRn ≤ z →
          S2.core.mem z = S1.core.mem z) ∧
          (∀ z, (z < Lo + c ∨ S2.core.ptrs 15 ≤ z) → (z < F - Dn WbI C.card ∨ F ≤ z) →
          S2.integerMemory z = S1.integerMemory z) := by
        constructor
        · intro z h1 h2
          apply run_mem_unwritten
          intro hc'
          rcases ccw _ hc' with ⟨e1, _⟩ | ⟨_, e2 | e2⟩
          · simp at e1
          · omega
          · omega
        · intro z h1 h2
          apply run_im_unwritten
          intro hc'
          rcases ccw _ hc' with ⟨_, e2 | e2 | e2⟩ | ⟨e1, _⟩
          · omega
          · omega
          · omega
          · simp at e1
      -- the return
      have hFr : FrameAt S2 (S2.core.ptrs 8) (frameOf s) := by
        rw [c8]; intro k
        rw [cI _ (Or.inl (by have := k.isLt; omega)) (Or.inr (by omega))]
        exact aF k
      obtain ⟨d1, d2, d3, dR, dP, dRg, dI, dM, dw, dcw⟩ :=
        kid_post (Blocks.prog B) B.o14 B.lbl_NODE hE S2 c1 c2 (frameOf s) hFr rfl
      set S3 := run (Blocks.prog B) S2 detTape 26 with hS3
      have fr : ∀ k : Fin 10, k ≠ 0 → k ≠ 2 → S3.core.ptrs (frameRegs k) = frameOf s k := dR
      have r2 : S3.core.ptrs 2 = v := by rw [show (2 : ℕ) = frameRegs 1 from rfl, fr 1 (by decide) (by decide)]; exact hEnv.p2
      have r11 : S3.core.ptrs 11 = S.card := by
        rw [show (11 : ℕ) = frameRegs 3 from rfl, fr 3 (by decide) (by decide)]; exact hEnv.p11
      have r10 : S3.core.ptrs 10 = Sa := by
        rw [show (10 : ℕ) = frameRegs 4 from rfl, fr 4 (by decide) (by decide)]; exact hEnv.p10
      have r20 : S3.core.ptrs 20 = Zn := by
        rw [show (20 : ℕ) = frameRegs 5 from rfl, fr 5 (by decide) (by decide)]; exact hEnv.p20
      have r19 : S3.core.ptrs 19 = Kd := by
        rw [show (19 : ℕ) = frameRegs 6 from rfl, fr 6 (by decide) (by decide)]; exact h19
      have r21 : S3.core.ptrs 21 = vr := by
        rw [show (21 : ℕ) = frameRegs 7 from rfl, fr 7 (by decide) (by decide)]; exact h21
      have r8 : S3.core.ptrs 8 = FP := by
        rw [show (8 : ℕ) = frameRegs 8 from rfl, fr 8 (by decide) (by decide)]; exact h8
      have r28 : S3.core.ptrs 28 = ZRn := by
        rw [show (28 : ℕ) = frameRegs 9 from rfl, fr 9 (by decide) (by decide)]; exact hEnv.p28
      have r3 : S3.core.ptrs 3 = (i + 1 : ℕ) := by rw [d3]; simp [frameOf, h3]
      have r15 : S3.core.ptrs 15 = S2.core.ptrs 15 := dP 15 (by simp)
      have r16 : S3.core.ptrs 16 = S2.core.ptrs 16 := dP 16 (by simp)
      have fI2 : ∀ z, 0 ≤ z → z < Lo → (z < Kd + i ∨ Kd + S.card ≤ z) →
          S2.integerMemory z = s.integerMemory z := by
        intro z h0 h1 h2
        rw [cI z (Or.inl (by omega)) (Or.inr (by omega))]
        exact aI z (by omega)
      have fL2 : ∀ z, Zn - S.card ≤ z → z < 0 → S2.integerMemory z = s.integerMemory z := by
        intro z h0 h1
        rw [cI z (Or.inl (by omega)) (Or.inr (by omega))]
        exact aI z (Or.inr (Or.inl ⟨h0, by omega⟩))
      have fM2 : ∀ z, 0 ≤ z → z < s.core.ptrs 16 → S2.core.mem z = s.core.mem z := by
        intro z h0 h1
        rw [cM z (Or.inl h1) (Or.inr (by omega)), aM]
      have env3 : NodeEnv Y δ T0 v0 S v Sa Zn ZRn S3 :=
        ⟨GInv.transfer Y δ T0 v0 cG (fun x hx => dP x (by simp at hx ⊢; omega)) (fun x _ => by rw [dRg])
          (fun z _ _ => by rw [dI]) (fun z _ _ => by rw [dM]), r2, r10, r11, r20, r28,
          fun k => by rw [dI, fI2 _ (by omega) (by have := k.isLt; omega) (Or.inl (by have := k.isLt; omega))];
                      exact hEnv.slist k, hSa0⟩
      obtain ⟨t4, e1, e2, eG, e2', e13, e14, e8, e15l, e15u, e16l, e16u, ew, eI, eL, eK, eM, eS, ecw⟩ :=
        ih (i + 1) (by omega) S3 d1 d2 env3 r3 r19 r21 r8
          (fun k hk => by rw [dI, fL2 _ (by omega) (by omega)]; exact hlab k hk)
          (by rw [r15]; omega) (by rw [r16]; omega)
      refine ⟨t1 + t2 + 26 + t4, ?_⟩
      have R1 : run (Blocks.prog B) s detTape (t1 + t2) = S2 := by rw [run_add]
      have R2 : run (Blocks.prog B) s detTape (t1 + t2 + 26) = S3 := by rw [run_add, R1]
      have R : run (Blocks.prog B) s detTape (t1 + t2 + 26 + t4) = run (Blocks.prog B) S3 detTape t4 := by
        rw [run_add, R2]
      have CW : cellsWritten (Blocks.prog B) s (t1 + t2 + 26 + t4) =
          cellsWritten (Blocks.prog B) s t1 ∪ cellsWritten (Blocks.prog B) S1 t2 ∪
            cellsWritten (Blocks.prog B) S2 26 ∪ cellsWritten (Blocks.prog B) S3 t4 := by
        rw [cellsWritten_add, R2, cellsWritten_add, R1, cellsWritten_add]
      rw [R, CW, dcw, Finset.union_empty]
      set Sf := run (Blocks.prog B) S3 detTape t4 with hSf
      have ksum : kidSum Y f S i = treePts Y f C + kidSum Y f S (i + 1) := by
        unfold kidSum
        obtain ⟨h1, h2⟩ := compsFrom_succ_rep Y S i hin hrep
        rw [h1, Finset.sum_insert h2]
      have hT1 : 1 ≤ treePts Y f C := le_trans hC1 hTC
      refine ⟨e1, e2, eG, e2', e13, e14, e8, by omega, ?_, by omega, ?_, ?_, fun z h0 h1 h2 => ?_,
        fun z h0 h1 => ?_, fun j hj hj' => ?_, fun z h0 h1 => ?_, fun j hj hj' => ?_, fun c' hc' => ?_⟩
      · have k1 : (kidSumH Y f S i KH : ℤ) = (C.card : ℤ) + 8 + (treePts Y f C : ℤ) * KH +
            (kidSumH Y f S (i + 1) KH : ℤ) := by
          unfold kidSumH
          obtain ⟨h1, h2⟩ := compsFrom_succ_rep Y S i hin hrep
          rw [h1, Finset.sum_insert h2]; push_cast; ring
        have k2 : (c : ℤ) = C.card := by rw [hlenC]
        rw [r15] at e15u
        push_cast at e15u c15u ⊢
        linarith
      · have k1 : (kidSum Y f S i : ℤ) * KR = (treePts Y f C : ℤ) * KR +
            (kidSum Y f S (i + 1) : ℤ) * KR := by rw [ksum]; push_cast; ring
        rw [r16] at e16u
        push_cast at e16u c16u ⊢
        linarith
      · have k1 : kidSum Y f S i * KW = treePts Y f C * KW + kidSum Y f S (i + 1) * KW := by
          rw [ksum]; ring
        have k2 : (d + 1) * kidW S.card = d * kidW S.card + kidW S.card := by ring
        have k3 : 23 * S.card + 75 ≤ kidW S.card := by unfold kidW; omega
        have hw3 : S3.work = S2.work + 26 := dw
        have hw1 : S1.work = s.work + t1 := aw
        rw [k1, k2]
        omega
      · rw [eI z h0 (by omega) (by omega), dI, fI2 z h0 h1 h2]
      · rw [eL z h0 h1, dI, fL2 z h0 h1]
      · rw [eK j hj (by omega), dI, cI _ (Or.inl (by omega)) (Or.inr (by omega))]
        rcases Nat.lt_or_ge j i with hji | hji
        · exact aI _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
        · rw [aK j hji hj, if_neg]
          unfold labOf; rw [dif_pos hj]; intro h; have : compMin (ptsOf Y S) (dK Y S) ⟨j, hj⟩ = i := by exact_mod_cast h
          omega
      · rw [eM z h0 (by omega), dM, fM2 z h0 h1]
      · intro s'' hI hH hM
        by_cases hji : compMin (ptsOf Y S) (dK Y S) ⟨j, hj⟩ = i
        · have hij : i ≤ j := by have := compMin_le (ptsOf Y S) (dK Y S) ⟨j, hj⟩; simp at this; omega
          have hval' : Sf.integerMemory (Kd + j) = Lo + c := by
            rw [eK j hj (by omega), dI, cI _ (Or.inl (by omega)) (Or.inr (by omega)), aK j hij hj, if_pos]
            unfold labOf; rw [dif_pos hj, hji]
          rw [hval', compBotOf_of_compMin Y S ⟨j, hj⟩ i hin hji]
          apply cS s''
          · intro z h1 h2
            rw [hI z h1 (by omega), eI z (by omega) (by omega) (Or.inr (by omega)), dI]
          · intro z h1 h2
            rw [hH z h1 h2, eI z h1 (by omega) (Or.inl (by omega)), dI]
          · intro z h1 h2
            rw [hM z h1 (by omega), eM z (by omega) (by omega), dM]
        · exact eS j hj (by omega) s'' (fun z h1 h2 => hI z (by omega) h2) hH
            (fun z h1 h2 => hM z (by omega) h2)
      · simp only [Finset.mem_union] at hc'
        rcases hc' with (h | h) | h
        · obtain ⟨e1', e2'' | e2'' | e2''⟩ := acw c' h
          · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨e2''.1, by omega⟩)⟩
          · exact Or.inl ⟨e1', Or.inl ⟨by omega, e2''.2⟩⟩
          · exact Or.inl ⟨e1', Or.inr (Or.inr ⟨by omega, e2''.2⟩)⟩
        · rcases ccw c' h with ⟨e1', e2'' | e2'' | e2''⟩ | ⟨e1', e2'' | e2''⟩
          · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
          · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
          · exact Or.inl ⟨e1', Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
          · exact Or.inr ⟨e1', Or.inl ⟨e2''.1, by omega⟩⟩
          · exact Or.inr ⟨e1', Or.inr e2''⟩
        · rcases ecw c' h with ⟨e1', e2'' | e2'' | e2''⟩ | ⟨e1', e2'' | e2''⟩
          · exact Or.inl ⟨e1', Or.inl ⟨by omega, e2''.2⟩⟩
          · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨by omega, e2''.2⟩)⟩
          · exact Or.inl ⟨e1', Or.inr (Or.inr e2'')⟩
          · exact Or.inr ⟨e1', Or.inl ⟨by omega, e2''.2⟩⟩
          · exact Or.inr ⟨e1', Or.inr e2''⟩
    · -- not a representative: skip
      have hlt : labOf Y S i < i := by
        rw [hli]
        have : compMin (ptsOf Y S) (dK Y S) ⟨i, hin⟩ < i := by omega
        exact_mod_cast this
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, aw, acw⟩ :=
        kid_skip (Blocks.prog B) B.o14 B.lbl_NODE hE s S.card i (labOf Y S) Zn hpc hh h3 hEnv.p11 hin
          hEnv.p20 (hlab i hin) hlt
      set S1 := run (Blocks.prog B) s detTape 8 with hS1
      have env1 : NodeEnv Y δ T0 v0 S v Sa Zn ZRn S1 := hEnv.transfer Y δ T0 v0
        (fun x hx => a4 x (by simp at hx ⊢; omega)) (fun x _ => by rw [a5]) (fun z _ => by rw [a6])
        (fun z _ _ => by rw [a7])
      obtain ⟨t2, b1, b2, b3, b4, b5, b6, b8, b15l, b15u, b16l, b16u, bw, bI, bL, bK, bM, bS, bcw⟩ :=
        ih (i + 1) (by omega) S1 a1 a2 env1 a3 (by rw [a4 19 (by simp)]; exact h19)
          (by rw [a4 21 (by simp)]; exact h21) (by rw [a4 8 (by simp)]; exact h8)
          (fun k hk => by rw [a6]; exact hlab k hk) (by rw [a4 15 (by simp)]; exact hK)
          (by rw [a4 16 (by simp)]; exact hR)
      have q15 : S1.core.ptrs 15 = s.core.ptrs 15 := a4 15 (by simp)
      have q16 : S1.core.ptrs 16 = s.core.ptrs 16 := a4 16 (by simp)
      have hsum : kidSum Y f S i = kidSum Y f S (i + 1) := by
        unfold kidSum; rw [compsFrom_succ_nonrep Y S i hin hrep]
      have hsumH : kidSumH Y f S i KH = kidSumH Y f S (i + 1) KH := by
        unfold kidSumH; rw [compsFrom_succ_nonrep Y S i hin hrep]
      refine ⟨8 + t2, ?_⟩
      rw [run_add, cellsWritten_add, ← hS1, acw, Finset.empty_union]
      rw [q15] at b15l b15u bI bS bcw
      rw [q16] at b16l b16u bM bS bcw
      refine ⟨b1, b2, b3, b4, b5, b6, b8, b15l, by rw [hsumH]; exact b15u, b16l, by rw [hsum]; exact b16u,
        ?_, fun z h0 h1 h2 => ?_, fun z h1 h2 => ?_, fun j hj hj' => ?_, fun z h0 h1 => ?_,
        fun j hj hj' => ?_, fun c hc => ?_⟩
      · rw [hsum]; rw [aw] at bw
        have e : (d + 1) * kidW S.card = d * kidW S.card + kidW S.card := by ring
        have e8 : 8 ≤ kidW S.card := by unfold kidW; omega
        rw [e]; omega
      · rw [bI z h0 h1 (by omega), a6]
      · rw [bL z h1 h2, a6]
      · rw [bK j hj (by omega), a6]
      · rw [bM z h0 h1, a7]
      · have : compMin (ptsOf Y S) (dK Y S) ⟨j, hj⟩ ≠ i :=
          fun h => hrep (rep_of_compMin Y S ⟨j, hj⟩ i hin h)
        exact bS j hj (by omega)
      · rcases bcw c hc with ⟨e1, e2 | e2 | e2⟩ | e
        · exact Or.inl ⟨e1, Or.inl ⟨by omega, e2.2⟩⟩
        · exact Or.inl ⟨e1, Or.inr (Or.inl e2)⟩
        · exact Or.inl ⟨e1, Or.inr (Or.inr e2)⟩
        · exact Or.inr e

end DetANN.HPIM.PP

theorem solution : type_of% @DetANN.HPIM.PP.kids_loop := @DetANN.HPIM.PP.kids_loop
