-- Prove2me | solution 1 for DetANN.HPIM.hpim_query_program_wf
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T20:28:33.983556+00:00
-- url     : https://prove2.me/submissions/8dc1a6d7-7ca6-4a02-8875-8dbfe346c023

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF

/-!
# The query program for well-formed HPIM trees (`DetANN.HPIM.hpim_query_program_wf`)

`Qprog` (135 instructions, no coin, no `rpow`, no real literals) walks the HPIM tree iteratively:
* `HN = 7`: read the node; a single point halts with its index; an inner node looks up `Z_0`, then
  `Z_{M-1}`, and either descends (child of the answer, or representatives) or runs the bisection
  `BLOOP = 42` with the table of powers, and halts with the global index of the final answer.
* `LOOKUP = 88` computes `u = I[I[v+2] + i]`; `EVAL = 94` evaluates the box tree at `u`, testing
  `q ∈ [lo, hi]` coordinatewise in the loop `LOOP = 102`; `DISP = 131` returns to one of four call
  sites through the selector `p11`.

Proof layers (by induction, with explicit step counts): `loop_spec` (≤ 13 k + 1 steps), `eval_spec`
(≤ (13 m + 20) · visits), `lookup_spec`, `bisect_spec` (≤ 33 (m + 1) · bisectCost), the straight-line
segments `seg_*`, `hn_spec` (≤ 80 (m + 1) · cost) and the 7 initial steps; `c₀ = 87`.
-/

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

/-- The query program. -/
def Qprog : Program := [
  .core (.pset 9 (0)), -- 0
  .core (.pset 19 (1)), -- 1
  .core (.pset 20 (2)), -- 2
  .core (.pset 4 (1)), -- 3
  .integerLoad 1 4, -- 4
  .core (.pset 4 (2)), -- 5
  .integerLoad 2 4, -- 6
  .integerLoad 18 2, -- 7
  .core (.pjle 18 9 76), -- 8
  .core (.pcopy 4 2), -- 9
  .core (.pinc 4), -- 10
  .integerLoad 12 4, -- 11
  .core (.pcopy 13 12), -- 12
  .core (.pdec 13), -- 13
  .core (.pjle 12 9 80), -- 14
  .core (.pset 17 (0)), -- 15
  .core (.pset 11 (0)), -- 16
  .core (.pjle 9 9 88), -- 17
  .core (.pjle 10 9 29), -- 18
  .core (.pcopy 4 2), -- 19
  .core (.pinc 4), -- 20
  .core (.pinc 4), -- 21
  .core (.pinc 4), -- 22
  .core (.pinc 4), -- 23
  .integerLoad 4 4, -- 24
  .core (.pdec 10), -- 25
  .pointerAdd 4 4 10, -- 26
  .integerLoad 2 4, -- 27
  .core (.pjle 9 9 7), -- 28
  .core (.pcopy 17 13), -- 29
  .core (.pset 11 (1)), -- 30
  .core (.pjle 9 9 88), -- 31
  .core (.pjle 10 9 80), -- 32
  .core (.pcopy 4 2), -- 33
  .core (.pinc 4), -- 34
  .core (.pinc 4), -- 35
  .core (.pinc 4), -- 36
  .core (.pinc 4), -- 37
  .core (.pinc 4), -- 38
  .core (.pinc 4), -- 39
  .integerLoad 14 4, -- 40
  .core (.pset 15 (0)), -- 41
  .core (.pjle 14 9 58), -- 42
  .core (.pdec 14), -- 43
  .core (.pset 4 (3)), -- 44
  .integerLoad 4 4, -- 45
  .pointerAdd 4 4 14, -- 46
  .integerLoad 21 4, -- 47
  .pointerAdd 16 15 21, -- 48
  .core (.pcopy 17 16), -- 49
  .core (.pjle 17 13 52), -- 50
  .core (.pcopy 17 13), -- 51
  .core (.pset 11 (2)), -- 52
  .core (.pjle 9 9 88), -- 53
  .core (.pjle 10 9 56), -- 54
  .core (.pjle 9 9 42), -- 55
  .core (.pcopy 15 16), -- 56
  .core (.pjle 9 9 42), -- 57
  .core (.pcopy 17 15), -- 58
  .core (.pinc 17), -- 59
  .core (.pjle 17 13 62), -- 60
  .core (.pcopy 17 13), -- 61
  .core (.pset 11 (3)), -- 62
  .core (.pjle 9 9 88), -- 63
  .core (.pjle 10 9 74), -- 64
  .core (.pcopy 4 2), -- 65
  .core (.pinc 4), -- 66
  .core (.pinc 4), -- 67
  .core (.pinc 4), -- 68
  .integerLoad 4 4, -- 69
  .core (.pdec 10), -- 70
  .pointerAdd 4 4 10, -- 71
  .integerLoad 0 4, -- 72
  .halt, -- 73
  .core (.pset 0 (0)), -- 74
  .halt, -- 75
  .core (.pcopy 4 2), -- 76
  .core (.pinc 4), -- 77
  .integerLoad 0 4, -- 78
  .halt, -- 79
  .core (.pcopy 4 2), -- 80
  .core (.pinc 4), -- 81
  .core (.pinc 4), -- 82
  .core (.pinc 4), -- 83
  .core (.pinc 4), -- 84
  .core (.pinc 4), -- 85
  .integerLoad 2 4, -- 86
  .core (.pjle 9 9 7), -- 87
  .core (.pcopy 4 2), -- 88
  .core (.pinc 4), -- 89
  .core (.pinc 4), -- 90
  .integerLoad 4 4, -- 91
  .pointerAdd 4 4 17, -- 92
  .integerLoad 3 4, -- 93
  .integerLoad 18 3, -- 94
  .core (.pjle 18 9 128), -- 95
  .core (.pcopy 4 3), -- 96
  .core (.pinc 4), -- 97
  .integerLoad 5 4, -- 98
  .pointerAdd 6 5 1, -- 99
  .core (.pset 7 (-1)), -- 100
  .core (.pcopy 8 1), -- 101
  .core (.pjle 8 9 117), -- 102
  .core (.load 0 5), -- 103
  .core (.load 1 7), -- 104
  .core (.sub 2 0 1), -- 105
  .core (.jle 2 108), -- 106
  .core (.pjle 9 9 122), -- 107
  .core (.load 0 6), -- 108
  .core (.sub 2 1 0), -- 109
  .core (.jle 2 112), -- 110
  .core (.pjle 9 9 122), -- 111
  .core (.pinc 5), -- 112
  .core (.pinc 6), -- 113
  .core (.pdec 7), -- 114
  .core (.pdec 8), -- 115
  .core (.pjle 9 9 102), -- 116
  .core (.pcopy 4 3), -- 117
  .core (.pinc 4), -- 118
  .core (.pinc 4), -- 119
  .integerLoad 3 4, -- 120
  .core (.pjle 9 9 94), -- 121
  .core (.pcopy 4 3), -- 122
  .core (.pinc 4), -- 123
  .core (.pinc 4), -- 124
  .core (.pinc 4), -- 125
  .integerLoad 3 4, -- 126
  .core (.pjle 9 9 94), -- 127
  .core (.pcopy 4 3), -- 128
  .core (.pinc 4), -- 129
  .integerLoad 10 4, -- 130
  .core (.pjle 11 9 18), -- 131
  .core (.pjle 11 19 32), -- 132
  .core (.pjle 11 20 54), -- 133
  .core (.pjle 9 9 64) -- 134
]

end DetANN.HPIM.QP

-- ===== QP_Loop =====
namespace DetANN.HPIM.QP

open PNormReg PNormRegLib SmaleNinth



/-- The box-test loop at `LOOP = 102`: coordinates `j, …, m-1` are checked. -/
lemma loop_spec (m : ℕ) (lo hi q : Fin m → ℝ) (a : ℤ) (MEM : ℤ → ℝ)
    (hlo : ∀ j : Fin m, MEM (a + j) = lo j) (hhi : ∀ j : Fin m, MEM (a + m + j) = hi j)
    (hq : ∀ j : Fin m, MEM (-1 - j) = q j) :
    ∀ k j : ℕ, k + j = m → ∀ s : State, s.core.pc = 102 → s.halted = false → s.core.mem = MEM →
      s.core.ptrs 8 = k → s.core.ptrs 5 = a + j → s.core.ptrs 6 = a + m + j →
      s.core.ptrs 7 = -1 - j → s.core.ptrs 9 = 0 →
      ∃ n, n ≤ 13 * k + 1 ∧
        (run Qprog s detTape n).core.pc =
          (if ∀ j' : Fin m, j ≤ (j' : ℕ) → lo j' ≤ q j' ∧ q j' ≤ hi j' then 117 else 122) ∧
        (run Qprog s detTape n).halted = false ∧ (run Qprog s detTape n).core.mem = MEM ∧
        (run Qprog s detTape n).integerMemory = s.integerMemory ∧
        (∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → (run Qprog s detTape n).core.ptrs x = s.core.ptrs x) ∧
        (run Qprog s detTape n).work = s.work + n := by
  intro k
  induction k with
  | zero =>
    intro j hj s hpc hh hmem h8 h5 h6 h7 h9
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh hmem h8 h5 h6 h7 h9
    subst hpc hh hmem
    refine ⟨1, le_refl _, ?_⟩
    (rw [run_exec rfl rfl]; simp only [exec, coreExec])
    rw [if_pos (by rw [h8, h9]; simp), run_zero]
    refine ⟨?_, by (first | rfl | trivial | (intros; rfl) | (intros; trivial)), by (first | rfl | trivial | (intros; rfl) | (intros; trivial)), by (first | rfl | trivial | (intros; rfl) | (intros; trivial)), by (first | rfl | trivial | (intros; rfl) | (intros; trivial)), by (first | rfl | trivial | (intros; rfl) | (intros; trivial))⟩
    rw [if_pos]
    intro j' hj'; omega
  | succ k ih =>
    intro j hj s hpc hh hmem h8 h5 h6 h7 h9
    have hjm : j < m := by omega
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh hmem h8 h5 h6 h7 h9
    subst hpc hh hmem
    have hk : ¬ ptrs 8 ≤ ptrs 9 := by rw [h8, h9]; push_cast; omega
    set jj : Fin m := ⟨j, hjm⟩
    have hA := hlo jj; have hH := hhi jj; have hQ := hq jj
    simp only [jj] at hA hH hQ
    by_cases c1 : lo jj ≤ q jj
    · by_cases c2 : q jj ≤ hi jj
      · -- the coordinate passes: 13 steps back to the loop head
        set S := run Qprog ⟨⟨102, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 13 with hSdef
        have hS : S.core.pc = 102 ∧ S.halted = false ∧ S.core.mem = mem ∧ S.integerMemory = im ∧
            S.core.ptrs 8 = k ∧ S.core.ptrs 5 = a + (j + 1 : ℕ) ∧ S.core.ptrs 6 = a + m + (j + 1 : ℕ) ∧
            S.core.ptrs 7 = -1 - (j + 1 : ℕ) ∧ S.core.ptrs 9 = 0 ∧
            (∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → S.core.ptrs x = ptrs x) ∧ S.work = w + 13 := by
          rw [hSdef]
          (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg hk]
          (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
          rw [if_pos (by simp [Function.update_apply, h5, h7, hA, hQ]; linarith)]
          (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
          rw [if_pos (by simp [Function.update_apply, h6, h7, hH, hQ]; linarith)]
          (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
          rw [if_pos le_rfl, run_zero]
          refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [Function.update_apply, h8]
          · simp [Function.update_apply, h5]; ring
          · simp [Function.update_apply, h6]; ring
          · simp [Function.update_apply, h7]; ring
          · simp [Function.update_apply, h9]
          · intro x h5' h6' h7' h8'; simp [Function.update_apply, h5', h6', h7', h8']
          · rfl
        obtain ⟨p1, p2, p3, p4, p8, p5, p6, p7, p9, pf, pw⟩ := hS
        obtain ⟨n', hn', r1, r2, r3, r4, r5, r6⟩ := ih (j + 1) (by omega) S p1 p2 p3 p8 p5 p6 p7 p9
        refine ⟨13 + n', by omega, ?_⟩
        rw [run_add, ← hSdef]
        refine ⟨?_, r2, r3, by rw [r4, p4], ?_, by rw [r6, pw]; ring⟩
        · rw [r1]
          congr 1
          apply propext
          constructor
          · intro h j' hj'
            rcases Nat.eq_or_lt_of_le hj' with e | e
            · have : j' = jj := Fin.ext e.symm
              rw [this]; exact ⟨c1, c2⟩
            · exact h j' e
          · intro h j' hj'
            exact h j' (by omega)
        · intro x h5' h6' h7' h8'
          rw [r5 x h5' h6' h7' h8', pf x h5' h6' h7' h8']
      · -- the upper bound fails: 10 steps to NO
        refine ⟨9, by omega, ?_⟩
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg hk]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
        rw [if_pos (by simp [Function.update_apply, h5, h7, hA, hQ]; linarith)]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
        rw [if_neg (by simp [Function.update_apply, h6, h7, hH, hQ]; linarith)]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl, run_zero]
        refine ⟨?_, by (first | rfl | trivial | (intros; rfl) | (intros; trivial)), by (first | rfl | trivial | (intros; rfl) | (intros; trivial)), by (first | rfl | trivial | (intros; rfl) | (intros; trivial)), ?_, by (first | rfl | trivial | (intros; rfl) | (intros; trivial))⟩
        · rw [if_neg]; intro h; exact c2 (h jj le_rfl).2
        · intro x h5' h6' h7' h8'; simp [Function.update_apply, h5', h6', h7', h8']
    · -- the lower bound fails: 6 steps to NO
      refine ⟨6, by omega, ?_⟩
      (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg hk]
      (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
      rw [if_neg (by simp [Function.update_apply, h5, h7, hA, hQ]; linarith)]
      (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl, run_zero]
      refine ⟨?_, by (first | rfl | trivial | (intros; rfl) | (intros; trivial)), by (first | rfl | trivial | (intros; rfl) | (intros; trivial)), by (first | rfl | trivial | (intros; rfl) | (intros; trivial)), ?_, by (first | rfl | trivial | (intros; rfl) | (intros; trivial))⟩
      · rw [if_neg]; intro h; exact c1 (h jj le_rfl).1
      · intro x h5' h6' h7' h8'; simp [Function.update_apply, h5', h6', h7', h8']

end DetANN.HPIM.QP

-- ===== QP_Eval =====
namespace DetANN.HPIM.QP

open PNormReg PNormRegLib SmaleNinth

/-- The invariant of a running query: not halted, fixed memories, and the constant registers
`p1 = m`, `p9 = 0`, `p19 = 1`, `p20 = 2`. -/
structure Ctx (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (s : State) : Prop where
  hh : s.halted = false
  mem : s.core.mem = MEM
  im : s.integerMemory = IM
  pM : s.core.ptrs 1 = m
  pZ : s.core.ptrs 9 = 0
  pOne : s.core.ptrs 19 = 1
  pTwo : s.core.ptrs 20 = 2

/-- Pointer registers outside `l` are unchanged. -/
def Keep (l : List ℕ) (s s' : State) : Prop := ∀ x, x ∉ l → s'.core.ptrs x = s.core.ptrs x

lemma Keep.trans {l : List ℕ} {s₁ s₂ s₃ : State} (h₁ : Keep l s₁ s₂) (h₂ : Keep l s₂ s₃) :
    Keep l s₁ s₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

lemma Keep.mono {l l' : List ℕ} {s s' : State} (h : Keep l s s') (hl : ∀ x ∈ l, x ∈ l') :
    Keep l' s s' := fun x hx => h x (fun h' => hx (hl x h'))

/-- The register code of a lookup answer. -/
def code : Option ℕ → ℤ
  | none => 0
  | some i => (i : ℤ) + 1

lemma ctx_of {m : ℕ} {IM : ℤ → ℤ} {MEM : ℤ → ℝ} {s s' : State} (hC : Ctx m IM MEM s)
    (hh : s'.halted = false) (hm : s'.core.mem = s.core.mem) (hi : s'.integerMemory = s.integerMemory)
    (hk : ∀ x, x = 1 ∨ x = 9 ∨ x = 19 ∨ x = 20 → s'.core.ptrs x = s.core.ptrs x) : Ctx m IM MEM s' :=
  ⟨hh, hm.trans hC.mem, hi.trans hC.im, (hk 1 (by simp)).trans hC.pM, (hk 9 (by simp)).trans hC.pZ,
    (hk 19 (by simp)).trans hC.pOne, (hk 20 (by simp)).trans hC.pTwo⟩


lemma keep_nil_of {s s' : State} (l : List ℕ) (h : ∀ x, x ∉ l → s'.core.ptrs x = s.core.ptrs x) :
    Keep l s s' := h

/-- **The BoxTree evaluator** at `EVAL = 94`: it reaches `DISP = 131` with `p10 = code (T.eval q)`. -/
lemma eval_spec (m : ℕ) (s₀ : State) (q : Fin m → ℝ) (MEM : ℤ → ℝ)
    (hpos : ∀ z, 0 ≤ z → MEM z = s₀.core.mem z) (hq : ∀ j : Fin m, MEM (-1 - j) = q j) :
    ∀ u T, BoxTreeAt m s₀ u T → ∀ s, s.core.pc = 94 → Ctx m s₀.integerMemory MEM s → s.core.ptrs 3 = u →
      ∃ n, n ≤ (13 * m + 20) * T.visits q ∧ (run Qprog s detTape n).core.pc = 131 ∧
        Ctx m s₀.integerMemory MEM (run Qprog s detTape n) ∧
        (run Qprog s detTape n).core.ptrs 10 = code (T.eval q) ∧
        Keep [3, 4, 5, 6, 7, 8, 10, 18] s (run Qprog s detTape n) ∧
        (run Qprog s detTape n).work = s.work + n := by
  intro u T hT
  induction hT with
  | leaf u a h0 h1 =>
    intro s hpc hC h3
    obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh hmem him hM hZ hO hT2 h3
    subst hpc hh hmem him
    refine ⟨5, by simp only [BoxTree.visits]; omega, ?_⟩
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
    rw [if_pos (by simp [Function.update_apply, h3, h0, hZ])]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
    rw [run_zero]
    refine ⟨rfl, ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩, ?_, ?_, rfl⟩
    · simp [Function.update_apply, hM]
    · simp [Function.update_apply, hZ]
    · simp [Function.update_apply, hO]
    · simp [Function.update_apply, hT2]
    · simp [Function.update_apply, h3, h1, BoxTree.eval, code]; cases a <;> rfl
    · intro x hx; simp at hx; simp [Function.update_apply, hx]
  | test u lo hi y nn h1 h0 hlo hhi hy hn ihy ihn =>
    intro s hpc hC h3
    obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh hmem him hM hZ hO hT2 h3
    subst hpc hh hmem him
    set a := s₀.integerMemory (u + 1) with ha
    -- phase 1: eight steps to the loop head
    set S := run Qprog ⟨⟨94, regs, ptrs, mem⟩, s₀.integerMemory, cur, false, w⟩ detTape 8 with hSdef
    have hS : S.core.pc = 102 ∧ S.halted = false ∧ S.core.mem = mem ∧
        S.integerMemory = s₀.integerMemory ∧
        S.core.ptrs 8 = ((m : ℕ) : ℤ) ∧ S.core.ptrs 5 = a + ((0 : ℕ) : ℤ) ∧
        S.core.ptrs 6 = a + m + ((0 : ℕ) : ℤ) ∧ S.core.ptrs 7 = -1 - ((0 : ℕ) : ℤ) ∧ S.core.ptrs 9 = 0 ∧
        (∀ x, x ∉ [4, 5, 6, 7, 8, 18] → S.core.ptrs x = ptrs x) ∧ S.work = w + 8 := by
      rw [hSdef]
      (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
      rw [if_neg (by simp [Function.update_apply, h3, h1, hZ])]
      (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
      rw [run_zero]
      refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · simp [Function.update_apply, hM]
      · simp [Function.update_apply, h3, ha]
      · simp [Function.update_apply, h3, ha, hM]
      · simp [Function.update_apply]
      · simp [Function.update_apply, hZ]
      · intro x hx; simp at hx; simp [Function.update_apply, hx]
    obtain ⟨p1, p2, p3, p4, p8, p5, p6, p7, p9, pk, pw⟩ := hS
    have ha0 : 0 ≤ a := h0
    have hlo' : ∀ j : Fin m, mem (a + j) = lo j := fun j => by
      rw [hpos _ (by positivity)]; exact hlo j
    have hhi' : ∀ j : Fin m, mem (a + m + j) = hi j := fun j => by
      rw [hpos _ (by positivity)]; exact hhi j
    have hq' : ∀ j : Fin m, mem (-1 - j) = q j := hq
    -- phase 2: the loop
    obtain ⟨n1, hn1, r1, r2, r3, r4, r5, r6⟩ :=
      loop_spec m lo hi q a mem hlo' hhi' hq' m 0 (by simp) S p1 p2 p3 p8 p5 p6 p7 p9
    have hbox : (∀ j' : Fin m, 0 ≤ (j' : ℕ) → lo j' ≤ q j' ∧ q j' ≤ hi j') ↔ InBox lo hi q :=
      ⟨fun h j => h j (Nat.zero_le _), fun h j _ => h j⟩
    have hu3 : (run Qprog S detTape n1).core.ptrs 3 = u := by
      rw [r5 3 (by simp) (by simp) (by simp) (by simp), pk 3 (by simp), h3]
    have hZ1 : (run Qprog S detTape n1).core.ptrs 9 = 0 := by
      rw [r5 9 (by simp) (by simp) (by simp) (by simp), p9]
    generalize hS1 : run Qprog S detTape n1 = S1 at r1 r2 r3 r4 r5 r6 hu3 hZ1
    rw [p4] at r4
    by_cases hin : InBox lo hi q
    · have hpc1 : S1.core.pc = 117 := by rw [r1, if_pos (hbox.2 hin)]
      obtain ⟨⟨pc1, regs1, ptrs1, mem1⟩, im1, cur1, hlt1, w1⟩ := S1
      simp only at hpc1 r2 r3 r4 r5 r6 hu3 hZ1
      subst hpc1 r2 r4; subst mem1
      set S2 := run Qprog ⟨⟨117, regs1, ptrs1, mem⟩, s₀.integerMemory, cur1, false, w1⟩ detTape 5 with hS2def
      have hS2 : S2.core.pc = 94 ∧ S2.halted = false ∧ S2.core.mem = mem ∧
          S2.integerMemory = s₀.integerMemory ∧ S2.core.ptrs 3 = s₀.integerMemory (u + 2) ∧
          (∀ x, x ∉ [3, 4] → S2.core.ptrs x = ptrs1 x) ∧ S2.work = w1 + 5 := by
        rw [hS2def]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
        rw [if_pos (by simp [Function.update_apply, hZ1]), run_zero]
        refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
        · simp [Function.update_apply, hu3]; ring_nf
        · intro x hx; simp at hx; simp [Function.update_apply, hx]
      obtain ⟨q1, q2, q3, q4, q3', qk, qw⟩ := hS2
      have hkeep1 : ∀ x, x ∉ [3, 4, 5, 6, 7, 8, 10, 18] → S2.core.ptrs x = ptrs x := by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [qk x (by simp [hx.1, hx.2.1]), r5 x hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1,
          pk x (by simp [hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.2])]
      have hC2 : Ctx m s₀.integerMemory mem S2 :=
        ⟨q2, q3, q4, by rw [hkeep1 1 (by simp), hM], by rw [hkeep1 9 (by simp), hZ],
          by rw [hkeep1 19 (by simp), hO], by rw [hkeep1 20 (by simp), hT2]⟩
      obtain ⟨n2, hn2, t1, t2, t3, t4, t5⟩ := ihy S2 q1 hC2 q3'
      refine ⟨8 + n1 + 5 + n2, ?_, ?_⟩
      · have hv : (BoxTree.test lo hi y nn).visits q = 1 + y.visits q := by
          simp [BoxTree.visits, hin]
        rw [hv, mul_add, mul_one]; linarith
      rw [run_add, run_add, run_add, ← hSdef, hS1, ← hS2def]
      refine ⟨t1, t2, ?_, ?_, ?_⟩
      · rw [t3]; simp [BoxTree.eval, hin]
      · intro x hx; rw [t4 x hx, hkeep1 x hx]
      · rw [t5, qw, r6, pw]; ring
    · have hpc1 : S1.core.pc = 122 := by rw [r1, if_neg (fun h => hin (hbox.1 h))]
      obtain ⟨⟨pc1, regs1, ptrs1, mem1⟩, im1, cur1, hlt1, w1⟩ := S1
      simp only at hpc1 r2 r3 r4 r5 r6 hu3 hZ1
      subst hpc1 r2 r4; subst mem1
      set S2 := run Qprog ⟨⟨122, regs1, ptrs1, mem⟩, s₀.integerMemory, cur1, false, w1⟩ detTape 6 with hS2def
      have hS2 : S2.core.pc = 94 ∧ S2.halted = false ∧ S2.core.mem = mem ∧
          S2.integerMemory = s₀.integerMemory ∧ S2.core.ptrs 3 = s₀.integerMemory (u + 3) ∧
          (∀ x, x ∉ [3, 4] → S2.core.ptrs x = ptrs1 x) ∧ S2.work = w1 + 6 := by
        rw [hS2def]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
        rw [if_pos (by simp [Function.update_apply, hZ1]), run_zero]
        refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
        · simp [Function.update_apply, hu3]; ring_nf
        · intro x hx; simp at hx; simp [Function.update_apply, hx]
      obtain ⟨q1, q2, q3, q4, q3', qk, qw⟩ := hS2
      have hkeep1 : ∀ x, x ∉ [3, 4, 5, 6, 7, 8, 10, 18] → S2.core.ptrs x = ptrs x := by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [qk x (by simp [hx.1, hx.2.1]), r5 x hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1,
          pk x (by simp [hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.2])]
      have hC2 : Ctx m s₀.integerMemory mem S2 :=
        ⟨q2, q3, q4, by rw [hkeep1 1 (by simp), hM], by rw [hkeep1 9 (by simp), hZ],
          by rw [hkeep1 19 (by simp), hO], by rw [hkeep1 20 (by simp), hT2]⟩
      obtain ⟨n2, hn2, t1, t2, t3, t4, t5⟩ := ihn S2 q1 hC2 q3'
      refine ⟨8 + n1 + 6 + n2, ?_, ?_⟩
      · have hv : (BoxTree.test lo hi y nn).visits q = 1 + nn.visits q := by
          simp [BoxTree.visits, hin]
        rw [hv, mul_add, mul_one]; linarith
      rw [run_add, run_add, run_add, ← hSdef, hS1, ← hS2def]
      refine ⟨t1, t2, ?_, ?_, ?_⟩
      · rw [t3]; simp [BoxTree.eval, hin]
      · intro x hx; rw [t4 x hx, hkeep1 x hx]
      · rw [t5, qw, r6, pw]; ring

end DetANN.HPIM.QP

-- ===== QP_Lookup =====
namespace DetANN.HPIM.QP

open PNormReg PNormRegLib SmaleNinth

/-- The return labels of the dispatch. -/
def retLabel : ℕ → ℕ
  | 0 => 18
  | 1 => 32
  | 2 => 54
  | _ => 64

/-- **A lookup** at `LOOKUP = 88`: evaluate the box tree at `I[I[v+2] + i]`, then dispatch on `p11`. -/
lemma lookup_spec (m : ℕ) (s₀ : State) (q : Fin m → ℝ) (MEM : ℤ → ℝ)
    (hpos : ∀ z, 0 ≤ z → MEM z = s₀.core.mem z) (hq : ∀ j : Fin m, MEM (-1 - j) = q j)
    (v i : ℤ) (T : BoxTree m)
    (hT : BoxTreeAt m s₀ (s₀.integerMemory (s₀.integerMemory (v + 2) + i)) T) (r : ℕ) (hr : r ≤ 3)
    (s : State) (hpc : s.core.pc = 88) (hC : Ctx m s₀.integerMemory MEM s) (hv : s.core.ptrs 2 = v)
    (hi : s.core.ptrs 17 = i) (hret : s.core.ptrs 11 = r) :
    ∃ n, n ≤ 10 + (13 * m + 20) * T.visits q ∧ (run Qprog s detTape n).core.pc = retLabel r ∧
      Ctx m s₀.integerMemory MEM (run Qprog s detTape n) ∧
      (run Qprog s detTape n).core.ptrs 10 = code (T.eval q) ∧
      Keep [3, 4, 5, 6, 7, 8, 10, 18] s (run Qprog s detTape n) ∧
      (run Qprog s detTape n).work = s.work + n := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hmem him hM hZ hO hT2 hv hi hret
  subst hpc hh him; subst mem
  set S := run Qprog ⟨⟨88, regs, ptrs, MEM⟩, s₀.integerMemory, cur, false, w⟩ detTape 6 with hSdef
  have hS : S.core.pc = 94 ∧ Ctx m s₀.integerMemory MEM S ∧
      S.core.ptrs 3 = s₀.integerMemory (s₀.integerMemory (v + 2) + i) ∧
      (∀ x, x ∉ [3, 4] → S.core.ptrs x = ptrs x) ∧ S.work = w + 6 := by
    rw [hSdef]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
    rw [run_zero]
    refine ⟨rfl, ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩, ?_, ?_, rfl⟩
    · simp [Function.update_apply, hM]
    · simp [Function.update_apply, hZ]
    · simp [Function.update_apply, hO]
    · simp [Function.update_apply, hT2]
    · simp [Function.update_apply, hv, hi]; ring_nf
    · intro x hx; simp at hx; simp [Function.update_apply, hx]
  obtain ⟨p1, pC, p3, pk, pw⟩ := hS
  obtain ⟨n1, hn1, r1, rC, r10, rk, rw'⟩ := eval_spec m s₀ q MEM hpos hq _ T hT S p1 pC p3
  have hret' : (run Qprog S detTape n1).core.ptrs 11 = r := by
    rw [rk 11 (by simp), pk 11 (by simp), hret]
  generalize hS1 : run Qprog S detTape n1 = S1 at r1 rC r10 rk rw' hret'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := rC
  obtain ⟨⟨pc1, regs1, ptrs1, mem1⟩, im1, cur1, hlt1, w1⟩ := S1
  simp only at r1 c1 c2 c3 c4 c5 c6 c7 r10 rk rw' hret'
  subst r1 c1 c3; subst mem1
  have hkeep : ∀ x, x ∉ [3, 4, 5, 6, 7, 8, 10, 18] → ptrs1 x = ptrs x := by
    intro x hx
    have h1 := rk x hx
    simp only at h1
    have hx' : x ∉ [3, 4] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
    rw [h1, pk x hx']
  interval_cases r
  · refine ⟨6 + n1 + 1, by omega, ?_⟩
    rw [run_add, run_add, ← hSdef, hS1]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [hret', c5, c6, c7])]
    rw [run_zero]
    refine ⟨rfl, ⟨rfl, rfl, rfl, c4, c5, c6, c7⟩, r10, ?_, ?_⟩
    · intro x hx; simp only; rw [hkeep x hx]
    · simp only; rw [rw', pw]; ring
  · refine ⟨6 + n1 + 2, by omega, ?_⟩
    rw [run_add, run_add, ← hSdef, hS1]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [hret', c5, c6, c7])]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [hret', c5, c6, c7])]
    rw [run_zero]
    refine ⟨rfl, ⟨rfl, rfl, rfl, c4, c5, c6, c7⟩, r10, ?_, ?_⟩
    · intro x hx; simp only; rw [hkeep x hx]
    · simp only; rw [rw', pw]; ring
  · refine ⟨6 + n1 + 3, by omega, ?_⟩
    rw [run_add, run_add, ← hSdef, hS1]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [hret', c5, c6, c7])]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [hret', c5, c6, c7])]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [hret', c5, c6, c7])]
    rw [run_zero]
    refine ⟨rfl, ⟨rfl, rfl, rfl, c4, c5, c6, c7⟩, r10, ?_, ?_⟩
    · intro x hx; simp only; rw [hkeep x hx]
    · simp only; rw [rw', pw]; ring
  · refine ⟨6 + n1 + 4, by omega, ?_⟩
    rw [run_add, run_add, ← hSdef, hS1]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [hret', c5, c6, c7])]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [hret', c5, c6, c7])]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [hret', c5, c6, c7])]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl]
    rw [run_zero]
    refine ⟨rfl, ⟨rfl, rfl, rfl, c4, c5, c6, c7⟩, r10, ?_, ?_⟩
    · intro x hx; simp only; rw [hkeep x hx]
    · simp only; rw [rw', pw]; ring

end DetANN.HPIM.QP

-- ===== QP_Bisect =====
namespace DetANN.HPIM.QP

open PNormReg PNormRegLib SmaleNinth

lemma lookupC_eq {m M : ℕ} (Z : Fin M → BoxTree m) (hM : 1 ≤ M) (i : ℕ) (q : Fin m → ℝ) :
    lookupC Z i q = (Z ⟨min i (M - 1), by omega⟩).eval q ∧
      lookupCCost Z i q = (Z ⟨min i (M - 1), by omega⟩).visits q := by
  unfold lookupC lookupCCost lookup lookupCost
  rw [dif_pos (by omega), dif_pos (by omega)]
  exact ⟨rfl, rfl⟩

/-- **The bisection loop** at `BLOOP = 42`: it reaches `FIN = 58` with `p15 + 1 = bisect`. -/
lemma bisect_spec (m : ℕ) (s₀ : State) (q : Fin m → ℝ) (MEM : ℤ → ℝ)
    (hpos : ∀ z, 0 ≤ z → MEM z = s₀.core.mem z) (hq : ∀ j : Fin m, MEM (-1 - j) = q j)
    (v : ℤ) (M t₀ : ℕ) (hM : 1 ≤ M) (Z : Fin M → BoxTree m)
    (hZ : ∀ i : Fin M, BoxTreeAt m s₀ (s₀.integerMemory (s₀.integerMemory (v + 2) + i)) (Z i))
    (hpow : ∀ t ≤ t₀, s₀.integerMemory (s₀.integerMemory 3 + t) = 2 ^ t) :
    ∀ t lo : ℕ, t ≤ t₀ → ∀ s : State, s.core.pc = 42 → Ctx m s₀.integerMemory MEM s →
      s.core.ptrs 2 = v → s.core.ptrs 14 = t → s.core.ptrs 15 = lo → s.core.ptrs 13 = (M : ℤ) - 1 →
      ∃ n L : ℕ, n ≤ 33 * (m + 1) * bisectCost Z q t lo ∧ bisect Z q t lo = L + 1 ∧
        (run Qprog s detTape n).core.pc = 58 ∧ Ctx m s₀.integerMemory MEM (run Qprog s detTape n) ∧
        (run Qprog s detTape n).core.ptrs 15 = L ∧ (run Qprog s detTape n).core.ptrs 2 = v ∧
        (run Qprog s detTape n).core.ptrs 13 = (M : ℤ) - 1 ∧
        (run Qprog s detTape n).work = s.work + n := by
  intro t
  induction t with
  | zero =>
    intro lo _ s hpc hC hv ht hlo hmm
    obtain ⟨hh, hmem, him, hM', hZ', hO, hT2⟩ := hC
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh hmem him hM' hZ' hO hT2 hv ht hlo hmm
    subst hpc hh him; subst mem
    refine ⟨1, lo, by simp [bisectCost]; nlinarith, rfl, ?_⟩
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [ht, hZ']), run_zero]
    exact ⟨rfl, ⟨rfl, rfl, rfl, hM', hZ', hO, hT2⟩, hlo, hv, hmm, rfl⟩
  | succ t ih =>
    intro lo ht0 s hpc hC hv ht hlo hmm
    obtain ⟨hh, hmem, him, hM', hZ', hO, hT2⟩ := hC
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh hmem him hM' hZ' hO hT2 hv ht hlo hmm
    subst hpc hh him; subst mem
    have hpw : s₀.integerMemory (s₀.integerMemory 3 + (t : ℤ)) = 2 ^ t := hpow t (by omega)
    have ht' : ptrs 14 - 1 = (t : ℤ) := by rw [ht]; push_cast; ring
    have hP' : ((lo + 2 ^ t : ℕ) : ℤ) = (lo : ℤ) + 2 ^ t := by push_cast; ring
    set P : ℕ := lo + 2 ^ t with hP
    set idx : ℕ := min P (M - 1) with hidx
    have hidxM : idx < M := by omega
    obtain ⟨hlC, hlCC⟩ := lookupC_eq Z hM P q
    -- continuation from the lookup call
    have cont : ∀ d (S : State), d ≤ 12 → S = run Qprog ⟨⟨42, regs, ptrs, MEM⟩, s₀.integerMemory, cur, false, w⟩
        detTape d → S.core.pc = 88 → Ctx m s₀.integerMemory MEM S → S.core.ptrs 2 = v →
        S.core.ptrs 17 = (idx : ℤ) → S.core.ptrs 11 = ((2 : ℕ) : ℤ) → S.core.ptrs 14 = t → S.core.ptrs 15 = lo →
        S.core.ptrs 16 = (P : ℤ) → S.core.ptrs 13 = (M : ℤ) - 1 → S.work = w + d →
        ∃ n L : ℕ, n ≤ 33 * (m + 1) * bisectCost Z q (t + 1) lo ∧ bisect Z q (t + 1) lo = L + 1 ∧
          (run Qprog ⟨⟨42, regs, ptrs, MEM⟩, s₀.integerMemory, cur, false, w⟩ detTape n).core.pc = 58 ∧
          Ctx m s₀.integerMemory MEM (run Qprog ⟨⟨42, regs, ptrs, MEM⟩, s₀.integerMemory, cur, false, w⟩
            detTape n) ∧
          (run Qprog ⟨⟨42, regs, ptrs, MEM⟩, s₀.integerMemory, cur, false, w⟩ detTape n).core.ptrs 15 = L ∧
          (run Qprog ⟨⟨42, regs, ptrs, MEM⟩, s₀.integerMemory, cur, false, w⟩ detTape n).core.ptrs 2 = v ∧
          (run Qprog ⟨⟨42, regs, ptrs, MEM⟩, s₀.integerMemory, cur, false, w⟩ detTape n).core.ptrs 13 =
            (M : ℤ) - 1 ∧
          (run Qprog ⟨⟨42, regs, ptrs, MEM⟩, s₀.integerMemory, cur, false, w⟩ detTape n).work =
            w + n := by
      intro d S hd hS e1 eC e2 e17 e11 e14 e15 e16 e13 ew
      have hZi := hZ ⟨idx, hidxM⟩
      simp only at hZi
      obtain ⟨n1, hn1, r1, rC, r10, rk, rw'⟩ :=
        lookup_spec m s₀ q MEM hpos hq v idx (Z ⟨idx, hidxM⟩) hZi 2 (by norm_num) S e1 eC e2 e17 e11
      have k2 := rk 2 (by simp); have k13 := rk 13 (by simp); have k14 := rk 14 (by simp)
      have k15 := rk 15 (by simp); have k16 := rk 16 (by simp)
      generalize hS1 : run Qprog S detTape n1 = S1 at r1 rC r10 rk rw' k2 k13 k14 k15 k16
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := rC
      obtain ⟨⟨pc1, regs1, ptrs1, mem1⟩, im1, cur1, hlt1, w1⟩ := S1
      simp only at r1 c1 c2 c3 c4 c5 c6 c7 r10 rw' k2 k13 k14 k15 k16
      simp only [retLabel] at r1
      subst r1 c1 c3; subst mem1
      by_cases hnone : lookupC Z P q = none
      · -- advance: lo := P
        have hev : (Z ⟨idx, hidxM⟩).eval q = none := by rw [← hlC]; exact hnone
        set S2 := run Qprog ⟨⟨54, regs1, ptrs1, MEM⟩, s₀.integerMemory, cur1, false, w1⟩ detTape 3
          with hS2def
        have hS2 : S2.core.pc = 42 ∧ Ctx m s₀.integerMemory MEM S2 ∧ S2.core.ptrs 2 = v ∧
            S2.core.ptrs 14 = t ∧ S2.core.ptrs 15 = (P : ℤ) ∧ S2.core.ptrs 13 = (M : ℤ) - 1 ∧
            S2.work = w1 + 3 := by
          rw [hS2def]
          (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [r10, hev, code, c5])]
          (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl, run_zero]
          refine ⟨rfl, ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl⟩ <;>
            simp [Function.update_apply, c4, c5, c6, c7, k2, k14, k16, k13, e2, e14, e16, e13]
        obtain ⟨q1, qC, q2, q14, q15, q13, qw⟩ := hS2
        obtain ⟨n2, L, hn2, hL, t1, tC, t15, t2, t13, tw⟩ := ih P (by omega) S2 q1 qC q2 q14 q15 q13
        refine ⟨d + n1 + 3 + n2, L, ?_, ?_, ?_⟩
        · have hc : bisectCost Z q (t + 1) lo = 1 + (Z ⟨idx, hidxM⟩).visits q + bisectCost Z q t P := by
            simp only [bisectCost, ← hP, hnone, if_true, hlCC]; rfl
          rw [hc]
          have : (13 * m + 20) * (Z ⟨idx, hidxM⟩).visits q ≤ 33 * (m + 1) * (Z ⟨idx, hidxM⟩).visits q :=
            Nat.mul_le_mul_right _ (by omega)
          rw [mul_add, mul_add, mul_one]; linarith
        · simp only [bisect, ← hP, hnone, if_true]; exact hL
        · rw [run_add, run_add, run_add, ← hS, hS1, ← hS2def]
          exact ⟨t1, tC, t15, t2, t13, by rw [tw, qw, rw', ew]; ring⟩
      · -- keep lo
        have hev : ∃ i, (Z ⟨idx, hidxM⟩).eval q = some i := by
          rw [← hlC]; exact Option.ne_none_iff_exists'.1 hnone
        obtain ⟨i, hi⟩ := hev
        set S2 := run Qprog ⟨⟨54, regs1, ptrs1, MEM⟩, s₀.integerMemory, cur1, false, w1⟩ detTape 2
          with hS2def
        have hS2 : S2.core.pc = 42 ∧ Ctx m s₀.integerMemory MEM S2 ∧ S2.core.ptrs 2 = v ∧
            S2.core.ptrs 14 = t ∧ S2.core.ptrs 15 = (lo : ℤ) ∧ S2.core.ptrs 13 = (M : ℤ) - 1 ∧
            S2.work = w1 + 2 := by
          rw [hS2def]
          (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [r10, hi, code, c5] <;> omega)]
          (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl, run_zero]
          refine ⟨rfl, ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl⟩ <;>
            simp [Function.update_apply, c4, c5, c6, c7, k2, k14, k15, k13, e2, e14, e15, e13]
        obtain ⟨q1, qC, q2, q14, q15, q13, qw⟩ := hS2
        obtain ⟨n2, L, hn2, hL, t1, tC, t15, t2, t13, tw⟩ := ih lo (by omega) S2 q1 qC q2 q14 q15 q13
        refine ⟨d + n1 + 2 + n2, L, ?_, ?_, ?_⟩
        · have hc : bisectCost Z q (t + 1) lo = 1 + (Z ⟨idx, hidxM⟩).visits q + bisectCost Z q t lo := by
            simp only [bisectCost, ← hP, hnone, if_false, hlCC]; rfl
          rw [hc]
          have : (13 * m + 20) * (Z ⟨idx, hidxM⟩).visits q ≤ 33 * (m + 1) * (Z ⟨idx, hidxM⟩).visits q :=
            Nat.mul_le_mul_right _ (by omega)
          rw [mul_add, mul_add, mul_one]; linarith
        · simp only [bisect, ← hP, hnone, if_false]; exact hL
        · rw [run_add, run_add, run_add, ← hS, hS1, ← hS2def]
          exact ⟨t1, tC, t15, t2, t13, by rw [tw, qw, rw', ew]; ring⟩
    -- the setup phase, with or without the clamp
    by_cases hcl : (P : ℤ) ≤ (M : ℤ) - 1
    · have hidx' : (idx : ℤ) = P := by rw [hidx]; push_cast; omega
      set S := run Qprog ⟨⟨42, regs, ptrs, MEM⟩, s₀.integerMemory, cur, false, w⟩ detTape 11 with hSdef
      have hS : S.core.pc = 88 ∧ Ctx m s₀.integerMemory MEM S ∧ S.core.ptrs 2 = v ∧
          S.core.ptrs 17 = (idx : ℤ) ∧ S.core.ptrs 11 = ((2 : ℕ) : ℤ) ∧ S.core.ptrs 14 = t ∧
          S.core.ptrs 15 = lo ∧ S.core.ptrs 16 = (P : ℤ) ∧ S.core.ptrs 13 = (M : ℤ) - 1 ∧
          S.work = w + 11 := by
        rw [hSdef]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [ht, hZ'] <;> omega)]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
        rw [if_pos (by simp [Function.update_apply, hlo, ht', hpw, hmm]; push_cast at hcl ⊢; linarith)]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
        rw [if_pos le_rfl, run_zero]
        refine ⟨rfl, ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
        · simp [Function.update_apply, hM']
        · simp [Function.update_apply, hZ']
        · simp [Function.update_apply, hO]
        · simp [Function.update_apply, hT2]
        · simp [Function.update_apply, hv]
        · simp [Function.update_apply, hlo, ht', hpw, hidx', hP, hP']
        · simp [Function.update_apply]
        · simp [Function.update_apply, ht']
        · simp [Function.update_apply, hlo]
        · simp [Function.update_apply, hlo, ht', hpw, hP, hP']
        · simp [Function.update_apply, hmm]
      obtain ⟨a1, aC, a2, a17, a11, a14, a15, a16, a13, aw⟩ := hS
      exact cont 11 S (by omega) hSdef a1 aC a2 a17 a11 a14 a15 a16 a13 aw
    · have hidx' : (idx : ℤ) = (M : ℤ) - 1 := by rw [hidx]; push_cast; omega
      set S := run Qprog ⟨⟨42, regs, ptrs, MEM⟩, s₀.integerMemory, cur, false, w⟩ detTape 12 with hSdef
      have hS : S.core.pc = 88 ∧ Ctx m s₀.integerMemory MEM S ∧ S.core.ptrs 2 = v ∧
          S.core.ptrs 17 = (idx : ℤ) ∧ S.core.ptrs 11 = ((2 : ℕ) : ℤ) ∧ S.core.ptrs 14 = t ∧
          S.core.ptrs 15 = lo ∧ S.core.ptrs 16 = (P : ℤ) ∧ S.core.ptrs 13 = (M : ℤ) - 1 ∧
          S.work = w + 12 := by
        rw [hSdef]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [ht, hZ'] <;> omega)]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
        rw [if_neg (by simp [Function.update_apply, hlo, ht', hpw, hmm]; push_cast at hcl ⊢; linarith)]
        (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
        rw [if_pos le_rfl, run_zero]
        refine ⟨rfl, ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
        · simp [Function.update_apply, hM']
        · simp [Function.update_apply, hZ']
        · simp [Function.update_apply, hO]
        · simp [Function.update_apply, hT2]
        · simp [Function.update_apply, hv]
        · simp [Function.update_apply, hmm, hidx']
        · simp [Function.update_apply]
        · simp [Function.update_apply, ht']
        · simp [Function.update_apply, hlo]
        · simp [Function.update_apply, hlo, ht', hpw, hP, hP']
        · simp [Function.update_apply, hmm]
      obtain ⟨a1, aC, a2, a17, a11, a14, a15, a16, a13, aw⟩ := hS
      exact cont 12 S (by omega) hSdef a1 aC a2 a17 a11 a14 a15 a16 a13 aw

end DetANN.HPIM.QP

-- ===== QP_Seg =====
namespace DetANN.HPIM.QP

open PNormReg PNormRegLib SmaleNinth


/-- A single point: halt with its index. -/
lemma seg_single (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (v : ℤ) (s : State) (hpc : s.core.pc = 7)
    (hC : Ctx m IM MEM s) (hv : s.core.ptrs 2 = v) (h0 : IM v = 0) :
    (run Qprog s detTape 6).halted = true ∧ (run Qprog s detTape 6).core.ptrs 0 = IM (v + 1) ∧ (run Qprog s detTape 6).work = s.work + 6 := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at *
  subst hpc hh him; subst mem
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [hv, h0, hZ])]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  rw [run_zero]
  refine ⟨rfl, ?_, rfl⟩
  simp [Function.update_apply, hv]

/-- An inner node with `M = 0`: go to the representatives. -/
lemma seg_m0 (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (v : ℤ) (s : State) (hpc : s.core.pc = 7)
    (hC : Ctx m IM MEM s) (hv : s.core.ptrs 2 = v) (h1 : IM v = 1) (hM0 : IM (v + 1) = 0) :
    (run Qprog s detTape 16).core.pc = 7 ∧ Ctx m IM MEM (run Qprog s detTape 16) ∧ (run Qprog s detTape 16).core.ptrs 2 = IM (v + 5) ∧ (run Qprog s detTape 16).work = s.work + 16 := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at *
  subst hpc hh him; subst mem
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [hv, h1, hZ])]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [Function.update_apply, hv, hM0, hZ])]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl]
  rw [run_zero]
  refine ⟨rfl, by (refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_apply, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, if_false, *]), ?_, rfl⟩
  simp [Function.update_apply, hv]; ring_nf

/-- An inner node with `M ≥ 1`: look up `Z_0`. -/
lemma seg_m1 (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (v : ℤ) (M : ℕ) (s : State) (hpc : s.core.pc = 7)
    (hC : Ctx m IM MEM s) (hv : s.core.ptrs 2 = v) (h1 : IM v = 1) (hMv : IM (v + 1) = M) (hM1 : 1 ≤ M) :
    (run Qprog s detTape 11).core.pc = 88 ∧ Ctx m IM MEM (run Qprog s detTape 11) ∧ (run Qprog s detTape 11).core.ptrs 2 = v ∧ (run Qprog s detTape 11).core.ptrs 17 = 0 ∧ (run Qprog s detTape 11).core.ptrs 11 = ((0 : ℕ) : ℤ) ∧ (run Qprog s detTape 11).core.ptrs 13 = (M : ℤ) - 1 ∧ (run Qprog s detTape 11).work = s.work + 11 := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at *
  subst hpc hh him; subst mem
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [hv, h1, hZ])]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [Function.update_apply, hv, hMv, hZ]<;> omega)]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl]
  rw [run_zero]
  refine ⟨rfl, by (refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_apply, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, if_false, *]), ?_, ?_, ?_, ?_, rfl⟩ <;> simp [Function.update_apply, hv, hMv]

/-- `Z_0` answers `i`: go to the child of `i`. -/
lemma seg_ret0_some (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (v : ℤ) (i : ℕ) (s : State) (hpc : s.core.pc = 18)
    (hC : Ctx m IM MEM s) (hv : s.core.ptrs 2 = v) (h10 : s.core.ptrs 10 = (i : ℤ) + 1) :
    (run Qprog s detTape 11).core.pc = 7 ∧ Ctx m IM MEM (run Qprog s detTape 11) ∧ (run Qprog s detTape 11).core.ptrs 2 = IM (IM (v + 4) + i) ∧ (run Qprog s detTape 11).work = s.work + 11 := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at *
  subst hpc hh him; subst mem
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [h10, hZ]<;> omega)]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl]
  rw [run_zero]
  refine ⟨rfl, by (refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_apply, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, if_false, *]), ?_, rfl⟩
  simp [Function.update_apply, hv, h10]; ring_nf

/-- `Z_0` is null: look up `Z_{M-1}`. -/
lemma seg_ret0_none (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (v : ℤ) (M : ℕ) (s : State) (hpc : s.core.pc = 18)
    (hC : Ctx m IM MEM s) (hv : s.core.ptrs 2 = v) (h10 : s.core.ptrs 10 = 0) (h13 : s.core.ptrs 13 = (M : ℤ) - 1) :
    (run Qprog s detTape 4).core.pc = 88 ∧ Ctx m IM MEM (run Qprog s detTape 4) ∧ (run Qprog s detTape 4).core.ptrs 2 = v ∧ (run Qprog s detTape 4).core.ptrs 17 = (M : ℤ) - 1 ∧ (run Qprog s detTape 4).core.ptrs 11 = ((1 : ℕ) : ℤ) ∧ (run Qprog s detTape 4).core.ptrs 13 = (M : ℤ) - 1 ∧ (run Qprog s detTape 4).work = s.work + 4 := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at *
  subst hpc hh him; subst mem
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [h10, hZ])]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl]
  rw [run_zero]
  refine ⟨rfl, by (refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_apply, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, if_false, *]), ?_, ?_, ?_, ?_, rfl⟩ <;> simp [Function.update_apply, hv, h13]

/-- `Z_{M-1}` is null: go to the representatives. -/
lemma seg_ret1_none (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (v : ℤ) (s : State) (hpc : s.core.pc = 32)
    (hC : Ctx m IM MEM s) (hv : s.core.ptrs 2 = v) (h10 : s.core.ptrs 10 = 0) :
    (run Qprog s detTape 9).core.pc = 7 ∧ Ctx m IM MEM (run Qprog s detTape 9) ∧ (run Qprog s detTape 9).core.ptrs 2 = IM (v + 5) ∧ (run Qprog s detTape 9).work = s.work + 9 := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at *
  subst hpc hh him; subst mem
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [h10, hZ])]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl]
  rw [run_zero]
  refine ⟨rfl, by (refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_apply, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, if_false, *]), ?_, rfl⟩
  simp [Function.update_apply, hv]; ring_nf

/-- `Z_{M-1}` answers: start the bisection. -/
lemma seg_ret1_some (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (v : ℤ) (M i : ℕ) (s : State) (hpc : s.core.pc = 32)
    (hC : Ctx m IM MEM s) (hv : s.core.ptrs 2 = v) (h10 : s.core.ptrs 10 = (i : ℤ) + 1) (h13 : s.core.ptrs 13 = (M : ℤ) - 1) :
    (run Qprog s detTape 10).core.pc = 42 ∧ Ctx m IM MEM (run Qprog s detTape 10) ∧ (run Qprog s detTape 10).core.ptrs 2 = v ∧ (run Qprog s detTape 10).core.ptrs 14 = IM (v + 6) ∧ (run Qprog s detTape 10).core.ptrs 15 = ((0 : ℕ) : ℤ) ∧ (run Qprog s detTape 10).core.ptrs 13 = (M : ℤ) - 1 ∧ (run Qprog s detTape 10).work = s.work + 10 := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at *
  subst hpc hh him; subst mem
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [h10, hZ]<;> omega)]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  rw [run_zero]
  refine ⟨rfl, by (refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_apply, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, if_false, *]), ?_, ?_, ?_, ?_, rfl⟩ <;> simp [Function.update_apply, hv, h13]; ring_nf

/-- The final lookup is null: answer `0`. -/
lemma seg_ret3_none (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (s : State) (hpc : s.core.pc = 64)
    (hC : Ctx m IM MEM s) (h10 : s.core.ptrs 10 = 0) :
    (run Qprog s detTape 3).halted = true ∧ (run Qprog s detTape 3).core.ptrs 0 = 0 ∧ (run Qprog s detTape 3).work = s.work + 3 := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at *
  subst hpc hh him; subst mem
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [h10, hZ])]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  rw [run_zero]
  refine ⟨rfl, ?_, rfl⟩
  simp [Function.update_apply]

/-- The final lookup answers `i`: answer its global index. -/
lemma seg_ret3_some (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (v : ℤ) (i : ℕ) (s : State) (hpc : s.core.pc = 64)
    (hC : Ctx m IM MEM s) (hv : s.core.ptrs 2 = v) (h10 : s.core.ptrs 10 = (i : ℤ) + 1) :
    (run Qprog s detTape 10).halted = true ∧ (run Qprog s detTape 10).core.ptrs 0 = IM (IM (v + 3) + i) ∧ (run Qprog s detTape 10).work = s.work + 10 := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at *
  subst hpc hh him; subst mem
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [h10, hZ]<;> omega)]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  rw [run_zero]
  refine ⟨rfl, ?_, rfl⟩
  simp [Function.update_apply, hv, h10]; ring_nf

end DetANN.HPIM.QP

-- ===== QP_Main =====
namespace DetANN.HPIM.QP

open PNormReg PNormRegLib SmaleNinth

/-- After the bisection: clamp `L + 1` and look up the final index. -/
lemma seg_fin (m : ℕ) (IM : ℤ → ℤ) (MEM : ℤ → ℝ) (v : ℤ) (M L : ℕ) (hM1 : 1 ≤ M) (s : State)
    (hpc : s.core.pc = 58) (hC : Ctx m IM MEM s) (hv : s.core.ptrs 2 = v) (h15 : s.core.ptrs 15 = L)
    (h13 : s.core.ptrs 13 = (M : ℤ) - 1) :
    ∃ d, d ≤ 6 ∧ (run Qprog s detTape d).core.pc = 88 ∧ Ctx m IM MEM (run Qprog s detTape d) ∧
      (run Qprog s detTape d).core.ptrs 2 = v ∧
      (run Qprog s detTape d).core.ptrs 17 = ((min (L + 1) (M - 1) : ℕ) : ℤ) ∧
      (run Qprog s detTape d).core.ptrs 11 = ((3 : ℕ) : ℤ) ∧ (run Qprog s detTape d).work = s.work + d := by
  obtain ⟨hh, hmem, him, hM, hZ, hO, hT2⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at *
  subst hpc hh him; subst mem
  by_cases hc : ((L : ℤ) + 1) ≤ (M : ℤ) - 1
  · refine ⟨5, by omega, ?_⟩
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos (by simp [Function.update_apply, h15, h13]; omega)]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl, run_zero]
    refine ⟨rfl, by (refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_apply, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, if_false, *]), ?_, ?_, ?_, rfl⟩ <;> simp [Function.update_apply, hv, h15]
    omega
  · refine ⟨6, by omega, ?_⟩
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_neg (by simp [Function.update_apply, h15, h13]; omega)]
    (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); rw [if_pos le_rfl, run_zero]
    refine ⟨rfl, by (refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_apply, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, if_false, *]), ?_, ?_, ?_, rfl⟩ <;> simp [Function.update_apply, hv, h13]
    omega

lemma ansLt_eval {m n : ℕ} {T : BoxTree m} (h : T.AnsLt n) (q : Fin m → ℝ) {i : ℕ}
    (hi : T.eval q = some i) : i < n := by
  induction T with
  | leaf a =>
    cases a with
    | none => simp [BoxTree.eval] at hi
    | some j => simp [BoxTree.eval] at hi; rw [← hi]; exact h
  | test lo hi' y t ihy iht =>
    classical
    simp only [BoxTree.eval] at hi
    split_ifs at hi
    · exact ihy h.1 hi
    · exact iht h.2 hi

lemma lookup_eq {m M : ℕ} (Z : Fin M → BoxTree m) {i : ℕ} (h : i < M) (q : Fin m → ℝ) :
    lookup Z i q = (Z ⟨i, h⟩).eval q ∧ lookupCost Z i q = (Z ⟨i, h⟩).visits q := by
  unfold lookup lookupCost; rw [dif_pos h, dif_pos h]; exact ⟨rfl, rfl⟩


lemma visits_mul (m V : ℕ) : (13 * m + 20) * V ≤ 80 * (m + 1) * V := Nat.mul_le_mul_right _ (by omega)

/-- **The HPIM search loop** at `HN = 7`. -/
theorem hn_spec (m : ℕ) (s₀ : State) (q : Fin m → ℝ) (MEM : ℤ → ℝ)
    (hpos : ∀ z, 0 ≤ z → MEM z = s₀.core.mem z) (hq : ∀ j : Fin m, MEM (-1 - j) = q j) :
    ∀ v T, HTreeAt m s₀ v T → T.WF → ∀ s : State, s.core.pc = 7 → Ctx m s₀.integerMemory MEM s →
      s.core.ptrs 2 = v →
      ∃ n, n ≤ 80 * (m + 1) * T.cost q ∧ (run Qprog s detTape n).halted = true ∧
        (run Qprog s detTape n).core.ptrs 0 = ((T.search q : ℕ) : ℤ) ∧
        (run Qprog s detTape n).work = s.work + n := by
  intro v T hT
  induction hT with
  | single v k h0 h1 =>
    intro _ s hpc hC hv
    obtain ⟨a1, a2, a3⟩ := seg_single m _ MEM v s hpc hC hv h0
    refine ⟨6, ?_, a1, by rw [a2, h1]; simp [HTree.search], a3⟩
    simp only [HTree.cost]; nlinarith
  | node v n M t₀ Z glob kidOf reps h1 hMv h6 hpow hZ hglob hkid hreps ihk ihr =>
    intro hwf s hpc hC hv
    have hwf' : (∀ i, (Z i).AnsLt n) ∧ (∀ i, (kidOf i).WF) ∧ reps.WF := hwf
    obtain ⟨wZ, wK, wR⟩ := hwf'
    rcases Nat.eq_zero_or_pos M with hM0 | hM1
    · -- `M = 0`: straight to the representatives
      subst hM0
      obtain ⟨a1, aC, a2, aw⟩ := seg_m0 m _ MEM v s hpc hC hv h1 (by rw [hMv]; rfl)
      obtain ⟨n', hn', b1, b2, bw⟩ := ihr wR _ a1 aC a2
      have hl : lookup Z 0 q = none ∧ lookupCost Z 0 q = 0 := by simp [lookup, lookupCost]
      refine ⟨16 + n', ?_, ?_⟩
      · simp only [HTree.cost, hl.1, hl.2, Nat.zero_sub]
        nlinarith
      · rw [run_add]
        exact ⟨b1, by rw [b2]; simp [HTree.search, hl.1], by rw [bw, aw]; ring⟩
    · -- `M ≥ 1`: look up `Z_0`
      obtain ⟨a1, aC, a2, a17, a11, a13, aw⟩ := seg_m1 m _ MEM v M s hpc hC hv h1 hMv hM1
      have hZ0 : BoxTreeAt m s₀ (s₀.integerMemory (s₀.integerMemory (v + 2) + 0)) (Z ⟨0, hM1⟩) := by
        have := hZ ⟨0, hM1⟩; simpa using this
      obtain ⟨n1, hn1, r1, rC, r10, rk, rw1⟩ :=
        lookup_spec m s₀ q MEM hpos hq v 0 (Z ⟨0, hM1⟩) hZ0 0 (by norm_num) _ a1 aC a2 a17 a11
      have r2 := rk 2 (by simp); have r13 := rk 13 (by simp)
      rw [a2] at r2; rw [a13] at r13
      obtain ⟨hl0, hc0⟩ := lookup_eq Z hM1 q
      simp only [retLabel] at r1
      cases he0 : (Z ⟨0, hM1⟩).eval q with
      | some i =>
        have hin : i < n := ansLt_eval (wZ _) q he0
        rw [he0] at r10
        obtain ⟨b1, bC, b2, bw⟩ := seg_ret0_some m _ MEM v i _ r1 rC r2 (by rw [r10]; rfl)
        have hk := hkid ⟨i, hin⟩
        simp only at hk
        obtain ⟨n2, hn2, c1, c2, cw⟩ := ihk ⟨i, hin⟩ (wK _) _ b1 bC b2
        refine ⟨11 + n1 + 11 + n2, ?_, ?_⟩
        · have hcost : (HTree.node n M t₀ Z glob kidOf reps).cost q =
              1 + (Z ⟨0, hM1⟩).visits q + (kidOf ⟨i, hin⟩).cost q := by
            simp only [HTree.cost, hl0, hc0, he0, dif_pos hin]
          rw [hcost]
          have := visits_mul m ((Z ⟨0, hM1⟩).visits q)
          rw [mul_add, mul_add, mul_one]; linarith
        · rw [run_add, run_add, run_add]
          refine ⟨c1, ?_, ?_⟩
          · rw [c2]; simp [HTree.search, hl0, he0, dif_pos hin]
          · rw [cw, bw, rw1, aw]; ring
      | none =>
        rw [he0] at r10
        obtain ⟨b1, bC, b2, b17, b11, b13, bw⟩ :=
          seg_ret0_none m _ MEM v M _ r1 rC r2 (by rw [r10]; rfl) r13
        have hMm : M - 1 < M := by omega
        have hZ1 : BoxTreeAt m s₀ (s₀.integerMemory (s₀.integerMemory (v + 2) + ((M : ℤ) - 1)))
            (Z ⟨M - 1, hMm⟩) := by
          have := hZ ⟨M - 1, hMm⟩; simp only at this; rwa [Nat.cast_sub hM1, Nat.cast_one] at this
        obtain ⟨n2, hn2, s1, sC, s10, sk, sw⟩ :=
          lookup_spec m s₀ q MEM hpos hq v ((M : ℤ) - 1) (Z ⟨M - 1, hMm⟩) hZ1 1 (by norm_num) _ b1 bC b2 b17 b11
        have s2 := sk 2 (by simp); have s13 := sk 13 (by simp)
        rw [b2] at s2; rw [b13] at s13
        obtain ⟨hl1, hc1⟩ := lookup_eq Z hMm q
        simp only [retLabel] at s1
        cases he1 : (Z ⟨M - 1, hMm⟩).eval q with
        | none =>
          rw [he1] at s10
          obtain ⟨d1, dC, d2, dw⟩ := seg_ret1_none m _ MEM v _ s1 sC s2 (by rw [s10]; rfl)
          obtain ⟨n3, hn3, e1, e2, ew⟩ := ihr wR _ d1 dC d2
          refine ⟨11 + n1 + 4 + n2 + 9 + n3, ?_, ?_⟩
          · have hcost : (HTree.node n M t₀ Z glob kidOf reps).cost q =
                1 + (Z ⟨0, hM1⟩).visits q + ((Z ⟨M - 1, hMm⟩).visits q + reps.cost q) := by
              simp only [HTree.cost, hl0, hc0, he0, hl1, hc1, he1]
            rw [hcost]
            have := visits_mul m ((Z ⟨0, hM1⟩).visits q)
            have := visits_mul m ((Z ⟨M - 1, hMm⟩).visits q)
            rw [mul_add, mul_add, mul_add, mul_add, mul_one]; linarith
          · rw [run_add, run_add, run_add, run_add, run_add]
            refine ⟨e1, ?_, ?_⟩
            · rw [e2]; simp [HTree.search, hl0, he0, hl1, he1]
            · rw [ew, dw, sw, bw, rw1, aw]; ring
        | some j =>
          rw [he1] at s10
          obtain ⟨d1, dC, d2, d14, d15, d13, dw⟩ :=
            seg_ret1_some m _ MEM v M j _ s1 sC s2 (by rw [s10]; rfl) s13
          rw [h6] at d14
          obtain ⟨n4, L, hn4, hL, f1, fC, f15, f2, f13, fw⟩ :=
            bisect_spec m s₀ q MEM hpos hq v M t₀ hM1 Z hZ hpow t₀ 0 le_rfl _ d1 dC d2 d14 d15 d13
          obtain ⟨d, hd, g1, gC, g2, g17, g11, gw⟩ := seg_fin m _ MEM v M L hM1 _ f1 fC f2 f15 f13
          set idx := min (L + 1) (M - 1) with hidx
          have hidxM : idx < M := by omega
          have hZ3 : BoxTreeAt m s₀ (s₀.integerMemory (s₀.integerMemory (v + 2) + (idx : ℤ)))
              (Z ⟨idx, hidxM⟩) := hZ ⟨idx, hidxM⟩
          obtain ⟨n6, hn6, k1, kC, k10, kk, kw⟩ :=
            lookup_spec m s₀ q MEM hpos hq v idx (Z ⟨idx, hidxM⟩) hZ3 3 le_rfl _ g1 gC g2 g17 g11
          simp only [retLabel] at k1
          have k2 := kk 2 (by simp)
          rw [g2] at k2
          obtain ⟨hlC, hcC⟩ := lookupC_eq Z hM1 (L + 1) q
          have hcost : (HTree.node n M t₀ Z glob kidOf reps).cost q =
              1 + (Z ⟨0, hM1⟩).visits q + ((Z ⟨M - 1, hMm⟩).visits q +
                (bisectCost Z q t₀ 0 + (Z ⟨idx, hidxM⟩).visits q)) := by
            simp only [HTree.cost, hl0, hc0, he0, hl1, hc1, he1, hL, hcC]; rfl
          have hbound : ∀ e, e ≤ 10 → 11 + n1 + 4 + n2 + 10 + n4 + d + n6 + e ≤
              80 * (m + 1) * (HTree.node n M t₀ Z glob kidOf reps).cost q := by
            intro e he
            rw [hcost]
            have := visits_mul m ((Z ⟨0, hM1⟩).visits q)
            have := visits_mul m ((Z ⟨M - 1, hMm⟩).visits q)
            have := visits_mul m ((Z ⟨idx, hidxM⟩).visits q)
            rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_one]; linarith
          cases he3 : (Z ⟨idx, hidxM⟩).eval q with
          | none =>
            rw [he3] at k10
            obtain ⟨l1, l2, lw⟩ := seg_ret3_none m _ MEM _ k1 kC (by rw [k10]; rfl)
            refine ⟨11 + n1 + 4 + n2 + 10 + n4 + d + n6 + 3, hbound 3 (by norm_num), ?_⟩
            rw [run_add, run_add, run_add, run_add, run_add, run_add, run_add, run_add]
            refine ⟨l1, ?_, ?_⟩
            · rw [l2]; simp [HTree.search, hl0, he0, hl1, he1, hL, hlC, ← hidx, he3]
            · rw [lw, kw, gw, fw, dw, sw, bw, rw1, aw]; ring
          | some i =>
            rw [he3] at k10
            have hin : i < n := ansLt_eval (wZ _) q he3
            obtain ⟨l1, l2, lw⟩ := seg_ret3_some m _ MEM v i _ k1 kC k2 (by rw [k10]; rfl)
            refine ⟨11 + n1 + 4 + n2 + 10 + n4 + d + n6 + 10, hbound 10 le_rfl, ?_⟩
            rw [run_add, run_add, run_add, run_add, run_add, run_add, run_add, run_add]
            refine ⟨l1, ?_, ?_⟩
            · rw [l2, hglob ⟨i, hin⟩]
              simp [HTree.search, hl0, he0, hl1, he1, hL, hlC, ← hidx, he3, globOf, dif_pos hin]
            · rw [lw, kw, gw, fw, dw, sw, bw, rw1, aw]; ring

end DetANN.HPIM.QP

-- ===== QP_Final =====
namespace DetANN.HPIM.QP

open PNormReg PNormRegLib SmaleNinth

lemma cost_pos {m : ℕ} (T : HTree m) (q : Fin m → ℝ) : 1 ≤ T.cost q := by
  cases T with
  | single k => simp [HTree.cost]
  | node => simp only [HTree.cost]; omega

lemma qprog_det : DetProgram Qprog := by
  refine ⟨?_, ?_⟩
  · intro op hop
    simp only [Qprog, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> trivial
  · intro op hop
    simp only [Qprog, List.mem_cons, List.not_mem_nil, or_false] at hop
    refine ⟨fun r h => ?_, fun r a e h => ?_⟩ <;> subst h <;> simp at hop

/-- The seven initial steps: constants, `p1 = I[1]`, `p2 = I[2]`. -/
lemma seg_init (m : ℕ) (s₀ : State) (q : EuclideanSpace ℝ (Fin m)) (hm : s₀.integerMemory 1 = m) :
    let s := queryState m s₀ q
    (run Qprog s detTape 7).core.pc = 7 ∧
      Ctx m s₀.integerMemory s.core.mem (run Qprog s detTape 7) ∧
      (run Qprog s detTape 7).core.ptrs 2 = s₀.integerMemory 2 ∧ (run Qprog s detTape 7).work = 7 := by
  intro s
  simp only [s, queryState]
  (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec]); (rw [run_exec rfl rfl]; simp only [exec, coreExec])
  rw [run_zero]
  refine ⟨rfl, ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩, ?_, rfl⟩ <;> simp [Function.update_apply, hm]

end DetANN.HPIM.QP

open DetANN DetANN.HPIM DetANN.HPIM.QP PNormReg in
theorem solution :
    ∃ Qry : PNormReg.Program, DetProgram Qry ∧ ∃ c₀ : ℕ,
      ∀ (m : ℕ) (s : PNormReg.State) (T : HTree m) (q : EuclideanSpace ℝ (Fin m)),
        1 ≤ m → T.WF → s.integerMemory 1 = m → HTreeAt m s (s.integerMemory 2) T →
        ∃ t : ℕ,
          (PNormReg.run Qry (queryState m s q) detTape t).halted = true ∧
          (PNormReg.run Qry (queryState m s q) detTape t).work ≤ c₀ * (m + 1) * T.cost q ∧
          (PNormReg.run Qry (queryState m s q) detTape t).core.ptrs 0 = T.search q := by
  refine ⟨Qprog, qprog_det, 87, ?_⟩
  intro m s T q _ hwf hm hT
  obtain ⟨a1, aC, a2, aw⟩ := seg_init m s q hm
  have hpos : ∀ z, 0 ≤ z → (queryState m s q).core.mem z = s.core.mem z := by
    intro z hz
    simp only [queryState]
    rw [dif_neg (fun h => by omega)]
  have hq : ∀ j : Fin m, (queryState m s q).core.mem (-1 - j) = q j := by
    intro j
    simp only [queryState]
    rw [dif_pos ⟨by omega, by simp⟩]
    exact congrArg (fun i => q i) (Fin.ext (by simp))
  obtain ⟨n, hn, b1, b2, bw⟩ :=
    hn_spec m s q (queryState m s q).core.mem hpos hq _ T hT hwf _ a1 aC a2
  refine ⟨7 + n, ?_, ?_, ?_⟩
  · rw [run_add]; exact b1
  · rw [run_add, bw, aw]
    have := cost_pos T q
    nlinarith
  · rw [run_add]; exact b2
