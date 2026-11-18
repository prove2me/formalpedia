-- Prove2me | solution 1 for DetANN.HPIM.median_block
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T10:28:26.254003+00:00
-- url     : https://prove2.me/submissions/d27cc802-7267-4ed9-9f47-b27c590ee65d

import Mathlib
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

-- ===== PP_Prog =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth

/-- Driver segment 2 (58 instructions). Labels: PWL = off + 6, PWB = off + 8, PWE = off + 13, RSL = off + 17, RSE = off + 22, NODE = off + 39, INNER = off + 54. -/
def seg2 (off RETURN : ℕ) : Program :=
  [ .pointerAdd 9 12 23,
    .core (.pset 6 (3)),
    .integerStore 6 9,
    .core (.pset 3 (0)),
    .core (.pset 6 (1)),
    .core (.pcopy 7 9),
    .core (.pjle 3 42 (off + 8)),
    .core (.pjle 0 0 (off + 13)),
    .integerStore 7 6,
    .pointerAdd 6 6 6,
    .core (.pinc 7),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 6)),
    .core (.pcopy 15 7),
    .core (.pcopy 10 15),
    .core (.pset 3 (0)),
    .core (.pcopy 7 10),
    .core (.pjle 23 3 (off + 22)),
    .integerStore 7 3,
    .core (.pinc 7),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 17)),
    .core (.pcopy 2 7),
    .core (.pset 27 (3)),
    .pointerAdd 6 2 27,
    .integerStore 6 10,
    .core (.pset 27 (7)),
    .pointerAdd 6 2 27,
    .integerStore 6 23,
    .core (.pset 27 (8)),
    .pointerAdd 15 2 27,
    .core (.pset 6 (2)),
    .integerStore 6 2,
    .core (.pset 8 (-10)),
    .core (.pset 6 (0)),
    .integerStore 8 6,
    .core (.pcopy 13 8),
    .core (.pset 14 (0)),
    .core (.pjle 0 0 (off + 39)),
    .core (.pset 27 (3)),
    .pointerAdd 6 2 27,
    .integerLoad 10 6,
    .core (.pset 27 (7)),
    .pointerAdd 6 2 27,
    .integerLoad 11 6,
    .core (.pset 27 (2)),
    .core (.pjle 27 11 (off + 54)),
    .core (.pset 6 (0)),
    .integerStore 2 6,
    .integerLoad 6 10,
    .core (.pcopy 7 2),
    .core (.pinc 7),
    .integerStore 7 6,
    .core (.pjle 0 0 (RETURN)),
    .core (.pset 6 (1)),
    .integerStore 2 6,
    .core (.pcopy 20 13),
    .core (.pcopy 28 14) ]

/-- Driver segment 8 (0 instructions). Labels: . -/
def seg8 (off : ℕ) : Program :=
  [  ]

namespace Blocks

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

lemma det_append {A B : Program} (hA : DetProgram A) (hB : DetProgram B) : DetProgram (A ++ B) := by
  refine ⟨fun op hop => ?_, fun op hop => ?_⟩
  · rcases List.mem_append.1 hop with h | h
    · exact hA.1 op h
    · exact hB.1 op h
  · rcases List.mem_append.1 hop with h | h
    · exact hA.2 op h
    · exact hB.2 op h

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

end Comp

section Ladder

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

end Ladder

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

-- ===== CB_Prog =====
namespace DetANN.HPIM.CB

open PNormReg PNormRegLib DetANN DetANN.HPIM

/-- The components block at offset `off` (51 instructions). -/
def cb (off : ℕ) : Program :=
  [ .core (.mul 43 10 10),              -- 0   d²
    .core (.pset 41 0),                 -- 1   a := 0
    .core (.pjle 11 41 (off + 8)),      -- 2   INIT: n ≤ a → 8
    .pointerSub 44 13 41,               -- 3
    .core (.pdec 44),                   -- 4   p44 = Z − 1 − a
    .integerStore 44 41,                -- 5   lab a := a
    .core (.pinc 41),                   -- 6
    .core (.pjle 41 41 (off + 2)),      -- 7
    .core (.pset 40 0),                 -- 8   r := 0
    .core (.pjle 11 40 (off + 51)),     -- 9   ROUND: n ≤ r → END
    .core (.pset 41 0),                 -- 10  a := 0
    .core (.pjle 11 41 (off + 49)),     -- 11  A: n ≤ a → A_E
    .pointerAdd 47 10 41,               -- 12
    .integerLoad 47 47,                 -- 13
    .pointerAdd 47 12 47,               -- 14
    .integerLoad 45 47,                 -- 15  p45 = address of a
    .pointerSub 44 13 41,               -- 16
    .core (.pdec 44),                   -- 17  p44 = Z − 1 − a
    .core (.pset 42 0),                 -- 18  b := 0
    .core (.pjle 11 42 (off + 47)),     -- 19  B: n ≤ b → B_E
    .pointerAdd 47 10 42,               -- 20
    .integerLoad 47 47,                 -- 21
    .pointerAdd 47 12 47,               -- 22
    .integerLoad 46 47,                 -- 23  p46 = address of b
    .core (.const 40 0),                -- 24  acc := 0
    .core (.pset 43 0),                 -- 25  j := 0
    .core (.pjle 1 43 (off + 36)),      -- 26  J: m ≤ j → J_E
    .pointerAdd 47 45 43,               -- 27
    .core (.load 41 47),                -- 28
    .pointerAdd 47 46 43,               -- 29
    .core (.load 42 47),                -- 30
    .core (.sub 41 41 42),              -- 31
    .core (.mul 41 41 41),              -- 32
    .core (.add 40 40 41),              -- 33  acc += (A_j − B_j)²
    .core (.pinc 43),                   -- 34
    .core (.pjle 43 43 (off + 26)),     -- 35
    .core (.sub 41 40 43),              -- 36  J_E: acc − d²
    .core (.jle 41 (off + 39)),         -- 37  edge → 39
    .core (.pjle 42 42 (off + 45)),     -- 38  no edge → NB
    .integerLoad 48 44,                 -- 39  p48 = lab a
    .pointerSub 49 13 42,               -- 40
    .core (.pdec 49),                   -- 41
    .integerLoad 49 49,                 -- 42  p49 = lab b
    .core (.pjle 48 49 (off + 45)),     -- 43  lab a ≤ lab b → NB
    .integerStore 44 49,                -- 44  lab a := lab b
    .core (.pinc 42),                   -- 45  NB
    .core (.pjle 42 42 (off + 19)),     -- 46
    .core (.pinc 41),                   -- 47  B_E
    .core (.pjle 41 41 (off + 11)),     -- 48
    .core (.pinc 40),                   -- 49  A_E
    .core (.pjle 40 40 (off + 9)) ]     -- 50

lemma cb_len (off : ℕ) : (cb off).length = 51 := rfl

lemma cb_det (off : ℕ) : DetProgram (cb off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold cb at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)

end DetANN.HPIM.CB

-- ===== CB_Math =====
namespace DetANN.HPIM.CB

open DetANN.HPIM Classical

variable {m n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ)

/-- The point with a natural-number index (`0` outside the range). -/
noncomputable def pt (i : ℕ) : EuclideanSpace ℝ (Fin m) := if h : i < n then pts ⟨i, h⟩ else 0

/-- The (reflexive) threshold relation on indices. -/
def edge (a b : ℕ) : Prop := dist (pt pts a) (pt pts b) ≤ d

/-- One relaxation step. -/
noncomputable def relax (a b : ℕ) (f : ℕ → ℕ) : ℕ → ℕ :=
  if edge pts d a b ∧ f b < f a then Function.update f a (f b) else f

/-- The pairs `(a, b)` relaxed for a fixed `a`, from `b₀` on. -/
def bList (a b₀ : ℕ) : List (ℕ × ℕ) := (List.range' b₀ (n - b₀)).map (fun b => (a, b))

/-- Fold the relaxations over a list of pairs. -/
noncomputable def relaxL (L : List (ℕ × ℕ)) (f : ℕ → ℕ) : ℕ → ℕ :=
  L.foldl (fun g p => relax pts d p.1 p.2 g) f

/-- The sweep of one `a` over `b ∈ [b₀, n)`. -/
noncomputable def bsweep (a b₀ : ℕ) (f : ℕ → ℕ) : ℕ → ℕ := relaxL pts d (bList (n := n) a b₀) f

/-- The sweep over `a ∈ [a₀, n)`. -/
noncomputable def asweep (a₀ : ℕ) (f : ℕ → ℕ) : ℕ → ℕ :=
  (List.range' a₀ (n - a₀)).foldl (fun g a => bsweep pts d a 0 g) f

/-- `k` rounds. -/
noncomputable def rounds (k : ℕ) (f : ℕ → ℕ) : ℕ → ℕ := (asweep pts d 0)^[k] f

lemma bsweep_step (a b : ℕ) (hb : b < n) (f : ℕ → ℕ) :
    bsweep pts d a b f = bsweep pts d a (b + 1) (relax pts d a b f) := by
  unfold bsweep bList relaxL
  rw [show n - b = (n - (b + 1)) + 1 by omega, List.range'_succ]
  simp

lemma bsweep_end (a b : ℕ) (hb : n ≤ b) (f : ℕ → ℕ) : bsweep pts d a b f = f := by
  unfold bsweep bList relaxL
  rw [show n - b = 0 by omega]
  simp

lemma asweep_step (a : ℕ) (ha : a < n) (f : ℕ → ℕ) :
    asweep pts d a f = asweep pts d (a + 1) (bsweep pts d a 0 f) := by
  unfold asweep
  rw [show n - a = (n - (a + 1)) + 1 by omega, List.range'_succ]
  simp

lemma asweep_end (a : ℕ) (ha : n ≤ a) (f : ℕ → ℕ) : asweep pts d a f = f := by
  unfold asweep
  rw [show n - a = 0 by omega]
  simp

lemma relax_le (a b : ℕ) (f : ℕ → ℕ) (x : ℕ) : relax pts d a b f x ≤ f x := by
  unfold relax
  split_ifs with h
  · rcases eq_or_ne x a with rfl | hx
    · simp only [Function.update_self]; exact h.2.le
    · rw [Function.update_of_ne hx]
  · exact le_rfl

lemma relax_at (a b : ℕ) (f : ℕ → ℕ) (h : edge pts d a b) : relax pts d a b f a ≤ f b := by
  unfold relax
  split_ifs with h'
  · simp
  · push_neg at h'
    exact h' h

lemma relaxL_le (L : List (ℕ × ℕ)) : ∀ (f : ℕ → ℕ) (x : ℕ), relaxL pts d L f x ≤ f x := by
  induction L with
  | nil => intro f x; exact le_rfl
  | cons p L ih =>
    intro f x
    unfold relaxL at ih ⊢
    rw [List.foldl_cons]
    exact (ih _ x).trans (relax_le pts d _ _ f x)

lemma relaxL_pair (L : List (ℕ × ℕ)) : ∀ (f : ℕ → ℕ) (a b : ℕ), (a, b) ∈ L → edge pts d a b →
    relaxL pts d L f a ≤ f b := by
  induction L with
  | nil => intro f a b h; simp at h
  | cons p L ih =>
    intro f a b hm he
    unfold relaxL at ih ⊢
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hm with rfl | hm
    · exact (relaxL_le pts d L _ a).trans (relax_at pts d a b f he)
    · exact (ih _ a b hm he).trans (relax_le pts d _ _ f b)

/-- A sweep is a fold over all pairs. -/
lemma asweep_eq (a₀ : ℕ) (f : ℕ → ℕ) :
    asweep pts d a₀ f =
      relaxL pts d ((List.range' a₀ (n - a₀)).flatMap (fun a => bList (n := n) a 0)) f := by
  unfold asweep relaxL bsweep relaxL
  rw [List.foldl_flatMap]

lemma mem_pairs (a b : ℕ) (ha : a < n) (hb : b < n) :
    (a, b) ∈ (List.range' 0 (n - 0)).flatMap (fun a => bList (n := n) a 0) := by
  simp only [List.mem_flatMap, List.mem_range'_1, bList, List.mem_map, Prod.mk.injEq]
  exact ⟨a, ⟨by omega, by omega⟩, b, ⟨by omega, by omega⟩, rfl, rfl⟩

lemma asweep_le (f : ℕ → ℕ) (x : ℕ) : asweep pts d 0 f x ≤ f x := by
  rw [asweep_eq]; exact relaxL_le pts d _ f x

lemma asweep_pair (f : ℕ → ℕ) (a b : ℕ) (ha : a < n) (hb : b < n) (he : edge pts d a b) :
    asweep pts d 0 f a ≤ f b := by
  rw [asweep_eq]; exact relaxL_pair pts d _ f a b (mem_pairs a b ha hb) he

lemma rounds_le (k : ℕ) : ∀ x, rounds pts d k (fun i => i) x ≤ x := by
  induction k with
  | zero => intro x; exact le_rfl
  | succ k ih =>
    intro x
    unfold rounds at ih ⊢
    rw [Function.iterate_succ_apply']
    exact (asweep_le pts d _ x).trans (ih x)

lemma pt_of_lt (i : ℕ) (h : i < n) : pt pts i = pts ⟨i, h⟩ := by unfold pt; rw [dif_pos h]

lemma reach_of_edge (a b : ℕ) (ha : a < n) (hb : b < n) (he : edge pts d a b) :
    thrReach pts d ⟨a, ha⟩ ⟨b, hb⟩ := by
  rcases eq_or_ne a b with rfl | hne
  · exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.fromRel_adj]
    refine ⟨fun h => hne (congrArg Fin.val h), Or.inl ?_⟩
    have := he; unfold edge at this; rwa [pt_of_lt pts a ha, pt_of_lt pts b hb] at this

/-- Labels are indices of points in the same component. -/
def Sound (f : ℕ → ℕ) : Prop := ∀ a (ha : a < n), ∃ hf : f a < n, thrReach pts d ⟨a, ha⟩ ⟨f a, hf⟩

lemma sound_id : Sound pts d (fun i => i) := fun a ha => ⟨ha, SimpleGraph.Reachable.refl _⟩

lemma sound_relax (a b : ℕ) (ha : a < n) (hb : b < n) (f : ℕ → ℕ) (hf : Sound pts d f) :
    Sound pts d (relax pts d a b f) := by
  unfold relax
  split_ifs with h
  · intro x hx
    rcases eq_or_ne x a with rfl | hxa
    · simp only [Function.update_self]
      obtain ⟨hfb, hr⟩ := hf b hb
      exact ⟨hfb, (reach_of_edge pts d x b hx hb h.1).trans hr⟩
    · rw [Function.update_of_ne hxa]; exact hf x hx
  · exact hf

lemma sound_relaxL (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, p.1 < n ∧ p.2 < n) :
    ∀ f, Sound pts d f → Sound pts d (relaxL pts d L f) := by
  induction L with
  | nil => intro f hf; exact hf
  | cons p L ih =>
    intro f hf
    unfold relaxL at ih ⊢
    rw [List.foldl_cons]
    have hp := hL p (List.mem_cons_self ..)
    exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) _ (sound_relax pts d _ _ hp.1 hp.2 f hf)

lemma sound_rounds (k : ℕ) : Sound pts d (rounds pts d k (fun i => i)) := by
  induction k with
  | zero => exact sound_id pts d
  | succ k ih =>
    unfold rounds at ih ⊢
    rw [Function.iterate_succ_apply', asweep_eq]
    refine sound_relaxL pts d _ ?_ _ ih
    intro p hp
    simp only [List.mem_flatMap, List.mem_range'_1, bList, List.mem_map] at hp
    obtain ⟨a, ⟨_, ha⟩, b, ⟨_, hb⟩, rfl⟩ := hp
    exact ⟨by omega, by omega⟩

lemma edge_of_adj (a b : Fin n)
    (h : (SimpleGraph.fromRel fun a b : Fin n => dist (pts a) (pts b) ≤ d).Adj a b) :
    edge pts d a b := by
  rw [SimpleGraph.fromRel_adj] at h
  unfold edge
  rw [pt_of_lt pts a a.isLt, pt_of_lt pts b b.isLt]
  rcases h.2 with h | h
  · exact h
  · rwa [dist_comm]

lemma rounds_walk (k : ℕ) : ∀ (a j : Fin n)
    (w : (SimpleGraph.fromRel fun a b : Fin n => dist (pts a) (pts b) ≤ d).Walk a j),
    w.length ≤ k → rounds pts d k (fun i => i) a ≤ j := by
  induction k with
  | zero =>
    intro a j w hw
    have : w.length = 0 := by omega
    have hj := SimpleGraph.Walk.eq_of_length_eq_zero this
    subst hj
    exact rounds_le pts d 0 a
  | succ k ih =>
    intro a j w hw
    unfold rounds at ih ⊢
    rw [Function.iterate_succ_apply']
    cases w with
    | nil => exact (asweep_le pts d _ a).trans (rounds_le pts d k a)
    | cons hadj w' =>
      rename_i b
      have h1 := asweep_pair pts d ((asweep pts d 0)^[k] (fun i => i)) a b a.isLt b.isLt
        (edge_of_adj pts d a b hadj)
      have h2 := ih b j w' (by simp at hw; omega)
      exact h1.trans h2

/-- **Label propagation computes `compMin`.** -/
theorem rounds_eq_compMin (a : Fin n) : rounds pts d n (fun i => i) a = compMin pts d a := by
  set g := rounds pts d n (fun i => i)
  obtain ⟨hga, hr⟩ := sound_rounds pts d n a a.isLt
  unfold compMin
  set F := Finset.univ.filter (thrReach pts d a)
  have hmem : (⟨g a, hga⟩ : Fin n) ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, hr⟩
  apply le_antisymm
  · -- the least member is reached by a path, of length `< n`
    have hmin := Finset.min'_mem F ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      SimpleGraph.Reachable.refl _⟩⟩
    obtain ⟨w⟩ := (Finset.mem_filter.1 hmin).2
    have hp := w.toPath.2
    have hl := hp.length_lt
    simp only [Fintype.card_fin] at hl
    exact rounds_walk pts d n a _ w.toPath.1 hl.le
  · exact_mod_cast Finset.min'_le F _ hmem

end DetANN.HPIM.CB

-- ===== CB_Loops =====
namespace DetANN.HPIM.CB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

/-- The squared-distance loop (`J`, offsets 26–35): from `j`, it adds `(A_i − B_i)²` for `i ∈ [j, m)`. -/
lemma j_loop (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) (m : ℕ) (A B : ℤ) :
    ∀ k (j : ℕ) (acc : ℝ) (s : State), j + k = m →
      s.core.pc = off + 26 → s.halted = false → s.core.ptrs 1 = m → s.core.ptrs 43 = j →
      s.core.ptrs 45 = A → s.core.ptrs 46 = B → s.core.regs 40 = acc →
      (run Q s detTape (10 * k + 1)).core.pc = off + 36 ∧
      (run Q s detTape (10 * k + 1)).halted = false ∧
      (run Q s detTape (10 * k + 1)).core.regs 40 =
        acc + ∑ i ∈ Finset.range k,
          (s.core.mem (A + ((j + i : ℕ) : ℤ)) - s.core.mem (B + ((j + i : ℕ) : ℤ))) ^ 2 ∧
      (run Q s detTape (10 * k + 1)).core.ptrs 43 = m ∧
      (∀ x, x ≠ 43 → x ≠ 47 → (run Q s detTape (10 * k + 1)).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 40 → x ≠ 41 → x ≠ 42 → (run Q s detTape (10 * k + 1)).core.regs x = s.core.regs x) ∧
      (run Q s detTape (10 * k + 1)).core.mem = s.core.mem ∧
      (run Q s detTape (10 * k + 1)).integerMemory = s.integerMemory ∧
      (run Q s detTape (10 * k + 1)).work = s.work + (10 * k + 1) ∧
      cellsWritten Q s (10 * k + 1) = ∅ := by
  intro k
  induction k with
  | zero =>
    intro j acc s hjk hpc hh h1 h43 h45 h46 h40
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h1 h43 h45 h46 h40; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h1, h43]; omega)]
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp [h40], by simp only; rw [h43]; omega, fun x _ _ => rfl,
      fun x _ _ _ => rfl, rfl, rfl, rfl, by simp⟩
  | succ k ih =>
    intro j acc s hjk hpc hh h1 h43 h45 h46 h40
    -- one iteration: 10 steps back to `off + 26`
    have it : (run Q s detTape 10).core.pc = off + 26 ∧ (run Q s detTape 10).halted = false ∧
        (run Q s detTape 10).core.ptrs 43 = ((j + 1 : ℕ) : ℤ) ∧
        (run Q s detTape 10).core.regs 40 =
          acc + (s.core.mem (A + (j : ℤ)) - s.core.mem (B + (j : ℤ))) ^ 2 ∧
        (∀ x, x ≠ 43 → x ≠ 47 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 40 → x ≠ 41 → x ≠ 42 → (run Q s detTape 10).core.regs x = s.core.regs x) ∧
        (run Q s detTape 10).core.mem = s.core.mem ∧
        (run Q s detTape 10).integerMemory = s.integerMemory ∧
        (run Q s detTape 10).work = s.work + 10 ∧ cellsWritten Q s 10 = ∅ := by
      obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
      simp only at hpc hh h1 h43 h45 h46 h40 ⊢; subst hpc hh
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell]
      rw [if_neg (by rw [h1, h43]; push_cast; omega)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_zero, cw_zero]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, by simp⟩
      · simp [h43]
      · simp [h40, h45, h46, h43]; ring
      · intro x h1 h2; simp [h1, h2]
      · intro x h1 h2 h3; simp [h1, h2, h3]
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := it
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
      ih (j + 1) _ (run Q s detTape 10) (by omega) i1 i2 (by rw [i5 1 (by norm_num) (by norm_num), h1])
        i3 (by rw [i5 45 (by norm_num) (by norm_num), h45]) (by rw [i5 46 (by norm_num) (by norm_num), h46]) i4
    have RR : run Q s detTape (10 * (k + 1) + 1) = run Q (run Q s detTape 10) detTape (10 * k + 1) := by
      rw [← run_add]; congr 1; ring
    have CW : cellsWritten Q s (10 * (k + 1) + 1) =
        cellsWritten Q s 10 ∪ cellsWritten Q (run Q s detTape 10) (10 * k + 1) := by
      rw [← cellsWritten_add]; congr 1; ring
    rw [RR]
    refine ⟨c1, c2, ?_, c4, ?_, ?_, by rw [c7, i7], by rw [c8, i8], by rw [c9, i9]; ring, ?_⟩
    · rw [c3, i7, Finset.sum_range_succ']
      simp only [Nat.add_zero, add_zero]
      have e : ∀ i, j + 1 + i = j + (i + 1) := fun i => by omega
      simp only [e]; ring
    · intro x h1 h2; rw [c5 x h1 h2, i5 x h1 h2]
    · intro x h1 h2 h3; rw [c6 x h1 h2 h3, i6 x h1 h2 h3]
    · rw [CW, i10, c10]; simp

/-- After the distance loop (offsets 36–46): test the edge, compare the labels, maybe store, and
step `b`. -/
lemma pair_tail (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) (n : ℕ) (Z : ℤ)
    (f : ℕ → ℕ) (a b : ℕ) (ha : a < n) (hb : b < n) (S D2 : ℝ) (s : State)
    (hpc : s.core.pc = off + 36) (hh : s.halted = false) (h13 : s.core.ptrs 13 = Z)
    (h42 : s.core.ptrs 42 = b) (h44 : s.core.ptrs 44 = Z - 1 - a) (h40 : s.core.regs 40 = S)
    (h43 : s.core.regs 43 = D2) (hL : ∀ i < n, s.integerMemory (Z - 1 - i) = f i) :
    ∃ t, t ≤ 10 ∧ (run Q s detTape t).core.pc = off + 19 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 42 = ((b + 1 : ℕ) : ℤ) ∧
      (∀ x, x ≠ 42 → x ≠ 48 → x ≠ 49 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 41 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).integerMemory =
        (if S ≤ D2 ∧ f b < f a then Function.update s.integerMemory (Z - 1 - a) (f b)
          else s.integerMemory) ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, c = (false, Z - 1 - a) := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h13 h42 h44 h40 h43 hL ⊢; subst hpc hh
  have la : im (Z - 1 - a) = f a := hL a ha
  have lb : im (Z - b - 1) = f b := by rw [show Z - b - 1 = Z - 1 - b by ring]; exact hL b hb
  by_cases hS : S ≤ D2
  · by_cases hf : f b < f a
    · refine ⟨10, by norm_num, ?_⟩
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell]
      rw [if_pos (by simp [h40, h43]; linarith)]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell, Function.update_apply]
      simp (config := {decide := true}) only [if_true, if_false, h44, h13, h42, la, lb]
      rw [if_neg (by push_cast; omega)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_zero, cw_zero]
      refine ⟨rfl, rfl, by simp [h42], ?_, ?_, rfl, ?_, by simp, ?_⟩
      · intro x h1 h2 h3; simp [h1, h2, h3]
      · intro x h1; simp [h1]
      · rw [if_pos ⟨hS, hf⟩]; simp [h44, h13, h42, lb]
      · intro c hc; simp [h44] at hc; exact hc
    · refine ⟨9, by norm_num, ?_⟩
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell]
      rw [if_pos (by simp [h40, h43]; linarith)]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell, Function.update_apply]
      simp (config := {decide := true}) only [if_true, if_false, h44, h13, h42, la, lb]
      rw [if_pos (by push_cast; omega)]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_zero, cw_zero]
      refine ⟨rfl, rfl, by simp [h42], ?_, ?_, rfl, ?_, by simp, ?_⟩
      · intro x h1 h2 h3; simp [h1, h2, h3]
      · intro x h1; simp [h1]
      · rw [if_neg (fun h => hf h.2)]
      · intro c hc; simp at hc
  · refine ⟨5, by norm_num, ?_⟩
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_neg (by simp [h40, h43]; linarith [not_le.1 hS])]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp [h42], ?_, ?_, rfl, ?_, by simp, ?_⟩
    · intro x h1 h2 h3; simp [h1, h2, h3]
    · intro x h1; simp [h1]
    · rw [if_neg (fun h => hS h.1)]
    · intro c hc; simp at hc

/-- `LocalPts` survives any run that keeps the low pointers, the real memory and the cells `≥ 0`. -/
lemma lp_transfer {m n : ℕ} {P : Fin n → Fin m → ℝ} {s s' : State} (h : LocalPts s P)
    (hp : ∀ x < 40, s'.core.ptrs x = s.core.ptrs x) (hm : s'.core.mem = s.core.mem)
    (hi : ∀ z, 0 ≤ z → s'.integerMemory z = s.integerMemory z) : LocalPts s' P := by
  obtain ⟨h1, h11, h10, h12, hpts⟩ := h
  refine ⟨by rw [hp 1 (by norm_num), h1], by rw [hp 11 (by norm_num), h11],
    by rw [hp 10 (by norm_num)]; exact h10, by rw [hp 12 (by norm_num)]; exact h12, fun i => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hpts i
  have q1 : s'.integerMemory (s'.core.ptrs 10 + i) = s.integerMemory (s.core.ptrs 10 + i) := by
    rw [hp 10 (by norm_num)]; exact hi _ (by positivity)
  have q2 : s'.integerMemory (s'.core.ptrs 12 + s'.integerMemory (s'.core.ptrs 10 + i)) =
      s.integerMemory (s.core.ptrs 12 + s.integerMemory (s.core.ptrs 10 + i)) := by
    rw [q1, hp 12 (by norm_num)]; exact hi _ (by positivity)
  refine ⟨by rw [q1]; exact e1, by rw [q2]; exact e2, fun j => ?_⟩
  rw [q2, hm]; exact e3 j

/-- The address of point `i`. -/
def addr (s : State) (i : ℕ) : ℤ := s.integerMemory (s.core.ptrs 12 + s.integerMemory (s.core.ptrs 10 + i))

lemma addr_pts {m n : ℕ} {pts : Fin n → EuclideanSpace ℝ (Fin m)} {s : State}
    (h : LocalPts s (fun i j => pts i j)) (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < m) :
    s.core.mem (addr s i + j) = pts ⟨i, hi⟩ ⟨j, hj⟩ := (h.2.2.2.2 ⟨i, hi⟩).2.2 ⟨j, hj⟩

lemma edge_iff_sum {m n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (hd : 0 ≤ d)
    (a b : ℕ) (ha : a < n) (hb : b < n) (g : ℕ → ℝ)
    (hg : ∀ i (hi : i < m), g i = pts ⟨a, ha⟩ ⟨i, hi⟩ - pts ⟨b, hb⟩ ⟨i, hi⟩) :
    edge pts d a b ↔ ∑ i ∈ Finset.range m, g i ^ 2 ≤ d * d := by
  unfold edge
  rw [pt_of_lt pts a ha, pt_of_lt pts b hb, EuclideanSpace.dist_eq, Real.sqrt_le_left hd,
    Finset.sum_range, pow_two d]
  apply Iff.of_eq; congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.dist_eq, sq_abs, hg i i.isLt]

set_option maxHeartbeats 1000000 in
/-- One pair `(a, b)` (offsets 19–46). -/
lemma pair (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) {m n : ℕ}
    (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (hd : 0 ≤ d) (Z : ℤ) (hZ : Z ≤ 0)
    (f : ℕ → ℕ) (a b : ℕ) (ha : a < n) (hb : b < n) (s : State)
    (hpc : s.core.pc = off + 19) (hh : s.halted = false) (hLP : LocalPts s (fun i j => pts i j))
    (h13 : s.core.ptrs 13 = Z) (h42 : s.core.ptrs 42 = b) (h44 : s.core.ptrs 44 = Z - 1 - a)
    (h45 : s.core.ptrs 45 = addr s a) (h43 : s.core.regs 43 = d * d)
    (hL : ∀ i < n, s.integerMemory (Z - 1 - i) = f i) :
    ∃ t, t ≤ 10 * m + 18 ∧ (run Q s detTape t).core.pc = off + 19 ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 42 = ((b + 1 : ℕ) : ℤ) ∧
      (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 46 → x ≠ 47 → x ≠ 48 → x ≠ 49 →
        (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 40 → x ≠ 41 → x ≠ 42 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (run Q s detTape t).core.mem = s.core.mem ∧
      (∀ z, z ≠ Z - 1 - a → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ i < n, (run Q s detTape t).integerMemory (Z - 1 - i) = relax pts d a b f i) ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, c = (false, Z - 1 - a) := by
  have h1 : s.core.ptrs 1 = m := hLP.1
  have h11 : s.core.ptrs 11 = n := hLP.2.1
  -- steps 19–25
  have seg : (run Q s detTape 7).core.pc = off + 26 ∧ (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 43 = ((0 : ℕ) : ℤ) ∧
      (run Q s detTape 7).core.ptrs 46 = addr s b ∧
      (run Q s detTape 7).core.regs 40 = 0 ∧
      (∀ x, x ≠ 43 → x ≠ 46 → x ≠ 47 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 40 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅ := by
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only [addr] at hpc hh h1 h11 h42 ⊢; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_neg (by rw [h11, h42]; push_cast; omega)]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp, by simp [h42], by simp, ?_, ?_, rfl, rfl, rfl, by simp⟩
    · intro x e1 e2 e3; simp [e1, e2, e3]
    · intro x e1; simp [e1]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := seg
  set s1 := run Q s detTape 7 with hs1
  obtain ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩ :=
    j_loop Q off hE m (addr s a) (addr s b) m 0 0 s1 (by omega) g1 g2
      (by rw [g6 1 (by norm_num) (by norm_num) (by norm_num), h1]) g3
      (by rw [g6 45 (by norm_num) (by norm_num) (by norm_num), h45]) g4 g5
  set s2 := run Q s1 detTape (10 * m + 1) with hs2
  set S := ∑ i ∈ Finset.range m,
    (s1.core.mem (addr s a + ((0 + i : ℕ) : ℤ)) - s1.core.mem (addr s b + ((0 + i : ℕ) : ℤ))) ^ 2
  have hS : S ≤ d * d ↔ edge pts d a b := by
    rw [edge_iff_sum pts d hd a b ha hb
      (fun i => s1.core.mem (addr s a + ((0 + i : ℕ) : ℤ)) - s1.core.mem (addr s b + ((0 + i : ℕ) : ℤ)))]
    intro i hi
    simp only [Nat.zero_add, g8]
    rw [addr_pts hLP a ha i hi, addr_pts hLP b hb i hi]
  obtain ⟨t3, ht3, k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ :=
    pair_tail Q off hE n Z f a b ha hb S (d * d) s2 j1 j2
      (by rw [j5 13 (by norm_num) (by norm_num), g6 13 (by norm_num) (by norm_num) (by norm_num), h13])
      (by rw [j5 42 (by norm_num) (by norm_num), g6 42 (by norm_num) (by norm_num) (by norm_num), h42])
      (by rw [j5 44 (by norm_num) (by norm_num), g6 44 (by norm_num) (by norm_num) (by norm_num), h44])
      (by rw [j3]; simp [S, g5])
      (by rw [j6 43 (by norm_num) (by norm_num) (by norm_num), g7 43 (by norm_num), h43])
      (fun i hi => by rw [j8, g9]; exact hL i hi)
  refine ⟨7 + (10 * m + 1) + t3, by omega, ?_⟩
  have RR : run Q s detTape (7 + (10 * m + 1) + t3) = run Q s2 detTape t3 := by
    rw [hs2, hs1, run_add, run_add]
  have CW : cellsWritten Q s (7 + (10 * m + 1) + t3) =
      cellsWritten Q s 7 ∪ cellsWritten Q s1 (10 * m + 1) ∪ cellsWritten Q s2 t3 := by
    rw [hs2, hs1, cellsWritten_add, cellsWritten_add, run_add]
  rw [RR, CW, g11, j10]
  simp only [Finset.empty_union]
  refine ⟨k1, k2, k3, ?_, ?_, by rw [k6, j7, g8], ?_, ?_, by rw [k8, j9, g10]; ring, k9⟩
  · intro x e1 e2 e3 e4 e5 e6
    rw [k4 x e1 e5 e6, j5 x e2 e4, g6 x e2 e3 e4]
  · intro x e1 e2 e3
    rw [k5 x e2, j6 x e1 e2 e3, g7 x e1]
  · intro z hz
    rw [k7]
    split_ifs
    · rw [Function.update_of_ne hz, j8, g9]
    · rw [j8, g9]
  · intro i hi
    rw [k7]
    unfold relax
    by_cases hc : S ≤ d * d ∧ f b < f a
    · rw [if_pos hc, if_pos ⟨hS.1 hc.1, hc.2⟩]
      rcases eq_or_ne i a with rfl | hia
      · simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne hia, j8, g9]; exact hL i hi
    · rw [if_neg hc, if_neg (fun h => hc ⟨hS.2 h.1, h.2⟩), j8, g9]; exact hL i hi

/-- The `b` loop (offset 19): all pairs `(a, b')` with `b' ∈ [b, n)`, then exit to `B_E = 47`. -/
lemma b_loop (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) {m n : ℕ}
    (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (hd : 0 ≤ d) (Z : ℤ) (hZ : Z ≤ 0)
    (a : ℕ) (ha : a < n) :
    ∀ k (b : ℕ) (f : ℕ → ℕ) (s : State), b + k = n →
      s.core.pc = off + 19 → s.halted = false → LocalPts s (fun i j => pts i j) →
      s.core.ptrs 13 = Z → s.core.ptrs 42 = b → s.core.ptrs 44 = Z - 1 - a →
      s.core.ptrs 45 = addr s a → s.core.regs 43 = d * d →
      (∀ i < n, s.integerMemory (Z - 1 - i) = f i) →
      ∃ t, t ≤ k * (10 * m + 18) + 1 ∧ (run Q s detTape t).core.pc = off + 47 ∧
        (run Q s detTape t).halted = false ∧
        (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 46 → x ≠ 47 → x ≠ 48 → x ≠ 49 →
          (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 40 → x ≠ 41 → x ≠ 42 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (∀ z, z ≠ Z - 1 - a → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ i < n, (run Q s detTape t).integerMemory (Z - 1 - i) = bsweep pts d a b f i) ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c = (false, Z - 1 - a) := by
  intro k
  induction k with
  | zero =>
    intro b f s hbk hpc hh hLP h13 h42 h44 h45 h43 hL
    have h11 : s.core.ptrs 11 = n := hLP.2.1
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h42 hL ⊢; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h42]; push_cast; omega)]
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, fun x _ _ _ _ _ _ => rfl, fun x _ _ _ => rfl, rfl, fun z _ => rfl, ?_, rfl, by simp⟩
    intro i hi; rw [bsweep_end pts d a b (by omega)]; exact hL i hi
  | succ k ih =>
    intro b f s hbk hpc hh hLP h13 h42 h44 h45 h43 hL
    obtain ⟨t1, ht1, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ :=
      pair Q off hE pts d hd Z hZ f a b ha (by omega) s hpc hh hLP h13 h42 h44 h45 h43 hL
    set s1 := run Q s detTape t1 with hs1
    have hneg : ∀ z, 0 ≤ z → s1.integerMemory z = s.integerMemory z :=
      fun z hz => p7 z (by omega)
    have hlow : ∀ x < 40, s1.core.ptrs x = s.core.ptrs x := fun x hx =>
      p4 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hLP1 := lp_transfer hLP hlow p6 hneg
    have ha1 : addr s1 a = addr s a := by
      unfold addr
      have e1 : 0 ≤ s.core.ptrs 10 + (a : ℤ) := by have := hLP.2.2.1; omega
      rw [hlow 10 (by norm_num), hlow 12 (by norm_num), hneg _ e1]
      have e2 : 0 ≤ s.core.ptrs 12 + s.integerMemory (s.core.ptrs 10 + (a : ℤ)) := by
        have h3 : 0 ≤ s.integerMemory (s.core.ptrs 10 + (a : ℤ)) := (hLP.2.2.2.2 ⟨a, ha⟩).1
        have := hLP.2.2.2.1; omega
      rw [hneg _ e2]
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih (b + 1) (relax pts d a b f) s1 (by omega) p1 p2 hLP1
        (by rw [hlow 13 (by norm_num), h13]) p3
        (by rw [p4 44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h44])
        (by rw [p4 45 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h45, ha1])
        (by rw [p5 43 (by norm_num) (by norm_num) (by norm_num), h43]) p8
    refine ⟨t1 + t2, ?_, ?_⟩
    · have : (k + 1) * (10 * m + 18) + 1 = (10 * m + 18) + (k * (10 * m + 18) + 1) := by ring
      omega
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, ?_, ?_, by rw [q5, p6], ?_, ?_, by rw [q8, p9]; ring, ?_⟩
    · intro x e1 e2 e3 e4 e5 e6; rw [q3 x e1 e2 e3 e4 e5 e6, p4 x e1 e2 e3 e4 e5 e6]
    · intro x e1 e2 e3; rw [q4 x e1 e2 e3, p5 x e1 e2 e3]
    · intro z hz; rw [q6 z hz, p7 z hz]
    · intro i hi; rw [q7 i hi, bsweep_step pts d a b (by omega)]
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · exact p10 c hc
      · exact q9 c hc

/-- Offsets 11–18 for `a < n`: the address of `a`, `Z − 1 − a`, `b := 0`. -/
lemma a_head (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) (n : ℕ) (Z : ℤ) (a : ℕ)
    (ha : a < n) (s : State) (hpc : s.core.pc = off + 11) (hh : s.halted = false)
    (h11 : s.core.ptrs 11 = n) (h13 : s.core.ptrs 13 = Z) (h41 : s.core.ptrs 41 = a) :
    (run Q s detTape 8).core.pc = off + 19 ∧ (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 42 = ((0 : ℕ) : ℤ) ∧
      (run Q s detTape 8).core.ptrs 44 = Z - 1 - a ∧
      (run Q s detTape 8).core.ptrs 45 = addr s a ∧
      (∀ x, x ≠ 42 → x ≠ 44 → x ≠ 45 → x ≠ 47 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).work = s.work + 8 ∧ cellsWritten Q s 8 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only [addr] at hpc hh h11 h13 h41 ⊢; subst hpc hh
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_neg (by rw [h11, h41]; push_cast; omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, by simp [h13, h41]; ring, by simp [h41], ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x e1 e2 e3 e4; simp [e1, e2, e3, e4]

/-- Offsets 47–48: `a := a + 1`, back to `A`. -/
lemma a_tail (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) (a : ℤ) (s : State)
    (hpc : s.core.pc = off + 47) (hh : s.halted = false) (h41 : s.core.ptrs 41 = a) :
    (run Q s detTape 2).core.pc = off + 11 ∧ (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 41 = a + 1 ∧
      (∀ x, x ≠ 41 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h41 ⊢; subst hpc hh
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp [h41], ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x e1; simp [e1]

/-- The window of label cells. -/
def Win (n : ℕ) (Z : ℤ) (c : Bool × ℤ) : Prop := c.1 = false ∧ Z - n ≤ c.2 ∧ c.2 < Z

set_option maxHeartbeats 1000000 in
/-- The `a` loop (offset 11): one sweep over `a ∈ [a₀, n)`, then exit to `A_E = 49`. -/
lemma a_loop (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) {m n : ℕ}
    (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (hd : 0 ≤ d) (Z : ℤ) (hZ : Z ≤ 0) :
    ∀ k (a : ℕ) (f : ℕ → ℕ) (s : State), a + k = n →
      s.core.pc = off + 11 → s.halted = false → LocalPts s (fun i j => pts i j) →
      s.core.ptrs 13 = Z → s.core.ptrs 41 = a → s.core.regs 43 = d * d →
      (∀ i < n, s.integerMemory (Z - 1 - i) = f i) →
      ∃ t, t ≤ k * (n * (10 * m + 18) + 11) + 1 ∧ (run Q s detTape t).core.pc = off + 49 ∧
        (run Q s detTape t).halted = false ∧
        (∀ x, (x < 40 ∨ 50 ≤ x) → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 40 → x ≠ 41 → x ≠ 42 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.ptrs 40 = s.core.ptrs 40 ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (∀ z, (z < Z - n ∨ Z ≤ z) → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ i < n, (run Q s detTape t).integerMemory (Z - 1 - i) = asweep pts d a f i) ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, Win n Z c := by
  intro k
  induction k with
  | zero =>
    intro a f s hak hpc hh hLP h13 h41 h43 hL
    have h11 : s.core.ptrs 11 = n := hLP.2.1
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h41 hL ⊢; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h41]; push_cast; omega)]
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, fun x _ => rfl, fun x _ _ _ => rfl, rfl, rfl, fun z _ => rfl, ?_, rfl, by simp⟩
    intro i hi; rw [asweep_end pts d a (by omega)]; exact hL i hi
  | succ k ih =>
    intro a f s hak hpc hh hLP h13 h41 h43 hL
    have ha : a < n := by omega
    have h11 : s.core.ptrs 11 = n := hLP.2.1
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := a_head Q off hE n Z a ha s hpc hh h11 h13 h41
    set s1 := run Q s detTape 8 with hs1
    have hlow1 : ∀ x < 40, s1.core.ptrs x = s.core.ptrs x :=
      fun x hx => g6 x (by omega) (by omega) (by omega) (by omega)
    have hLP1 := lp_transfer hLP hlow1 g8 (fun z _ => by rw [g9])
    have ha1 : addr s1 a = addr s a := by unfold addr; rw [g9, hlow1 10 (by norm_num), hlow1 12 (by norm_num)]
    obtain ⟨t2, ht2, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ :=
      b_loop Q off hE pts d hd Z hZ a ha n 0 f s1 (by omega) g1 g2 hLP1
        (by rw [hlow1 13 (by norm_num), h13]) g3 g4 (by rw [g5, ha1]) (by rw [g7, h43])
        (fun i hi => by rw [g9]; exact hL i hi)
    set s2 := run Q s1 detTape t2 with hs2
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := a_tail Q off hE a s2 b1 b2
      (by rw [b3 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        g6 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h41])
    set s3 := run Q s2 detTape 2 with hs3
    have hfr3 : ∀ x, (x < 40 ∨ 50 ≤ x) → s3.core.ptrs x = s.core.ptrs x := by
      intro x hx
      rw [c4 x (by omega), b3 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        g6 x (by omega) (by omega) (by omega) (by omega)]
    have hlow3 : ∀ x < 40, s3.core.ptrs x = s.core.ptrs x := fun x hx => hfr3 x (Or.inl hx)
    have hneg3 : ∀ z, z ≠ Z - 1 - a → s3.integerMemory z = s.integerMemory z := by
      intro z hz; rw [c7, b6 z hz, g9]
    have hLP3 := lp_transfer hLP hlow3 (by rw [c6, b5, g8]) (fun z hz => hneg3 z (by omega))
    obtain ⟨t4, ht4, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ :=
      ih (a + 1) (bsweep pts d a 0 f) s3 (by omega) c1 c2 hLP3 (by rw [hlow3 13 (by norm_num), h13])
        (by rw [c3]; push_cast; ring)
        (by rw [c5, b4 43 (by norm_num) (by norm_num) (by norm_num), g7, h43])
        (fun i hi => by rw [c7]; exact b7 i hi)
    refine ⟨8 + t2 + 2 + t4, ?_, ?_⟩
    · have : (k + 1) * (n * (10 * m + 18) + 11) + 1 =
          (n * (10 * m + 18) + 11) + (k * (n * (10 * m + 18) + 11) + 1) := by ring
      have : t2 ≤ n * (10 * m + 18) + 1 := by simpa using ht2
      omega
    have RR : run Q s detTape (8 + t2 + 2 + t4) = run Q s3 detTape t4 := by
      rw [hs3, hs2, hs1, run_add, run_add, run_add]
    have CW : cellsWritten Q s (8 + t2 + 2 + t4) =
        cellsWritten Q s 8 ∪ cellsWritten Q s1 t2 ∪ cellsWritten Q s2 2 ∪ cellsWritten Q s3 t4 := by
      rw [hs3, hs2, hs1, cellsWritten_add, cellsWritten_add, cellsWritten_add, run_add, run_add, run_add]
    rw [RR, CW, g11, c9]
    simp only [Finset.empty_union, Finset.union_empty]
    refine ⟨d1, d2, ?_, ?_, ?_, by rw [d6, c6, b5, g8], ?_, ?_, ?_, ?_⟩
    · intro x hx; rw [d3 x hx, hfr3 x hx]
    · intro x e1 e2 e3; rw [d4 x e1 e2 e3, c5, b4 x e1 e2 e3, g7]
    · rw [d5, c4 40 (by norm_num), b3 40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), g6 40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    · intro z hz; rw [d7 z hz, hneg3 z (by omega)]
    · intro i hi; rw [d8 i hi, asweep_step pts d a ha]
    · rw [d9, c8, b8, g10]; ring
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · have := b9 c hc; subst this; exact ⟨rfl, by simp; omega, by simp; omega⟩
      · exact d10 c hc

end DetANN.HPIM.CB

-- ===== CB_Main =====
namespace DetANN.HPIM.CB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

/-- Offsets 9–10 for `r < n`: `a := 0`. -/
lemma r_head (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) (n r : ℕ) (hr : r < n) (s : State)
    (hpc : s.core.pc = off + 9) (hh : s.halted = false) (h11 : s.core.ptrs 11 = n)
    (h40 : s.core.ptrs 40 = r) :
    (run Q s detTape 2).core.pc = off + 11 ∧ (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 41 = ((0 : ℕ) : ℤ) ∧
      (∀ x, x ≠ 41 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h11 h40 ⊢; subst hpc hh
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_neg (by rw [h11, h40]; push_cast; omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x e1; simp [e1]

/-- Offsets 49–50: `r := r + 1`, back to `ROUND`. -/
lemma r_tail (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) (r : ℤ) (s : State)
    (hpc : s.core.pc = off + 49) (hh : s.halted = false) (h40 : s.core.ptrs 40 = r) :
    (run Q s detTape 2).core.pc = off + 9 ∧ (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 40 = r + 1 ∧
      (∀ x, x ≠ 40 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h40 ⊢; subst hpc hh
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp [h40], ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x e1; simp [e1]

set_option maxHeartbeats 1000000 in
/-- The round loop (offset 9): `k` more rounds, then exit to `off + 51`. -/
lemma round_loop (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) {m n : ℕ}
    (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (hd : 0 ≤ d) (Z : ℤ) (hZ : Z ≤ 0) :
    ∀ k (r : ℕ) (f : ℕ → ℕ) (s : State), r + k = n →
      s.core.pc = off + 9 → s.halted = false → LocalPts s (fun i j => pts i j) →
      s.core.ptrs 13 = Z → s.core.ptrs 40 = r → s.core.regs 43 = d * d →
      (∀ i < n, s.integerMemory (Z - 1 - i) = f i) →
      ∃ t, t ≤ k * (n * (n * (10 * m + 18) + 11) + 5) + 1 ∧ (run Q s detTape t).core.pc = off + 51 ∧
        (run Q s detTape t).halted = false ∧
        (∀ x, (x < 40 ∨ 50 ≤ x) → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, (x < 40 ∨ 50 ≤ x) → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (∀ z, (z < Z - n ∨ Z ≤ z) → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ i < n, (run Q s detTape t).integerMemory (Z - 1 - i) = (asweep pts d 0)^[k] f i) ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, Win n Z c := by
  intro k
  induction k with
  | zero =>
    intro r f s hrk hpc hh hLP h13 h40 h43 hL
    have h11 : s.core.ptrs 11 = n := hLP.2.1
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h40 hL ⊢; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h40]; push_cast; omega)]
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, fun x _ => rfl, fun x _ => rfl, rfl, fun z _ => rfl, ?_, rfl, by simp⟩
    intro i hi; exact hL i hi
  | succ k ih =>
    intro r f s hrk hpc hh hLP h13 h40 h43 hL
    have h11 : s.core.ptrs 11 = n := hLP.2.1
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := r_head Q off hE n r (by omega) s hpc hh h11 h40
    set s1 := run Q s detTape 2 with hs1
    have hlow1 : ∀ x < 40, s1.core.ptrs x = s.core.ptrs x := fun x hx => g4 x (by omega)
    have hLP1 := lp_transfer hLP hlow1 g6 (fun z _ => by rw [g7])
    obtain ⟨t2, ht2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
      a_loop Q off hE pts d hd Z hZ n 0 f s1 (by omega) g1 g2 hLP1 (by rw [hlow1 13 (by norm_num), h13])
        g3 (by rw [g5, h43]) (fun i hi => by rw [g7]; exact hL i hi)
    set s2 := run Q s1 detTape t2 with hs2
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := r_tail Q off hE r s2 a1 a2
      (by rw [a5, g4 40 (by norm_num), h40])
    set s3 := run Q s2 detTape 2 with hs3
    have hfr3 : ∀ x, (x < 40 ∨ 50 ≤ x) → s3.core.ptrs x = s.core.ptrs x := by
      intro x hx; rw [c4 x (by omega), a3 x hx, g4 x (by omega)]
    have hlow3 : ∀ x < 40, s3.core.ptrs x = s.core.ptrs x := fun x hx => hfr3 x (Or.inl hx)
    have hLP3 := lp_transfer hLP hlow3 (by rw [c6, a6, g6])
      (fun z hz => by rw [c7, a7 z (by omega), g7])
    obtain ⟨t4, ht4, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
      ih (r + 1) (asweep pts d 0 f) s3 (by omega) c1 c2 hLP3 (by rw [hlow3 13 (by norm_num), h13])
        (by rw [c3]; push_cast; ring)
        (by rw [c5, a4 43 (by norm_num) (by norm_num) (by norm_num), g5, h43])
        (fun i hi => by rw [c7]; exact a8 i hi)
    refine ⟨2 + t2 + 2 + t4, ?_, ?_⟩
    · have : (k + 1) * (n * (n * (10 * m + 18) + 11) + 5) + 1 =
          (n * (n * (10 * m + 18) + 11) + 5) + (k * (n * (n * (10 * m + 18) + 11) + 5) + 1) := by ring
      have : t2 ≤ n * (n * (10 * m + 18) + 11) + 1 := by simpa using ht2
      omega
    have RR : run Q s detTape (2 + t2 + 2 + t4) = run Q s3 detTape t4 := by
      rw [hs3, hs2, hs1, run_add, run_add, run_add]
    have CW : cellsWritten Q s (2 + t2 + 2 + t4) =
        cellsWritten Q s 2 ∪ cellsWritten Q s1 t2 ∪ cellsWritten Q s2 2 ∪ cellsWritten Q s3 t4 := by
      rw [hs3, hs2, hs1, cellsWritten_add, cellsWritten_add, cellsWritten_add, run_add, run_add, run_add]
    rw [RR, CW, g9, c9]
    simp only [Finset.empty_union, Finset.union_empty]
    refine ⟨d1, d2, ?_, ?_, by rw [d5, c6, a6, g6], ?_, ?_, by rw [d8, c8, a9, g8]; ring, ?_⟩
    · intro x hx; rw [d3 x hx, hfr3 x hx]
    · intro x hx; rw [d4 x hx, c5, a4 x (by omega) (by omega) (by omega), g5]
    · intro z hz; rw [d6 z hz, c7, a7 z hz, g7]
    · intro i hi; rw [d7 i hi, Function.iterate_succ_apply]
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · exact a10 c hc
      · exact d9 c hc

set_option maxHeartbeats 1000000 in
/-- The initialization loop (offsets 2–7): `lab i := i` for `i ∈ [a, n)`, then exit to 8. -/
lemma init_loop (Q : Program) (off : ℕ) (hE : Embeds Q (cb off) off) (n : ℕ) (Z : ℤ) :
    ∀ k (a : ℕ) (s : State), a + k = n →
      s.core.pc = off + 2 → s.halted = false → s.core.ptrs 11 = n → s.core.ptrs 13 = Z →
      s.core.ptrs 41 = a → (∀ i < a, s.integerMemory (Z - 1 - i) = i) →
      (run Q s detTape (6 * k + 1)).core.pc = off + 8 ∧
      (run Q s detTape (6 * k + 1)).halted = false ∧
      (∀ x, x ≠ 41 → x ≠ 44 → (run Q s detTape (6 * k + 1)).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape (6 * k + 1)).core.regs = s.core.regs ∧
      (run Q s detTape (6 * k + 1)).core.mem = s.core.mem ∧
      (∀ z, (z < Z - n ∨ Z ≤ z) → (run Q s detTape (6 * k + 1)).integerMemory z = s.integerMemory z) ∧
      (∀ i < n, (run Q s detTape (6 * k + 1)).integerMemory (Z - 1 - i) = i) ∧
      (run Q s detTape (6 * k + 1)).work = s.work + (6 * k + 1) ∧
      ∀ c ∈ cellsWritten Q s (6 * k + 1), Win n Z c := by
  intro k
  induction k with
  | zero =>
    intro a s hak hpc hh h11 h13 h41 hL
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h13 h41 hL ⊢; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h41]; push_cast; omega)]
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, fun x _ _ => rfl, rfl, rfl, fun z _ => rfl, fun i hi => hL i (by omega), rfl, by simp⟩
  | succ k ih =>
    intro a s hak hpc hh h11 h13 h41 hL
    have it : (run Q s detTape 6).core.pc = off + 2 ∧ (run Q s detTape 6).halted = false ∧
        (run Q s detTape 6).core.ptrs 41 = ((a + 1 : ℕ) : ℤ) ∧
        (∀ x, x ≠ 41 → x ≠ 44 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape 6).core.regs = s.core.regs ∧ (run Q s detTape 6).core.mem = s.core.mem ∧
        (run Q s detTape 6).integerMemory = Function.update s.integerMemory (Z - 1 - a) a ∧
        (run Q s detTape 6).work = s.work + 6 ∧
        cellsWritten Q s 6 = {(false, Z - 1 - a)} := by
      obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
      simp only at hpc hh h11 h13 h41 ⊢; subst hpc hh
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell]
      rw [if_neg (by rw [h11, h41]; push_cast; omega)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_zero, cw_zero]
      have e : Z - a - 1 = Z - 1 - a := by ring
      refine ⟨rfl, rfl, by simp [h41], ?_, rfl, rfl, by simp [h13, h41, e], rfl, by simp [h13, h41, e]⟩
      intro x e1 e2; simp [e1, e2]
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := it
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
      ih (a + 1) (run Q s detTape 6) (by omega) i1 i2 (by rw [i4 11 (by norm_num) (by norm_num), h11])
        (by rw [i4 13 (by norm_num) (by norm_num), h13]) i3
        (by
          intro i hi
          rw [i7]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [Function.update_of_ne (by omega)]; exact hL i hi
          · simp)
    have RR : run Q s detTape (6 * (k + 1) + 1) = run Q (run Q s detTape 6) detTape (6 * k + 1) := by
      rw [← run_add]; congr 1; ring
    have CW : cellsWritten Q s (6 * (k + 1) + 1) =
        cellsWritten Q s 6 ∪ cellsWritten Q (run Q s detTape 6) (6 * k + 1) := by
      rw [← cellsWritten_add]; congr 1; ring
    rw [RR, CW]
    refine ⟨c1, c2, ?_, by rw [c4, i5], by rw [c5, i6], ?_, c7, by rw [c8, i8]; ring, ?_⟩
    · intro x e1 e2; rw [c3 x e1 e2, i4 x e1 e2]
    · intro z hz; rw [c6 z hz, i7, Function.update_of_ne (by omega)]
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · rw [i9, Finset.mem_singleton] at hc; subst hc; exact ⟨rfl, by simp; omega, by simp; omega⟩
      · exact c9 c hc

lemma work_le (n m : ℕ) :
    2 + (6 * n + 1) + 1 + (n * (n * (n * (10 * m + 18) + 11) + 5) + 1) ≤ 40 * (n + 1) ^ 3 * (m + 1) := by
  nlinarith [Nat.zero_le (n * n * n * m), Nat.zero_le (n * n * m), Nat.zero_le (n * m),
    Nat.zero_le (n * n * n), Nat.zero_le (n * n)]

set_option maxHeartbeats 1000000 in
/-- **The components block, with explicit frames** (used inside the median block). -/
theorem cb_spec (off : ℕ) (Q : Program) (hE : Embeds Q (cb off) off) {m n : ℕ}
    (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) (hLP : LocalPts s (fun i j => pts i j))
    (h10 : s.core.regs 10 = d) (hd : 0 ≤ d) (hZ : s.core.ptrs 13 ≤ 0) :
    ∃ t, t ≤ 40 * (n + 1) ^ 3 * (m + 1) ∧ (run Q s detTape t).core.pc = off + 51 ∧
      (run Q s detTape t).halted = false ∧
      (∀ i < n, (run Q s detTape t).integerMemory (s.core.ptrs 13 - 1 - i) =
        rounds pts d n (fun i => i) i) ∧
      (∀ x, (x < 40 ∨ 50 ≤ x) → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, (x < 40 ∨ 50 ≤ x) → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (run Q s detTape t).core.mem = s.core.mem ∧
      (∀ z, (z < s.core.ptrs 13 - n ∨ s.core.ptrs 13 ≤ z) →
        (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, Win n (s.core.ptrs 13) c := by
  set Z := s.core.ptrs 13 with hZdef
  have h11 : s.core.ptrs 11 = n := hLP.2.1
  -- steps 0–1
  have seg : (run Q s detTape 2).core.pc = off + 2 ∧ (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 41 = ((0 : ℕ) : ℤ) ∧
      (run Q s detTape 2).core.regs 43 = d * d ∧
      (∀ x, x ≠ 41 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 43 → (run Q s detTape 2).core.regs x = s.core.regs x) ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅ := by
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h10 ⊢; subst hh
    rw [show pc = off + 0 from hpc]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp, by simp [h10], ?_, ?_, rfl, rfl, rfl, by simp⟩
    · intro x e1; simp [e1]
    · intro x e1; simp [e1]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := seg
  set s1 := run Q s detTape 2 with hs1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ :=
    init_loop Q off hE n Z n 0 s1 (by omega) g1 g2 (by rw [g5 11 (by norm_num), h11])
      (by rw [g5 13 (by norm_num)]) g3 (fun i hi => by omega)
  set s2 := run Q s1 detTape (6 * n + 1) with hs2
  -- step 8
  have seg8 : (run Q s2 detTape 1).core.pc = off + 9 ∧ (run Q s2 detTape 1).halted = false ∧
      (run Q s2 detTape 1).core.ptrs 40 = ((0 : ℕ) : ℤ) ∧
      (∀ x, x ≠ 40 → (run Q s2 detTape 1).core.ptrs x = s2.core.ptrs x) ∧
      (run Q s2 detTape 1).core.regs = s2.core.regs ∧ (run Q s2 detTape 1).core.mem = s2.core.mem ∧
      (run Q s2 detTape 1).integerMemory = s2.integerMemory ∧
      (run Q s2 detTape 1).work = s2.work + 1 ∧ cellsWritten Q s2 1 = ∅ := by
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s2
    simp only at i1 i2 ⊢; subst i1 i2
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp, ?_, rfl, rfl, rfl, rfl, by simp⟩
    intro x e1; simp [e1]
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := seg8
  set s3 := run Q s2 detTape 1 with hs3
  have hfr3 : ∀ x, (x < 40 ∨ 50 ≤ x) → s3.core.ptrs x = s.core.ptrs x := by
    intro x hx; rw [e4 x (by omega), i3 x (by omega) (by omega), g5 x (by omega)]
  have hlow3 : ∀ x < 40, s3.core.ptrs x = s.core.ptrs x := fun x hx => hfr3 x (Or.inl hx)
  have hLP3 := lp_transfer hLP hlow3 (by rw [e6, i5, g7])
    (fun z hz => by rw [e7, i6 z (by omega), g8])
  obtain ⟨t4, ht4, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ :=
    round_loop Q off hE pts d hd Z hZ n 0 (fun i => i) s3 (by omega) e1 e2 hLP3
      (by rw [hlow3 13 (by norm_num)]) e3 (by rw [e5, i4, g4])
      (fun i hi => by rw [e7]; exact i7 i hi)
  refine ⟨2 + (6 * n + 1) + 1 + t4, ?_, ?_⟩
  · have hw := work_le n m
    have : t4 ≤ n * (n * (n * (10 * m + 18) + 11) + 5) + 1 := ht4
    omega
  have RR : run Q s detTape (2 + (6 * n + 1) + 1 + t4) = run Q s3 detTape t4 := by
    rw [hs3, hs2, hs1, run_add, run_add, run_add]
  have CW : cellsWritten Q s (2 + (6 * n + 1) + 1 + t4) =
      cellsWritten Q s 2 ∪ cellsWritten Q s1 (6 * n + 1) ∪ cellsWritten Q s2 1 ∪
        cellsWritten Q s3 t4 := by
    rw [hs3, hs2, hs1, cellsWritten_add, cellsWritten_add, cellsWritten_add]
    simp only [← run_add]
  rw [RR, CW, g10, e9]
  simp only [Finset.empty_union, Finset.union_empty]
  refine ⟨r1, r2, ?_, ?_, ?_, by rw [r5, e6, i5, g7], ?_, by rw [r8, e8, i8, g9]; ring, ?_⟩
  · intro i hi; rw [r7 i hi]; rfl
  · intro x hx; rw [r3 x hx, hfr3 x hx]
  · intro x hx; rw [r4 x hx, e5, i4, g6 x (by omega)]
  · intro z hz; rw [r6 z hz, e7, i6 z hz, g8]
  · intro c hc
    rcases Finset.mem_union.1 hc with hc | hc
    · exact i9 c hc
    · exact r9 c hc

end DetANN.HPIM.CB

-- ===== MB_Prog =====
namespace DetANN.HPIM.MB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.CB

/-- The part before the components block (offsets 0–27). -/
def mbA (off : ℕ) : Program :=
  [ .core (.const 50 0),                -- 0   best := 0
    .core (.const 55 0),                -- 1   zero
    .core (.pset 52 0),                 -- 2   found := 0
    .core (.pset 50 0),                 -- 3   i := 0
    .core (.pjle 11 50 (off + 116)),    -- 4   I: n ≤ i → END
    .pointerAdd 56 10 50,               -- 5
    .integerLoad 56 56,                 -- 6
    .pointerAdd 56 12 56,               -- 7
    .integerLoad 61 56,                 -- 8   p61 = address of i
    .core (.pset 51 0),                 -- 9   j := 0
    .core (.pjle 11 51 (off + 114)),    -- 10  J: n ≤ j → I_NEXT
    .pointerAdd 56 10 51,               -- 11
    .integerLoad 56 56,                 -- 12
    .pointerAdd 56 12 56,               -- 13
    .integerLoad 62 56,                 -- 14  p62 = address of j
    .core (.const 51 0),                -- 15  sum := 0
    .core (.pset 63 0),                 -- 16  c := 0
    .core (.pjle 1 63 (off + 27)),      -- 17  C: m ≤ c → C_E
    .pointerAdd 56 61 63,               -- 18
    .core (.load 52 56),                -- 19
    .pointerAdd 56 62 63,               -- 20
    .core (.load 53 56),                -- 21
    .core (.sub 52 52 53),              -- 22
    .core (.mul 52 52 52),              -- 23
    .core (.add 51 51 52),              -- 24  sum += (P_i − P_j)²
    .core (.pinc 63),                   -- 25
    .core (.pjle 63 63 (off + 17)),     -- 26
    .sqrt 54 51 ]                       -- 27  C_E: d := √sum

/-- The part after the components block (offsets 79–115; local index `k` is offset `79 + k`). -/
def mbB (off : ℕ) : Program :=
  [ .core (.pset 60 0),                 -- 80  qual := 0
    .core (.pset 53 0),                 -- 81  i₂ := 0
    .core (.pjle 11 53 (off + 104)),    -- 82  Q: n ≤ i₂ → Q_E
    .pointerSub 56 13 53,               -- 83 
    .core (.pdec 56),                   -- 84 
    .integerLoad 57 56,                 -- 85  p57 = lab i₂
    .core (.pset 55 0),                 -- 86  cnt := 0
    .core (.pset 54 0),                 -- 87  k := 0
    .core (.pjle 11 54 (off + 99)),     -- 88  K: n ≤ k → K_E
    .pointerSub 56 13 54,               -- 89 
    .core (.pdec 56),                   -- 90 
    .integerLoad 58 56,                 -- 91  p58 = lab k
    .core (.pjle 57 58 (off + 94)),     -- 92  lab i₂ ≤ lab k → 94
    .core (.pjle 54 54 (off + 97)),     -- 93  → K_NEXT
    .core (.pjle 58 57 (off + 96)),     -- 94  lab k ≤ lab i₂ → INC
    .core (.pjle 54 54 (off + 97)),     -- 95  → K_NEXT
    .core (.pinc 55),                   -- 96  INC
    .core (.pinc 54),                   -- 97  K_NEXT
    .core (.pjle 54 54 (off + 88)),     -- 98 
    .pointerAdd 59 55 55,               -- 99  K_E: 2 cnt
    .core (.pjle 59 11 (off + 102)),    -- 100 2 cnt ≤ n → skip
    .core (.pset 60 1),                 -- 101 qual := 1
    .core (.pinc 53),                   -- 102
    .core (.pjle 53 53 (off + 82)),     -- 103
    .core (.pset 56 0),                 -- 104 Q_E: p56 := 0
    .core (.pjle 60 56 (off + 112)),    -- 105 not qual → J_NEXT
    .core (.pjle 52 56 (off + 110)),    -- 106 not found yet → UPD
    .core (.sub 52 54 50),              -- 107 d − best
    .core (.jle 52 (off + 110)),        -- 108 d ≤ best → UPD
    .core (.pjle 56 56 (off + 112)),    -- 109 → J_NEXT
    .core (.add 50 54 55),              -- 110 UPD: best := d
    .core (.pset 52 1),                 -- 111 found := 1
    .core (.pinc 51),                   -- 112 J_NEXT
    .core (.pjle 51 51 (off + 10)),     -- 113
    .core (.pinc 50),                   -- 114 I_NEXT
    .core (.pjle 50 50 (off + 4)),      -- 115
    .core (.add 10 50 55) ]             -- 116 END: r10 := best

/-- The median-threshold block (117 instructions): `mbA` (offsets 0–27), `sqrt 10 51` (28), the
components block (29–79), `mbB` (80–116). -/
def mb (off : ℕ) : Program := mbA off ++ [.sqrt 10 51] ++ cb (off + 29) ++ mbB off

lemma mbA_len (off : ℕ) : (mbA off).length = 28 := rfl

lemma mb_len (off : ℕ) : (mb off).length = 117 := rfl

lemma det_mbA (off : ℕ) : DetProgram (mbA off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold mbA at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)

lemma det_mbB (off : ℕ) : DetProgram (mbB off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold mbB at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)

lemma det_sqrt : DetProgram [Instr.sqrt 10 51] := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  subst hop
  exact ⟨trivial, (fun r h => by cases h), (fun r a e h => by cases h)⟩

lemma mb_block : IsBlock mb 117 := fun off =>
  ⟨mb_len off, DetANN.HPIM.PP.det_append (DetANN.HPIM.PP.det_append
    (DetANN.HPIM.PP.det_append (det_mbA off) det_sqrt) (cb_det _)) (det_mbB off)⟩

/-- The components block sits at offset `off + 29`. -/
lemma emb_cb {Q : Program} {off : ℕ} (h : Embeds Q (mb off) off) : Embeds Q (cb (off + 29)) (off + 29) := by
  intro i x hx
  have hi : i < 51 := by
    obtain ⟨h1, -⟩ := List.getElem?_eq_some_iff.1 hx
    simpa [cb_len] using h1
  have : (mb off)[29 + i]? = some x := by
    unfold mb
    rw [List.getElem?_append_left (by simp [mbA_len, cb_len]; omega),
      List.getElem?_append_right (by simp [mbA_len]), ]
    simpa [mbA_len] using hx
  rw [show off + 29 + i = off + (29 + i) by ring]
  exact h _ x this

end DetANN.HPIM.MB

-- ===== MB_Math =====
namespace DetANN.HPIM.MB

open DetANN.HPIM DetANN.HPIM.CB Classical

variable {m n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin m))

lemma compMin_reach (d : ℝ) (i : Fin n) :
    ∃ h : compMin pts d i < n, thrReach pts d i ⟨compMin pts d i, h⟩ := by
  unfold compMin
  set F := Finset.univ.filter (thrReach pts d i)
  have hm := Finset.min'_mem F ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩⟩
  exact ⟨(F.min' _).isLt, (Finset.mem_filter.1 hm).2⟩

lemma compMin_eq_iff (d : ℝ) (i k : Fin n) :
    compMin pts d k = compMin pts d i ↔ thrReach pts d i k := by
  constructor
  · intro h
    obtain ⟨hi, ri⟩ := compMin_reach pts d i
    obtain ⟨hk, rk⟩ := compMin_reach pts d k
    have e : (⟨compMin pts d k, hk⟩ : Fin n) = ⟨compMin pts d i, hi⟩ := Fin.ext h
    rw [e] at rk
    exact ri.trans rk.symm
  · intro h
    unfold compMin
    have hF : Finset.univ.filter (thrReach pts d k) = Finset.univ.filter (thrReach pts d i) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hx => h.trans hx, fun hx => h.symm.trans hx⟩
    simp only [hF]

/-- The size of the component of `i`, counted through labels. -/
noncomputable def cnt (lab : ℕ → ℕ) (i : ℕ) : ℕ := ((Finset.range n).filter (fun k => lab k = lab i)).card

lemma cnt_eq (d : ℝ) (lab : ℕ → ℕ) (hlab : ∀ i (h : i < n), lab i = compMin pts d ⟨i, h⟩)
    (i : ℕ) (hi : i < n) :
    cnt (n := n) lab i = (Finset.univ.filter (thrReach pts d ⟨i, hi⟩)).card := by
  unfold cnt
  rw [← Finset.card_map ⟨(fun x : Fin n => (x : ℕ)), Fin.val_injective⟩]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hk, he⟩
    refine ⟨⟨k, hk⟩, ?_, rfl⟩
    rw [← compMin_eq_iff, ← hlab k hk, ← hlab i hi, he]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.isLt, ?_⟩
    rw [hlab x x.isLt, hlab i hi]
    exact (compMin_eq_iff pts d ⟨i, hi⟩ x).2 hx

/-- The qualification test of a threshold, as in `medThreshold`. -/
def Qual (d : ℝ) : Prop := ∃ i : Fin n, n / 2 + 1 ≤ (Finset.univ.filter (thrReach pts d i)).card

lemma half_iff (n c : ℕ) : n / 2 + 1 ≤ c ↔ n < 2 * c := by omega

lemma qual_iff (d : ℝ) (lab : ℕ → ℕ) (hlab : ∀ i (h : i < n), lab i = compMin pts d ⟨i, h⟩) :
    (∃ i < n, ¬ 2 * cnt (n := n) lab i ≤ n) ↔ Qual pts d := by
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [half_iff, ← cnt_eq pts d lab hlab i hi]; omega
  · rintro ⟨⟨i, hi⟩, h⟩
    refine ⟨i, hi, ?_⟩
    rw [half_iff, ← cnt_eq pts d lab hlab i hi] at h; omega

/-- The distance of a pair of indices. -/
noncomputable def D (i j : ℕ) : ℝ := dist (pt pts i) (pt pts j)

/-- One update of `(found, best)`. -/
noncomputable def upd (q : Prop) (x : ℝ) (st : Bool × ℝ) : Bool × ℝ :=
  if q ∧ (st.1 = false ∨ x ≤ st.2) then (true, x) else st

/-- The sweep of one `i` over `j ∈ [j₀, n)`. -/
noncomputable def jsweep (i j₀ : ℕ) (st : Bool × ℝ) : Bool × ℝ :=
  (List.range' j₀ (n - j₀)).foldl (fun st j => upd (Qual pts (D pts i j)) (D pts i j) st) st

/-- The sweep over `i ∈ [i₀, n)`. -/
noncomputable def isweep (i₀ : ℕ) (st : Bool × ℝ) : Bool × ℝ :=
  (List.range' i₀ (n - i₀)).foldl (fun st i => jsweep pts i 0 st) st

lemma jsweep_step (i j : ℕ) (hj : j < n) (st : Bool × ℝ) :
    jsweep pts i j st = jsweep pts i (j + 1) (upd (Qual pts (D pts i j)) (D pts i j) st) := by
  unfold jsweep
  rw [show n - j = (n - (j + 1)) + 1 by omega, List.range'_succ]
  simp

lemma jsweep_end (i j : ℕ) (hj : n ≤ j) (st : Bool × ℝ) : jsweep pts i j st = st := by
  unfold jsweep; rw [show n - j = 0 by omega]; simp

lemma isweep_step (i : ℕ) (hi : i < n) (st : Bool × ℝ) :
    isweep pts i st = isweep pts (i + 1) (jsweep pts i 0 st) := by
  unfold isweep
  rw [show n - i = (n - (i + 1)) + 1 by omega, List.range'_succ]
  simp

lemma isweep_end (i : ℕ) (hi : n ≤ i) (st : Bool × ℝ) : isweep pts i st = st := by
  unfold isweep; rw [show n - i = 0 by omega]; simp

/-- The list of all candidate distances, in the order of the sweep. -/
noncomputable def candL : List ℝ := (List.range n).flatMap (fun i => (List.range n).map (D pts i))

lemma isweep_eq (st : Bool × ℝ) :
    isweep pts 0 st = (candL pts).foldl (fun st x => upd (Qual pts x) x st) st := by
  unfold isweep candL jsweep
  rw [List.foldl_flatMap]
  simp only [List.foldl_map, Nat.sub_zero, List.range_eq_range']

/-- The invariant of the minimum fold. -/
def MInv (Q : ℝ → Prop) (P : List ℝ) (st : Bool × ℝ) : Prop :=
  (st.1 = false → st.2 = 0 ∧ ∀ x ∈ P, ¬ Q x) ∧
    (st.1 = true → st.2 ∈ P ∧ Q st.2 ∧ ∀ x ∈ P, Q x → st.2 ≤ x)

lemma minv_upd (Q : ℝ → Prop) (P : List ℝ) (st : Bool × ℝ) (h : MInv Q P st) (x : ℝ) :
    MInv Q (P ++ [x]) (upd (Q x) x st) := by
  obtain ⟨h0, h1⟩ := h
  unfold upd
  split_ifs with hc
  · refine ⟨fun h => by simp at h, fun _ => ⟨by simp, hc.1, ?_⟩⟩
    intro y hy hq
    rcases List.mem_append.1 hy with hy | hy
    · rcases hc.2 with hf | hle
      · exact absurd hq ((h0 hf).2 y hy)
      · rcases Bool.eq_false_or_eq_true st.1 with ht | hf
        · exact hle.trans ((h1 ht).2.2 y hy hq)
        · exact absurd hq ((h0 hf).2 y hy)
    · simp at hy; rw [hy]
  · push_neg at hc
    refine ⟨fun hf => ⟨(h0 hf).1, ?_⟩, fun ht => ⟨by simp [(h1 ht).1], (h1 ht).2.1, ?_⟩⟩
    · intro y hy hq
      rcases List.mem_append.1 hy with hy | hy
      · exact (h0 hf).2 y hy hq
      · simp at hy; subst hy; exact absurd hf (hc hq).1
    · intro y hy hq
      rcases List.mem_append.1 hy with hy | hy
      · exact (h1 ht).2.2 y hy hq
      · simp at hy; subst hy
        exact (hc hq).2.le

lemma minv_fold (Q : ℝ → Prop) (L : List ℝ) :
    ∀ (P : List ℝ) (st : Bool × ℝ), MInv Q P st →
      MInv Q (P ++ L) (L.foldl (fun st x => upd (Q x) x st) st) := by
  induction L with
  | nil => intro P st h; simpa using h
  | cons x L ih =>
    intro P st h
    rw [List.foldl_cons, show P ++ x :: L = (P ++ [x]) ++ L by simp]
    exact ih _ _ (minv_upd Q P st h x)

lemma mem_candL (x : ℝ) : x ∈ candL pts ↔ ∃ i j : Fin n, dist (pts i) (pts j) = x := by
  unfold candL D
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩, by rw [pt_of_lt pts i hi, pt_of_lt pts j hj]⟩
  · rintro ⟨i, j, rfl⟩
    exact ⟨i, i.isLt, j, j.isLt, by rw [pt_of_lt pts i i.isLt, pt_of_lt pts j j.isLt]⟩

/-- **The sweep computes `medThreshold`.** -/
theorem isweep_eq_med : (isweep pts 0 (false, 0)).2 = medThreshold pts := by
  have hI := minv_fold (Qual pts) (candL pts) [] (false, 0) ⟨fun _ => ⟨rfl, by simp⟩, fun h => by simp at h⟩
  rw [List.nil_append, ← isweep_eq] at hI
  obtain ⟨h0, h1⟩ := hI
  set st := isweep pts 0 (false, 0)
  unfold medThreshold
  simp only
  split_ifs with hne
  · obtain ⟨hm, hq, hle⟩ := h1 (by
      rcases Bool.eq_false_or_eq_true st.1 with ht | hf
      · exact ht
      · exfalso
        obtain ⟨x, hx⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_univ,
          true_and] at hx
        obtain ⟨⟨⟨i, j⟩, rfl⟩, hq⟩ := hx
        exact (h0 hf).2 _ ((mem_candL pts _).2 ⟨i, j, rfl⟩) hq)
    apply le_antisymm
    · apply hle
      · have := Finset.min'_mem _ hne
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_univ,
          true_and] at this
        obtain ⟨⟨⟨i, j⟩, e⟩, -⟩ := this
        exact (mem_candL pts _).2 ⟨i, j, e⟩
      · have := Finset.min'_mem _ hne
        simp only [Finset.mem_filter] at this
        exact this.2
    · apply Finset.min'_le
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
      obtain ⟨i, j, e⟩ := (mem_candL pts _).1 hm
      exact ⟨⟨⟨i, j⟩, e⟩, hq⟩
  · rcases Bool.eq_false_or_eq_true st.1 with ht | hf
    · obtain ⟨hm, hq, -⟩ := h1 ht
      exfalso; apply hne
      obtain ⟨i, j, e⟩ := (mem_candL pts _).1 hm
      exact ⟨st.2, by
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
        exact ⟨⟨⟨i, j⟩, e⟩, hq⟩⟩
    · exact (h0 hf).1

end DetANN.HPIM.MB

-- ===== MB_Loops =====
namespace DetANN.HPIM.MB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP DetANN.HPIM.CB

/-- The squared-distance loop (`C`, offsets 17–26). -/
lemma c_loop (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (m : ℕ) (A B : ℤ) :
    ∀ k (j : ℕ) (acc : ℝ) (s : State), j + k = m →
      s.core.pc = off + 17 → s.halted = false → s.core.ptrs 1 = m → s.core.ptrs 63 = j →
      s.core.ptrs 61 = A → s.core.ptrs 62 = B → s.core.regs 51 = acc →
      (run Q s detTape (10 * k + 1)).core.pc = off + 27 ∧
      (run Q s detTape (10 * k + 1)).halted = false ∧
      (run Q s detTape (10 * k + 1)).core.regs 51 =
        acc + ∑ i ∈ Finset.range k,
          (s.core.mem (A + ((j + i : ℕ) : ℤ)) - s.core.mem (B + ((j + i : ℕ) : ℤ))) ^ 2 ∧
      (∀ x, x ≠ 56 → x ≠ 63 → (run Q s detTape (10 * k + 1)).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 51 → x ≠ 52 → x ≠ 53 → (run Q s detTape (10 * k + 1)).core.regs x = s.core.regs x) ∧
      (run Q s detTape (10 * k + 1)).core.mem = s.core.mem ∧
      (run Q s detTape (10 * k + 1)).integerMemory = s.integerMemory ∧
      (run Q s detTape (10 * k + 1)).work = s.work + (10 * k + 1) ∧
      cellsWritten Q s (10 * k + 1) = ∅ := by
  intro k
  induction k with
  | zero =>
    intro j acc s hjk hpc hh h1 h63 h61 h62 h51
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h1 h63 h61 h62 h51; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h1, h63]; omega)]
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp [h51], fun x _ _ => rfl, fun x _ _ _ => rfl, rfl, rfl, rfl, by simp⟩
  | succ k ih =>
    intro j acc s hjk hpc hh h1 h63 h61 h62 h51
    have it : (run Q s detTape 10).core.pc = off + 17 ∧ (run Q s detTape 10).halted = false ∧
        (run Q s detTape 10).core.ptrs 63 = ((j + 1 : ℕ) : ℤ) ∧
        (run Q s detTape 10).core.regs 51 =
          acc + (s.core.mem (A + (j : ℤ)) - s.core.mem (B + (j : ℤ))) ^ 2 ∧
        (∀ x, x ≠ 56 → x ≠ 63 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 51 → x ≠ 52 → x ≠ 53 → (run Q s detTape 10).core.regs x = s.core.regs x) ∧
        (run Q s detTape 10).core.mem = s.core.mem ∧
        (run Q s detTape 10).integerMemory = s.integerMemory ∧
        (run Q s detTape 10).work = s.work + 10 ∧ cellsWritten Q s 10 = ∅ := by
      obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
      simp only at hpc hh h1 h63 h61 h62 h51 ⊢; subst hpc hh
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell]
      rw [if_neg (by rw [h1, h63]; push_cast; omega)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_zero, cw_zero]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, by simp⟩
      · simp [h63]
      · simp [h51, h61, h62, h63]; ring
      · intro x h1 h2; simp [h1, h2]
      · intro x h1 h2 h3; simp [h1, h2, h3]
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := it
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
      ih (j + 1) _ (run Q s detTape 10) (by omega) i1 i2 (by rw [i5 1 (by norm_num) (by norm_num), h1])
        i3 (by rw [i5 61 (by norm_num) (by norm_num), h61]) (by rw [i5 62 (by norm_num) (by norm_num), h62]) i4
    have RR : run Q s detTape (10 * (k + 1) + 1) = run Q (run Q s detTape 10) detTape (10 * k + 1) := by
      rw [← run_add]; congr 1; ring
    have CW : cellsWritten Q s (10 * (k + 1) + 1) =
        cellsWritten Q s 10 ∪ cellsWritten Q (run Q s detTape 10) (10 * k + 1) := by
      rw [← cellsWritten_add]; congr 1; ring
    rw [RR]
    refine ⟨c1, c2, ?_, ?_, ?_, by rw [c6, i7], by rw [c7, i8], by rw [c8, i9]; ring, ?_⟩
    · rw [c3, i7, Finset.sum_range_succ']
      simp only [add_zero]
      have e : ∀ i, j + 1 + i = j + (i + 1) := fun i => by omega
      simp only [e]; ring
    · intro x h1 h2; rw [c4 x h1 h2, i5 x h1 h2]
    · intro x h1 h2 h3; rw [c5 x h1 h2 h3, i6 x h1 h2 h3]
    · rw [CW, i10, c9]; simp

/-- The number of `k ∈ [k₀, n)` whose label is `L`. -/
noncomputable def cntFrom (n : ℕ) (lab : ℕ → ℕ) (L : ℤ) (k₀ : ℕ) : ℕ :=
  ((Finset.Ico k₀ n).filter (fun k => (lab k : ℤ) = L)).card

lemma cntFrom_step (n : ℕ) (lab : ℕ → ℕ) (L : ℤ) (k : ℕ) (hk : k < n) :
    cntFrom n lab L k = (if (lab k : ℤ) = L then 1 else 0) + cntFrom n lab L (k + 1) := by
  unfold cntFrom
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_eq_sum_Ico_succ_bot hk]

lemma cntFrom_end (n : ℕ) (lab : ℕ → ℕ) (L : ℤ) (k : ℕ) (hk : n ≤ k) : cntFrom n lab L k = 0 := by
  unfold cntFrom; rw [Finset.Ico_eq_empty (by omega)]; simp

/-- The counting loop (`K`, offsets 88–98). -/
lemma k_loop (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (n : ℕ) (Z : ℤ) (lab : ℕ → ℕ)
    (L : ℤ) :
    ∀ kk (k : ℕ) (c : ℕ) (s : State), k + kk = n →
      s.core.pc = off + 88 → s.halted = false → s.core.ptrs 11 = n → s.core.ptrs 13 = Z →
      s.core.ptrs 54 = k → s.core.ptrs 55 = c → s.core.ptrs 57 = L →
      (∀ i < n, s.integerMemory (Z - 1 - i) = lab i) →
      ∃ t, t ≤ 9 * kk + 1 ∧ (run Q s detTape t).core.pc = off + 99 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 55 = ((c + cntFrom n lab L k : ℕ) : ℤ) ∧
        (∀ x, x ≠ 54 → x ≠ 55 → x ≠ 56 → x ≠ 58 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ := by
  intro kk
  induction kk with
  | zero =>
    intro k c s hkk hpc hh h11 h13 h54 h55 h57 hL
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h54 h55 ⊢; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h54]; push_cast; omega)]
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp only; rw [h55, cntFrom_end n lab L k (by omega)]; simp, fun x _ _ _ _ => rfl, rfl,
      rfl, rfl, rfl, by simp⟩
  | succ kk ih =>
    intro k c s hkk hpc hh h11 h13 h54 h55 h57 hL
    have hk : k < n := by omega
    have lk : s.integerMemory (Z - k - 1) = lab k := by
      rw [show Z - k - 1 = Z - 1 - k by ring]; exact hL k hk
    -- one iteration, back at `off + 88` with `k + 1`
    have it : ∃ u, u ≤ 9 ∧ (run Q s detTape u).core.pc = off + 88 ∧
        (run Q s detTape u).halted = false ∧
        (run Q s detTape u).core.ptrs 54 = ((k + 1 : ℕ) : ℤ) ∧
        (run Q s detTape u).core.ptrs 55 = ((c + (if (lab k : ℤ) = L then 1 else 0) : ℕ) : ℤ) ∧
        (∀ x, x ≠ 54 → x ≠ 55 → x ≠ 56 → x ≠ 58 → (run Q s detTape u).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape u).core.regs = s.core.regs ∧ (run Q s detTape u).core.mem = s.core.mem ∧
        (run Q s detTape u).integerMemory = s.integerMemory ∧
        (run Q s detTape u).work = s.work + u ∧ cellsWritten Q s u = ∅ := by
      obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
      simp only at hpc hh h11 h13 h54 h55 h57 lk ⊢; subst hpc hh
      by_cases e1 : L ≤ (lab k : ℤ)
      · by_cases e2 : (lab k : ℤ) ≤ L
        · refine ⟨9, by norm_num, ?_⟩
          rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
          simp only [exec, coreExec, wcell]
          rw [if_neg (by rw [h11, h54]; push_cast; omega)]
          simp only [Nat.add_assoc, Nat.reduceAdd]
          (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
          rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
          simp only [exec, coreExec, wcell, Function.update_apply]
          simp (config := {decide := true}) only [if_true, if_false, h13, h54, h57, lk]
          rw [if_pos e1]
          rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
          simp only [exec, coreExec, wcell, Function.update_apply]
          simp (config := {decide := true}) only [if_true, if_false, h13, h54, h57, lk]
          rw [if_pos e2]
          (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
          rw [run_zero, cw_zero]
          have eq : (lab k : ℤ) = L := le_antisymm e2 e1
          refine ⟨rfl, rfl, by simp [h54], by simp [h55, eq], ?_, rfl, rfl, rfl, rfl, by simp⟩
          intro x x1 x2 x3 x4; simp [x1, x2, x3, x4]
        · refine ⟨9, by norm_num, ?_⟩
          rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
          simp only [exec, coreExec, wcell]
          rw [if_neg (by rw [h11, h54]; push_cast; omega)]
          simp only [Nat.add_assoc, Nat.reduceAdd]
          (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
          rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
          simp only [exec, coreExec, wcell, Function.update_apply]
          simp (config := {decide := true}) only [if_true, if_false, h13, h54, h57, lk]
          rw [if_pos e1]
          rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
          simp only [exec, coreExec, wcell, Function.update_apply]
          simp (config := {decide := true}) only [if_true, if_false, h13, h54, h57, lk]
          rw [if_neg e2]
          simp only [Nat.add_assoc, Nat.reduceAdd]
          (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
          rw [run_zero, cw_zero]
          have ne : (lab k : ℤ) ≠ L := fun h => e2 h.le
          refine ⟨rfl, rfl, by simp [h54], by simp [h55, ne], ?_, rfl, rfl, rfl, rfl, by simp⟩
          intro x x1 x2 x3 x4; simp [x1, x2, x3, x4]
      · refine ⟨8, by norm_num, ?_⟩
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]
        rw [if_neg (by rw [h11, h54]; push_cast; omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell, Function.update_apply]
        simp (config := {decide := true}) only [if_true, if_false, h13, h54, h57, lk]
        rw [if_neg e1]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_zero, cw_zero]
        have ne : (lab k : ℤ) ≠ L := fun h => e1 h.ge
        refine ⟨rfl, rfl, by simp [h54], by simp [h55, ne], ?_, rfl, rfl, rfl, rfl, by simp⟩
        intro x x1 x2 x3 x4; simp [x1, x2, x3, x4]
    obtain ⟨u, hu, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := it
    set s1 := run Q s detTape u with hs1
    obtain ⟨t2, ht2, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
      ih (k + 1) _ s1 (by omega) i1 i2 (by rw [i5 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h11])
        (by rw [i5 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h13]) i3 i4
        (by rw [i5 57 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h57])
        (fun i hi => by rw [i8]; exact hL i hi)
    refine ⟨u + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨c1, c2, ?_, ?_, by rw [c5, i6], by rw [c6, i7], by rw [c7, i8], by rw [c8, i9]; ring, ?_⟩
    · rw [c3, cntFrom_step n lab L k hk]; push_cast; ring
    · intro x x1 x2 x3 x4; rw [c4 x x1 x2 x3 x4, i5 x x1 x2 x3 x4]
    · rw [i10, c9]; simp

/-- Offsets 82–87 for `i₂ < n`: load `lab i₂`, reset the count. -/
lemma q_head (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (n : ℕ) (Z : ℤ) (lab : ℕ → ℕ)
    (i : ℕ) (hi : i < n) (s : State) (hpc : s.core.pc = off + 82) (hh : s.halted = false)
    (h11 : s.core.ptrs 11 = n) (h13 : s.core.ptrs 13 = Z) (h53 : s.core.ptrs 53 = i)
    (hL : ∀ i < n, s.integerMemory (Z - 1 - i) = lab i) :
    (run Q s detTape 6).core.pc = off + 88 ∧ (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 54 = ((0 : ℕ) : ℤ) ∧ (run Q s detTape 6).core.ptrs 55 = ((0 : ℕ) : ℤ) ∧
      (run Q s detTape 6).core.ptrs 57 = (lab i : ℤ) ∧
      (∀ x, x ≠ 54 → x ≠ 55 → x ≠ 56 → x ≠ 57 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧ (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧ cellsWritten Q s 6 = ∅ := by
  have li : s.integerMemory (Z - i - 1) = lab i := by
    rw [show Z - i - 1 = Z - 1 - i by ring]; exact hL i hi
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h11 h13 h53 li ⊢; subst hpc hh
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_neg (by rw [h11, h53]; push_cast; omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, by simp, by simp [h13, h53, li], ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x x1 x2 x3 x4; simp [x1, x2, x3, x4]

open Classical in
/-- Offsets 99–103: the test `n < 2 cnt`, then `i₂ := i₂ + 1`. -/
lemma q_tail (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (n c : ℕ) (q : Bool) (i : ℤ)
    (s : State) (hpc : s.core.pc = off + 99) (hh : s.halted = false) (h11 : s.core.ptrs 11 = n)
    (h53 : s.core.ptrs 53 = i) (h55 : s.core.ptrs 55 = c) (h60 : s.core.ptrs 60 = if q then 1 else 0) :
    ∃ u, u ≤ 5 ∧ (run Q s detTape u).core.pc = off + 82 ∧ (run Q s detTape u).halted = false ∧
      (run Q s detTape u).core.ptrs 53 = i + 1 ∧
      (run Q s detTape u).core.ptrs 60 = (if q = true ∨ ¬ 2 * c ≤ n then 1 else 0) ∧
      (∀ x, x ≠ 53 → x ≠ 59 → x ≠ 60 → (run Q s detTape u).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape u).core.regs = s.core.regs ∧ (run Q s detTape u).core.mem = s.core.mem ∧
      (run Q s detTape u).integerMemory = s.integerMemory ∧
      (run Q s detTape u).work = s.work + u ∧ cellsWritten Q s u = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h11 h53 h55 h60 ⊢; subst hpc hh
  by_cases hc : 2 * c ≤ n
  · refine ⟨4, by norm_num, ?_⟩
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell, Function.update_apply]
    simp (config := {decide := true}) only [if_true, if_false, h55, h11]
    rw [if_pos (by push_cast; omega)]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp [h53], ?_, ?_, rfl, rfl, rfl, rfl, by simp⟩
    · simp only [Function.update_apply]; simp (config := {decide := true}) only [if_false, h60]
      rcases q <;> simp [hc]
    · intro x x1 x2 x3; simp [x1, x2, x3]
  · refine ⟨5, by norm_num, ?_⟩
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell, Function.update_apply]
    simp (config := {decide := true}) only [if_true, if_false, h55, h11]
    rw [if_neg (by push_cast; omega)]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp [h53], ?_, ?_, rfl, rfl, rfl, rfl, by simp⟩
    · simp [hc]
    · intro x x1 x2 x3; simp [x1, x2, x3]

open Classical in
/-- The qualification loop (`Q`, offsets 82–103), exit to `Q_E = 104`. -/
lemma q_loop (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (n : ℕ) (Z : ℤ) (lab : ℕ → ℕ) :
    ∀ kk (i : ℕ) (q : Bool) (s : State), i + kk = n →
      s.core.pc = off + 82 → s.halted = false → s.core.ptrs 11 = n → s.core.ptrs 13 = Z →
      s.core.ptrs 53 = i → s.core.ptrs 60 = (if q then 1 else 0) →
      (∀ i < n, s.integerMemory (Z - 1 - i) = lab i) →
      ∃ t, t ≤ kk * (9 * n + 12) + 1 ∧ (run Q s detTape t).core.pc = off + 104 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 60 =
          (if q = true ∨ ∃ i', i ≤ i' ∧ i' < n ∧ ¬ 2 * cntFrom n lab (lab i') 0 ≤ n then 1 else 0) ∧
        (∀ x, x < 53 ∨ 60 < x → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ := by
  intro kk
  induction kk with
  | zero =>
    intro i q s hik hpc hh h11 h13 h53 h60 hL
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h53 h60 ⊢; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h53]; push_cast; omega)]
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, ?_, fun x _ => rfl, rfl, rfl, rfl, rfl, by simp⟩
    simp only; rw [h60]
    congr 1
    apply propext
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨i', h1, h2, -⟩)
      · exact h
      · omega
  | succ kk ih =>
    intro i q s hik hpc hh h11 h13 h53 h60 hL
    have hi : i < n := by omega
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := q_head Q off hE n Z lab i hi s hpc hh h11 h13 h53 hL
    set s1 := run Q s detTape 6 with hs1
    obtain ⟨t2, ht2, k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ :=
      k_loop Q off hE n Z lab (lab i) n 0 0 s1 (by omega) g1 g2
        (by rw [g6 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h11])
        (by rw [g6 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h13]) g3 g4 g5
        (fun j hj => by rw [g9]; exact hL j hj)
    set s2 := run Q s1 detTape t2 with hs2
    obtain ⟨u, hu, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
      q_tail Q off hE n (0 + cntFrom n lab (lab i) 0) q i s2 k1 k2
        (by rw [k4 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
          g6 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h11])
        (by rw [k4 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
          g6 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h53]) k3
        (by rw [k4 60 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
          g6 60 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h60])
    set s3 := run Q s2 detTape u with hs3
    have hfr3 : ∀ x, x < 53 ∨ 60 < x → s3.core.ptrs x = s.core.ptrs x := by
      intro x hx
      rw [c5 x (by omega) (by omega) (by omega), k4 x (by omega) (by omega) (by omega) (by omega),
        g6 x (by omega) (by omega) (by omega) (by omega)]
    obtain ⟨t4, ht4, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
      ih (i + 1) (decide (q = true ∨ ¬ 2 * (0 + cntFrom n lab (lab i) 0) ≤ n)) s3 (by omega) c1 c2
        (by rw [hfr3 11 (by omega), h11]) (by rw [hfr3 13 (by omega), h13])
        (by rw [c3]; push_cast; ring)
        (by rw [c4]; simp only [decide_eq_true_eq])
        (fun j hj => by rw [c8, k7, g9]; exact hL j hj)
    refine ⟨6 + t2 + u + t4, ?_, ?_⟩
    · have : (kk + 1) * (9 * n + 12) + 1 = (9 * n + 12) + (kk * (9 * n + 12) + 1) := by ring
      have : t2 ≤ 9 * n + 1 := by simpa using ht2
      omega
    have RR : run Q s detTape (6 + t2 + u + t4) = run Q s3 detTape t4 := by
      rw [hs3, hs2, hs1, run_add, run_add, run_add]
    have CW : cellsWritten Q s (6 + t2 + u + t4) =
        cellsWritten Q s 6 ∪ cellsWritten Q s1 t2 ∪ cellsWritten Q s2 u ∪ cellsWritten Q s3 t4 := by
      rw [hs3, hs2, hs1, cellsWritten_add, cellsWritten_add, cellsWritten_add]
      simp only [← run_add]
    rw [RR, CW, g11, k9, c10, d9]
    simp only [Finset.empty_union]
    refine ⟨d1, d2, ?_, ?_, by rw [d5, c6, k5, g7], by rw [d6, c7, k6, g8], by rw [d7, c8, k7, g9],
      by rw [d8, c9, k8, g10]; ring, by simp⟩
    · rw [d3]
      congr 1
      apply propext
      simp only [decide_eq_true_eq, Nat.zero_add]
      constructor
      · rintro ((h | h) | ⟨i', h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, le_rfl, hi, h⟩
        · exact Or.inr ⟨i', by omega, h2, h3⟩
      · rintro (h | ⟨i', h1, h2, h3⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.eq_or_lt_of_le h1 with rfl | h1
          · exact Or.inl (Or.inr h3)
          · exact Or.inr ⟨i', by omega, h2, h3⟩
    · intro x hx; rw [d4 x hx, hfr3 x hx]

/-- Offsets 10–16 for `j < n`: the address of `j`, `sum := 0`, `c := 0`. -/
lemma p_head (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (n j : ℕ) (hj : j < n) (s : State)
    (hpc : s.core.pc = off + 10) (hh : s.halted = false) (h11 : s.core.ptrs 11 = n)
    (h51 : s.core.ptrs 51 = j) :
    (run Q s detTape 7).core.pc = off + 17 ∧ (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 62 = addr s j ∧ (run Q s detTape 7).core.ptrs 63 = ((0 : ℕ) : ℤ) ∧
      (run Q s detTape 7).core.regs 51 = 0 ∧
      (∀ x, x ≠ 56 → x ≠ 62 → x ≠ 63 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 51 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only [addr] at hpc hh h11 h51 ⊢; subst hpc hh
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_neg (by rw [h11, h51]; push_cast; omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp [h51], by simp, by simp, ?_, ?_, rfl, rfl, rfl, by simp⟩
  · intro x x1 x2 x3; simp [x1, x2, x3]
  · intro x x1; simp [x1]

/-- Two straight-line steps: the shape of offsets 27–28 and 80–81. -/
lemma p_sqrt (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (s : State)
    (hpc : s.core.pc = off + 27) (hh : s.halted = false) :
    (run Q s detTape 2).core.pc = off + 29 ∧ (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.regs 54 = Real.sqrt (s.core.regs 51) ∧
      (run Q s detTape 2).core.regs 10 = Real.sqrt (s.core.regs 51) ∧
      (run Q s detTape 2).core.ptrs = s.core.ptrs ∧
      (∀ x, x ≠ 10 → x ≠ 54 → (run Q s detTape 2).core.regs x = s.core.regs x) ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh ⊢; subst hpc hh
  have h28 : (mb off)[28]? = some (Instr.sqrt 10 51) := rfl
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd]
  rw [run_exec_at hE rfl rfl h28, cw_exec_at hE rfl rfl h28]
  simp only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply]
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, by simp, rfl, ?_, rfl, rfl, rfl, by simp⟩
  intro x x1 x2; simp [x1, x2]

lemma p_q0 (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (s : State)
    (hpc : s.core.pc = off + 80) (hh : s.halted = false) :
    (run Q s detTape 2).core.pc = off + 82 ∧ (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 60 = (if false = true then 1 else 0) ∧
      (run Q s detTape 2).core.ptrs 53 = ((0 : ℕ) : ℤ) ∧
      (∀ x, x ≠ 53 → x ≠ 60 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh ⊢; subst hpc hh
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, by simp, ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x x1 x2; simp [x1, x2]

open Classical in
/-- Offsets 104–113: the update of `(found, best)`, then `j := j + 1`. -/
lemma p_tail (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (qq found : Bool) (best d : ℝ)
    (j : ℤ) (s : State) (hpc : s.core.pc = off + 104) (hh : s.halted = false)
    (h60 : s.core.ptrs 60 = if qq then 1 else 0) (h52 : s.core.ptrs 52 = if found then 1 else 0)
    (h51 : s.core.ptrs 51 = j) (r50 : s.core.regs 50 = best) (r54 : s.core.regs 54 = d)
    (r55 : s.core.regs 55 = 0) :
    ∃ u, u ≤ 9 ∧ (run Q s detTape u).core.pc = off + 10 ∧ (run Q s detTape u).halted = false ∧
      (run Q s detTape u).core.ptrs 51 = j + 1 ∧
      (run Q s detTape u).core.ptrs 52 = (if (upd (qq = true) d (found, best)).1 then 1 else 0) ∧
      (run Q s detTape u).core.regs 50 = (upd (qq = true) d (found, best)).2 ∧
      (∀ x, x ≠ 51 → x ≠ 52 → x ≠ 56 → (run Q s detTape u).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 50 → x ≠ 52 → (run Q s detTape u).core.regs x = s.core.regs x) ∧
      (run Q s detTape u).core.mem = s.core.mem ∧ (run Q s detTape u).integerMemory = s.integerMemory ∧
      (run Q s detTape u).work = s.work + u ∧ cellsWritten Q s u = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h60 h52 h51 r50 r54 r55 ⊢; subst hpc hh
  cases qq
  · -- not qualifying
    refine ⟨4, by norm_num, ?_⟩
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell, Function.update_apply]
    simp (config := {decide := true}) only [if_true, if_false, h60]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    unfold upd
    refine ⟨rfl, rfl, by simp [h51], by simp [h52], by simp [r50], ?_, ?_, rfl, rfl, rfl, by simp⟩
    · intro x x1 x2 x3; simp [x1, x2, x3]
    · intro x x1 x2; rfl
  · cases found
    · refine ⟨7, by norm_num, ?_⟩
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell, Function.update_apply]
      simp (config := {decide := true}) only [if_true, if_false, h60]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell, Function.update_apply]
      simp (config := {decide := true}) only [if_true, if_false, h52]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_zero, cw_zero]
      unfold upd
      refine ⟨rfl, rfl, by simp [h51], by simp, by simp [r54, r55], ?_, ?_, rfl, rfl, rfl, by simp⟩
      · intro x x1 x2 x3; simp [x1, x2, x3]
      · intro x x1 x2; simp [x1, x2]
    · by_cases hdb : d ≤ best
      · refine ⟨9, by norm_num, ?_⟩
        rw [show upd (true = true) d (true, best) = (true, d) by
          unfold upd; rw [if_pos ⟨rfl, Or.inr hdb⟩]]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell, Function.update_apply]
        simp (config := {decide := true}) only [if_true, if_false, h60]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell, Function.update_apply]
        simp (config := {decide := true}) only [if_true, if_false, h52]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell, Function.update_apply]
        simp (config := {decide := true}) only [if_true, if_false]
        rw [if_pos (by rw [r54, r50]; linarith)]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_zero, cw_zero]
        refine ⟨rfl, rfl, by simp [h51], by simp, by simp [r54, r55], ?_, ?_, rfl, rfl, rfl, by simp⟩
        · intro x x1 x2 x3; simp [x1, x2, x3]
        · intro x x1 x2; simp [x1, x2]
      · refine ⟨8, by norm_num, ?_⟩
        rw [show upd (true = true) d (true, best) = (true, best) by
          unfold upd; rw [if_neg (fun h => hdb (h.2.resolve_left (by simp)))]]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell, Function.update_apply]
        simp (config := {decide := true}) only [if_true, if_false, h60]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell, Function.update_apply]
        simp (config := {decide := true}) only [if_true, if_false, h52]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell, Function.update_apply]
        simp (config := {decide := true}) only [if_true, if_false]
        rw [if_neg (by rw [r54, r50]; linarith [not_le.1 hdb])]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_zero, cw_zero]
        refine ⟨rfl, rfl, by simp [h51], by simp [h52], by simp [r50], ?_, ?_, rfl, rfl, rfl, by simp⟩
        · intro x x1 x2 x3; simp [x1, x2, x3]
        · intro x x1 x2; simp [x1, x2]

end DetANN.HPIM.MB

-- ===== MB_Main =====
namespace DetANN.HPIM.MB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP DetANN.HPIM.CB

lemma D_eq_sum {m n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin m)) (s : State)
    (hLP : LocalPts s (fun i j => pts i j)) (i j : ℕ) (hi : i < n) (hj : j < n) :
    D pts i j = Real.sqrt (∑ c ∈ Finset.range m,
      (s.core.mem (addr s i + ((0 + c : ℕ) : ℤ)) - s.core.mem (addr s j + ((0 + c : ℕ) : ℤ))) ^ 2) := by
  unfold D
  rw [pt_of_lt pts i hi, pt_of_lt pts j hj, EuclideanSpace.dist_eq, Finset.sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [Real.dist_eq, sq_abs, Nat.zero_add, addr_pts hLP i hi c c.isLt, addr_pts hLP j hj c c.isLt]

lemma cntFrom_cnt (n : ℕ) (lab : ℕ → ℕ) (i : ℕ) : cntFrom n lab (lab i : ℤ) 0 = cnt (n := n) lab i := by
  unfold cntFrom cnt
  rw [Finset.range_eq_Ico]
  congr 1
  apply Finset.filter_congr
  intro k _
  exact Nat.cast_inj

open Classical in
lemma qual_from_labels {m n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) :
    (false = true ∨ ∃ i', 0 ≤ i' ∧ i' < n ∧
      ¬ 2 * cntFrom n (rounds pts d n (fun i => i)) (rounds pts d n (fun i => i) i') 0 ≤ n) ↔
      Qual pts d := by
  rw [← qual_iff pts d (rounds pts d n (fun i => i)) (fun i h => rounds_eq_compMin pts d ⟨i, h⟩)]
  simp only [Bool.false_eq_true, false_or, cntFrom_cnt]
  constructor
  · rintro ⟨i, -, h1, h2⟩; exact ⟨i, h1, h2⟩
  · rintro ⟨i, h1, h2⟩; exact ⟨i, Nat.zero_le _, h1, h2⟩

/-- The bound on one pair. -/
def PB (n m : ℕ) : ℕ := 10 * m + 40 * (n + 1) ^ 3 * (m + 1) + n * (9 * n + 12) + 25

set_option maxHeartbeats 2000000 in
open Classical in
/-- **One pair `(i, j)`** (offsets 10–113). -/
lemma mpair (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) {m n : ℕ}
    (pts : Fin n → EuclideanSpace ℝ (Fin m)) (Z : ℤ) (hZ : Z ≤ 0) (i j : ℕ) (hi : i < n) (hj : j < n)
    (found : Bool) (best : ℝ) (s : State) (hpc : s.core.pc = off + 10) (hh : s.halted = false)
    (hLP : LocalPts s (fun i j => pts i j)) (h13 : s.core.ptrs 13 = Z) (h51 : s.core.ptrs 51 = j)
    (h61 : s.core.ptrs 61 = addr s i) (h52 : s.core.ptrs 52 = if found then 1 else 0)
    (r50 : s.core.regs 50 = best) (r55 : s.core.regs 55 = 0) :
    ∃ t, t ≤ PB n m ∧ (run Q s detTape t).core.pc = off + 10 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 51 = ((j + 1 : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 52 =
        (if (upd (Qual pts (D pts i j)) (D pts i j) (found, best)).1 then 1 else 0) ∧
      (run Q s detTape t).core.regs 50 = (upd (Qual pts (D pts i j)) (D pts i j) (found, best)).2 ∧
      (∀ x, (x < 40 ∨ x = 50 ∨ x = 61) → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, ((x < 40 ∧ x ≠ 10) ∨ x = 55) → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (run Q s detTape t).core.mem = s.core.mem ∧
      (∀ z, (z < Z - n ∨ Z ≤ z) → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, Win n Z c := by
  have h1 : s.core.ptrs 1 = m := hLP.1
  have h11 : s.core.ptrs 11 = n := hLP.2.1
  -- 1. head
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := p_head Q off hE n j hj s hpc hh h11 h51
  set s1 := run Q s detTape 7 with hs1
  -- 2. the squared distance
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    c_loop Q off hE m (addr s i) (addr s j) m 0 0 s1 (by omega) g1 g2
      (by rw [g6 1 (by norm_num) (by norm_num) (by norm_num), h1]) g4
      (by rw [g6 61 (by norm_num) (by norm_num) (by norm_num), h61]) g3 g5
  set s2 := run Q s1 detTape (10 * m + 1) with hs2
  -- 3. d := √sum
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ := p_sqrt Q off hE s2 c1 c2
  set s3 := run Q s2 detTape 2 with hs3
  set d := D pts i j with hd
  have hdS : Real.sqrt (s2.core.regs 51) = d := by
    rw [c3, hd, D_eq_sum pts s hLP i j hi hj, g8, zero_add]
  have hlow3 : ∀ x, (x < 40 ∨ 50 ≤ x) → x ≠ 56 → x ≠ 62 → x ≠ 63 → s3.core.ptrs x = s.core.ptrs x := by
    intro x hx e1 e2 e3; rw [q5, c4 x e1 e3, g6 x e1 e2 e3]
  have hLP3 := lp_transfer hLP (fun x hx => hlow3 x (Or.inl hx) (by omega) (by omega) (by omega))
    (by rw [q7, c6, g8]) (fun z _ => by rw [q8, c7, g9])
  -- 4. the components block at `off + 29`
  obtain ⟨t4, ht4, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ :=
    cb_spec (off + 29) Q (emb_cb hE) pts d s3 q1 q2 hLP3 (by rw [q4, hdS]) (by rw [hd]; exact dist_nonneg)
      (by rw [hlow3 13 (Or.inl (by norm_num)) (by norm_num) (by norm_num) (by norm_num), h13]; exact hZ)
  have hZ3 : s3.core.ptrs 13 = Z := by
    rw [hlow3 13 (Or.inl (by norm_num)) (by norm_num) (by norm_num) (by norm_num), h13]
  rw [hZ3] at b3 b7 b9
  set s4 := run Q s3 detTape t4 with hs4
  -- 5. qual := 0, i₂ := 0
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := p_q0 Q off hE s4 (by rw [b1]) b2
  set s5 := run Q s4 detTape 2 with hs5
  have hfr5 : ∀ x, (x < 40 ∨ 50 ≤ x) → x ≠ 53 → x ≠ 60 → s5.core.ptrs x = s3.core.ptrs x := by
    intro x hx x1 x2; rw [e5 x x1 x2, b4 x hx]
  -- 6. the qualification loop
  set lab := rounds pts d n (fun i => i) with hlab
  obtain ⟨t6, ht6, k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ :=
    q_loop Q off hE n Z lab n 0 false s5 (by omega) e1 e2
      (by rw [hfr5 11 (Or.inl (by norm_num)) (by norm_num) (by norm_num),
        hlow3 11 (Or.inl (by norm_num)) (by norm_num) (by norm_num) (by norm_num), h11])
      (by rw [hfr5 13 (Or.inl (by norm_num)) (by norm_num) (by norm_num), hZ3]) e4 e3
      (fun x hx => by rw [e8]; exact b3 x hx)
  set s6 := run Q s5 detTape t6 with hs6
  have hfr6 : ∀ x, (x < 40 ∨ 60 < x) → s6.core.ptrs x = s3.core.ptrs x := by
    intro x hx; rw [k4 x (by omega), hfr5 x (by omega) (by omega) (by omega)]
  -- registers carried to the tail
  have rg : ∀ x, (x < 40 ∨ 50 ≤ x) → s6.core.regs x = s3.core.regs x := by
    intro x hx; rw [k5, e6, b5 x hx]
  -- 7. the update and `j := j + 1`
  obtain ⟨u, hu, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
    p_tail Q off hE (decide (false = true ∨ ∃ i', 0 ≤ i' ∧ i' < n ∧
      ¬ 2 * cntFrom n lab (lab i') 0 ≤ n)) found best d j s6 k1 k2
      (by rw [k3]; simp only [decide_eq_true_eq])
      (by rw [k4 52 (by omega), hfr5 52 (by omega) (by norm_num) (by norm_num),
        hlow3 52 (by omega) (by norm_num) (by norm_num) (by norm_num), h52])
      (by rw [k4 51 (by omega), hfr5 51 (by omega) (by norm_num) (by norm_num),
        hlow3 51 (by omega) (by norm_num) (by norm_num) (by norm_num), h51])
      (by rw [rg 50 (by omega), q6 50 (by norm_num) (by norm_num), c5 50 (by norm_num) (by norm_num)
        (by norm_num), g7 50 (by norm_num), r50])
      (by rw [rg 54 (by omega), q3, hdS])
      (by rw [rg 55 (by omega), q6 55 (by norm_num) (by norm_num), c5 55 (by norm_num) (by norm_num)
        (by norm_num), g7 55 (by norm_num), r55])
  have hq : (decide (false = true ∨ ∃ i', 0 ≤ i' ∧ i' < n ∧
      ¬ 2 * cntFrom n lab (lab i') 0 ≤ n) = true) = Qual pts d := by
    rw [decide_eq_true_eq]; exact propext (qual_from_labels pts d)
  rw [hq] at p4 p5
  set s7 := run Q s6 detTape u with hs7
  refine ⟨7 + (10 * m + 1) + 2 + t4 + 2 + t6 + u, ?_, ?_⟩
  · unfold PB
    have h6 : t6 ≤ n * (9 * n + 12) + 1 := ht6
    generalize 40 * (n + 1) ^ 3 * (m + 1) = A at ht4 ⊢
    generalize n * (9 * n + 12) = B at h6 ⊢
    omega
  have RR : run Q s detTape (7 + (10 * m + 1) + 2 + t4 + 2 + t6 + u) = s7 := by
    rw [hs7, hs6, hs5, hs4, hs3, hs2, hs1]; simp only [← run_add]
  have CW : cellsWritten Q s (7 + (10 * m + 1) + 2 + t4 + 2 + t6 + u) =
      cellsWritten Q s 7 ∪ cellsWritten Q s1 (10 * m + 1) ∪ cellsWritten Q s2 2 ∪
        cellsWritten Q s3 t4 ∪ cellsWritten Q s4 2 ∪ cellsWritten Q s5 t6 ∪ cellsWritten Q s6 u := by
    rw [hs6, hs5, hs4, hs3, hs2, hs1]
    simp only [cellsWritten_add, ← run_add]
  rw [RR, CW, g11, c9, q10, e10, k9, p11]
  simp only [Finset.empty_union, Finset.union_empty]
  refine ⟨p1, p2, ?_, p4, p5, ?_, ?_, ?_, ?_, ?_, b9⟩
  · rw [p3]; push_cast; ring
  · intro x hx
    rw [p6 x (by omega) (by omega) (by omega), k4 x (by omega), hfr5 x (by omega) (by omega) (by omega),
      hlow3 x (by omega) (by omega) (by omega) (by omega)]
  · intro x hx
    rw [p7 x (by omega) (by omega), rg x (by omega), q6 x (by omega) (by omega),
      c5 x (by omega) (by omega) (by omega), g7 x (by omega)]
  · rw [p8, k6, e7, b6, q7, c6, g8]
  · intro z hz; rw [p9, k7, e8, b7 z hz, q8, c7, g9]
  · rw [p10, k8, e9, b8, q9, c8, g10]; ring

/-- The `j` loop (offset 10): pairs `(i, j')` for `j' ∈ [j, n)`, then exit to `I_NEXT = 114`. -/
lemma jj_loop (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) {m n : ℕ}
    (pts : Fin n → EuclideanSpace ℝ (Fin m)) (Z : ℤ) (hZ : Z ≤ 0) (i : ℕ) (hi : i < n) :
    ∀ k (j : ℕ) (st : Bool × ℝ) (s : State), j + k = n →
      s.core.pc = off + 10 → s.halted = false → LocalPts s (fun i j => pts i j) →
      s.core.ptrs 13 = Z → s.core.ptrs 51 = j → s.core.ptrs 61 = addr s i →
      s.core.ptrs 52 = (if st.1 then 1 else 0) → s.core.regs 50 = st.2 → s.core.regs 55 = 0 →
      ∃ t, t ≤ k * PB n m + 1 ∧ (run Q s detTape t).core.pc = off + 114 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 52 = (if (jsweep pts i j st).1 then 1 else 0) ∧
        (run Q s detTape t).core.regs 50 = (jsweep pts i j st).2 ∧
        (∀ x, (x < 40 ∨ x = 50 ∨ x = 61) → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, ((x < 40 ∧ x ≠ 10) ∨ x = 55) → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (∀ z, (z < Z - n ∨ Z ≤ z) → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, Win n Z c := by
  intro k
  induction k with
  | zero =>
    intro j st s hjk hpc hh hLP h13 h51 h61 h52 r50 r55
    have h11 : s.core.ptrs 11 = n := hLP.2.1
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h51 h52 r50 ⊢; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h51]; push_cast; omega)]
    rw [run_zero, cw_zero]
    rw [jsweep_end pts i j (by omega)]
    exact ⟨rfl, rfl, h52, r50, fun x _ => rfl, fun x _ => rfl, rfl, fun z _ => rfl, rfl, by simp⟩
  | succ k ih =>
    intro j st s hjk hpc hh hLP h13 h51 h61 h52 r50 r55
    obtain ⟨t1, ht1, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
      mpair Q off hE pts Z hZ i j hi (by omega) st.1 st.2 s hpc hh hLP h13 h51 h61 h52 r50 r55
    set s1 := run Q s detTape t1 with hs1
    have hLP1 := lp_transfer hLP (fun x hx => p6 x (Or.inl hx)) p8 (fun z hz => p9 z (by omega))
    have ha1 : addr s1 i = addr s i := by
      unfold addr
      have e1 : 0 ≤ s.core.ptrs 10 + (i : ℤ) := by have := hLP.2.2.1; omega
      have h3 : 0 ≤ s.integerMemory (s.core.ptrs 10 + (i : ℤ)) := (hLP.2.2.2.2 ⟨i, hi⟩).1
      have e2 : 0 ≤ s.core.ptrs 12 + s.integerMemory (s.core.ptrs 10 + (i : ℤ)) := by
        have := hLP.2.2.2.1; omega
      rw [p6 10 (by omega), p6 12 (by omega), p9 (s.core.ptrs 10 + (i : ℤ)) (Or.inr (by omega)),
        p9 (s.core.ptrs 12 + s.integerMemory (s.core.ptrs 10 + (i : ℤ))) (Or.inr (by omega))]
    have hst : (st.1, st.2) = st := rfl
    rw [hst] at p4 p5
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
      ih (j + 1) _ s1 (by omega) p1 p2 hLP1 (by rw [p6 13 (by omega), h13]) p3
        (by rw [p6 61 (by omega), h61, ha1]) p4 p5 (by rw [p7 55 (by omega), r55])
    refine ⟨t1 + t2, ?_, ?_⟩
    · have : (k + 1) * PB n m + 1 = PB n m + (k * PB n m + 1) := by ring
      omega
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, ?_, ?_, ?_, ?_, by rw [q7, p8], ?_, by rw [q9, p10]; ring, ?_⟩
    · rw [q3, jsweep_step pts i j (by omega)]
    · rw [q4, jsweep_step pts i j (by omega)]
    · intro x hx; rw [q5 x hx, p6 x hx]
    · intro x hx; rw [q6 x hx, p7 x hx]
    · intro z hz; rw [q8 z hz, p9 z hz]
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · exact p11 c hc
      · exact q10 c hc

/-- Offsets 4–9 for `i < n`: the address of `i`, `j := 0`. -/
lemma i_head (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (n i : ℕ) (hi : i < n) (s : State)
    (hpc : s.core.pc = off + 4) (hh : s.halted = false) (h11 : s.core.ptrs 11 = n)
    (h50 : s.core.ptrs 50 = i) :
    (run Q s detTape 6).core.pc = off + 10 ∧ (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 61 = addr s i ∧ (run Q s detTape 6).core.ptrs 51 = ((0 : ℕ) : ℤ) ∧
      (∀ x, x ≠ 51 → x ≠ 56 → x ≠ 61 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧ (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧ cellsWritten Q s 6 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only [addr] at hpc hh h11 h50 ⊢; subst hpc hh
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_neg (by rw [h11, h50]; push_cast; omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp [h50], by simp, ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x x1 x2 x3; simp [x1, x2, x3]

/-- Offsets 114–115: `i := i + 1`, back to `I`. -/
lemma i_tail (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) (i : ℤ) (s : State)
    (hpc : s.core.pc = off + 114) (hh : s.halted = false) (h50 : s.core.ptrs 50 = i) :
    (run Q s detTape 2).core.pc = off + 4 ∧ (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 50 = i + 1 ∧
      (∀ x, x ≠ 50 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h50 ⊢; subst hpc hh
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp [h50], ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x e1; simp [e1]

set_option maxHeartbeats 1000000 in
/-- The `i` loop (offset 4), exit to `END = 116`. -/
lemma ii_loop (Q : Program) (off : ℕ) (hE : Embeds Q (mb off) off) {m n : ℕ}
    (pts : Fin n → EuclideanSpace ℝ (Fin m)) (Z : ℤ) (hZ : Z ≤ 0) :
    ∀ k (i : ℕ) (st : Bool × ℝ) (s : State), i + k = n →
      s.core.pc = off + 4 → s.halted = false → LocalPts s (fun i j => pts i j) →
      s.core.ptrs 13 = Z → s.core.ptrs 50 = i →
      s.core.ptrs 52 = (if st.1 then 1 else 0) → s.core.regs 50 = st.2 → s.core.regs 55 = 0 →
      ∃ t, t ≤ k * (n * PB n m + 9) + 1 ∧ (run Q s detTape t).core.pc = off + 116 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.regs 50 = (isweep pts i st).2 ∧
        (∀ x < 40, (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, ((x < 40 ∧ x ≠ 10) ∨ x = 55) → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (∀ z, (z < Z - n ∨ Z ≤ z) → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, Win n Z c := by
  intro k
  induction k with
  | zero =>
    intro i st s hik hpc hh hLP h13 h50 h52 r50 r55
    have h11 : s.core.ptrs 11 = n := hLP.2.1
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h50 r50 ⊢; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h50]; push_cast; omega)]
    rw [run_zero, cw_zero, isweep_end pts i (by omega)]
    exact ⟨rfl, rfl, r50, fun x _ => rfl, fun x _ => rfl, rfl, fun z _ => rfl, rfl, by simp⟩
  | succ k ih =>
    intro i st s hik hpc hh hLP h13 h50 h52 r50 r55
    have hi : i < n := by omega
    have h11 : s.core.ptrs 11 = n := hLP.2.1
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := i_head Q off hE n i hi s hpc hh h11 h50
    set s1 := run Q s detTape 6 with hs1
    have hLP1 := lp_transfer hLP (fun x hx => g5 x (by omega) (by omega) (by omega)) g7 (fun z _ => by rw [g8])
    have ha1 : addr s1 i = addr s i := by
      unfold addr; rw [g8, g5 10 (by norm_num) (by norm_num) (by norm_num),
        g5 12 (by norm_num) (by norm_num) (by norm_num)]
    obtain ⟨t2, ht2, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩ :=
      jj_loop Q off hE pts Z hZ i hi n 0 st s1 (by omega) g1 g2 hLP1
        (by rw [g5 13 (by norm_num) (by norm_num) (by norm_num), h13]) g4 (by rw [g3, ha1])
        (by rw [g5 52 (by norm_num) (by norm_num) (by norm_num), h52]) (by rw [g6, r50]) (by rw [g6, r55])
    set s2 := run Q s1 detTape t2 with hs2
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := i_tail Q off hE i s2 j1 j2
      (by rw [j5 50 (by omega), g5 50 (by norm_num) (by norm_num) (by norm_num), h50])
    set s3 := run Q s2 detTape 2 with hs3
    have hlow3 : ∀ x < 40, s3.core.ptrs x = s.core.ptrs x := by
      intro x hx; rw [c4 x (by omega), j5 x (by omega), g5 x (by omega) (by omega) (by omega)]
    have hLP3 := lp_transfer hLP hlow3 (by rw [c6, j7, g7]) (fun z hz => by rw [c7, j8 z (by omega), g8])
    obtain ⟨t4, ht4, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
      ih (i + 1) (jsweep pts i 0 st) s3 (by omega) c1 c2 hLP3 (by rw [hlow3 13 (by norm_num), h13])
        (by rw [c3]; push_cast; ring)
        (by rw [c4 52 (by norm_num), j3])
        (by rw [c5, j4]) (by rw [c5, j6 55 (by omega), g6, r55])
    refine ⟨6 + t2 + 2 + t4, ?_, ?_⟩
    · have : (k + 1) * (n * PB n m + 9) + 1 = (n * PB n m + 9) + (k * (n * PB n m + 9) + 1) := by ring
      omega
    have RR : run Q s detTape (6 + t2 + 2 + t4) = run Q s3 detTape t4 := by
      rw [hs3, hs2, hs1]; simp only [← run_add]
    have CW : cellsWritten Q s (6 + t2 + 2 + t4) =
        cellsWritten Q s 6 ∪ cellsWritten Q s1 t2 ∪ cellsWritten Q s2 2 ∪ cellsWritten Q s3 t4 := by
      rw [hs3, hs2, hs1]; simp only [cellsWritten_add, ← run_add]
    rw [RR, CW, g10, c9]
    simp only [Finset.empty_union, Finset.union_empty]
    refine ⟨d1, d2, by rw [d3, isweep_step pts i hi], ?_, ?_, by rw [d6, c6, j7, g7], ?_,
      by rw [d8, c8, j9, g9]; ring, ?_⟩
    · intro x hx; rw [d4 x hx, hlow3 x hx]
    · intro x hx; rw [d5 x hx, c5, j6 x hx, g6]
    · intro z hz; rw [d7 z hz, c7, j8 z hz, g8]
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · exact j10 c hc
      · exact d9 c hc

lemma work_le5 (n m : ℕ) :
    4 + (n * (n * PB n m + 9) + 1) + 1 ≤ 100 * (n + 1) ^ 5 * (m + 1) := by
  unfold PB
  have h1 : 10 * m ≤ 10 * (n + 1) ^ 3 * (m + 1) := by
    have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have h2 : n * (9 * n + 12) + 25 ≤ 25 * (n + 1) ^ 3 * (m + 1) := by
    have : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have : 1 ≤ m + 1 := by omega
    nlinarith
  have h3 : 10 * m + 40 * (n + 1) ^ 3 * (m + 1) + n * (9 * n + 12) + 25 ≤ 75 * (n + 1) ^ 3 * (m + 1) := by
    linarith
  have h4 : n * (n * (10 * m + 40 * (n + 1) ^ 3 * (m + 1) + n * (9 * n + 12) + 25) + 9) ≤
      n * (n * (75 * (n + 1) ^ 3 * (m + 1)) + 9) := by gcongr
  have h5 : n * (n * (75 * (n + 1) ^ 3 * (m + 1)) + 9) + 6 ≤ 100 * (n + 1) ^ 5 * (m + 1) := by
    have e : 100 * (n + 1) ^ 5 * (m + 1) = 100 * ((n + 1) ^ 2 * ((n + 1) ^ 3 * (m + 1))) := by ring
    rw [e]
    have : 1 ≤ (n + 1) ^ 3 * (m + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  omega

set_option maxHeartbeats 1000000 in
/-- **The median-threshold block.** -/
theorem median_block' :
    ∃ blk : ℕ → Program, ∃ L C : ℕ, IsBlock blk L ∧
      ∀ (off : ℕ) (Q : Program), Embeds Q (blk off) off →
      ∀ (m n : ℕ) (pts : Fin n → EuclideanSpace ℝ (Fin m)) (s : State),
        1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false →
        LocalPts s (fun i j => pts i j) → s.core.ptrs 13 ≤ 0 →
        ∃ t, (run Q s detTape t).core.pc = off + L ∧ (run Q s detTape t).halted = false ∧
          (run Q s detTape t).core.regs 10 = medThreshold pts ∧
          KeepsLow s (run Q s detTape t) [] [10] ∧
          WritesOnly Q s t (fun c => c.1 = false ∧
            s.core.ptrs 13 - C * (n + 1) ≤ c.2 ∧ c.2 < s.core.ptrs 13) ∧
          (run Q s detTape t).work ≤ s.work + C * (n + 1) ^ 5 * (m + 1) := by
  refine ⟨mb, 117, 100, mb_block, fun off Q hE m n pts s hm hn hpc hh hLP hZ => ?_⟩
  set Z := s.core.ptrs 13 with hZdef
  -- steps 0–3
  have seg : (run Q s detTape 4).core.pc = off + 4 ∧ (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 50 = ((0 : ℕ) : ℤ) ∧
      (run Q s detTape 4).core.ptrs 52 = (if (false, (0 : ℝ)).1 then 1 else 0) ∧
      (run Q s detTape 4).core.regs 50 = (false, (0 : ℝ)).2 ∧ (run Q s detTape 4).core.regs 55 = 0 ∧
      (∀ x, x ≠ 50 → x ≠ 52 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 50 → x ≠ 55 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧ cellsWritten Q s 4 = ∅ := by
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh ⊢; subst hh
    rw [show pc = off + 0 from hpc]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp, by simp, by simp, by simp, ?_, ?_, rfl, rfl, rfl, by simp⟩
    · intro x x1 x2; simp [x1, x2]
    · intro x x1 x2; simp [x1, x2]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := seg
  set s1 := run Q s detTape 4 with hs1
  have hLP1 := lp_transfer hLP (fun x hx => g7 x (by omega) (by omega)) g9 (fun z _ => by rw [g10])
  obtain ⟨t2, ht2, i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ :=
    ii_loop Q off hE pts Z hZ n 0 (false, 0) s1 (by omega) g1 g2 hLP1
      (by rw [g7 13 (by norm_num) (by norm_num)]) g3 g4 g5 g6
  set s2 := run Q s1 detTape t2 with hs2
  -- step 116: r10 := best
  have seg2 : (run Q s2 detTape 1).core.pc = off + 117 ∧ (run Q s2 detTape 1).halted = false ∧
      (run Q s2 detTape 1).core.regs 10 = s2.core.regs 50 + s2.core.regs 55 ∧
      (run Q s2 detTape 1).core.ptrs = s2.core.ptrs ∧
      (∀ x, x ≠ 10 → (run Q s2 detTape 1).core.regs x = s2.core.regs x) ∧
      (run Q s2 detTape 1).core.mem = s2.core.mem ∧
      (run Q s2 detTape 1).integerMemory = s2.integerMemory ∧
      (run Q s2 detTape 1).work = s2.work + 1 ∧ cellsWritten Q s2 1 = ∅ := by
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s2
    simp only at i1 i2 ⊢; subst i1 i2
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp, rfl, ?_, rfl, rfl, rfl, by simp⟩
    intro x x1; simp [x1]
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := seg2
  refine ⟨4 + t2 + 1, ?_⟩
  have RR : run Q s detTape (4 + t2 + 1) = run Q s2 detTape 1 := by
    rw [hs2, hs1]; simp only [← run_add]
  have CW : cellsWritten Q s (4 + t2 + 1) =
      cellsWritten Q s 4 ∪ cellsWritten Q s1 t2 ∪ cellsWritten Q s2 1 := by
    rw [hs2, hs1]; simp only [cellsWritten_add, ← run_add]
  rw [RR]
  refine ⟨e1, e2, ?_, ⟨fun x hx _ => ?_, fun x hx hx10 => ?_⟩, ?_, ?_⟩
  · rw [e3, i3, i5 55 (Or.inr rfl), g6, add_zero]
    exact isweep_eq_med pts
  · rw [e4, i4 x hx, g7 x (by omega) (by omega)]
  · simp only [List.mem_singleton] at hx10
    rw [e5 x hx10, i5 x (Or.inl ⟨hx, hx10⟩), g8 x (by omega) (by omega)]
  · intro c hc
    rw [CW, g12, e9] at hc
    simp only [Finset.empty_union, Finset.union_empty] at hc
    obtain ⟨w1, w2, w3⟩ := i9 c hc
    refine ⟨w1, ?_, w3⟩
    have : (n : ℤ) ≤ 100 * ((n : ℤ) + 1) := by omega
    push_cast; omega
  · rw [e8, i8, g11]
    have hw := work_le5 n m
    have : t2 ≤ n * (n * PB n m + 9) + 1 := ht2
    omega

end DetANN.HPIM.MB

namespace DetANN.HPIM

open PNormReg PNormRegLib

theorem _root_.solution :
    ∃ blk : ℕ → Program, ∃ L C : ℕ, IsBlock blk L ∧
      ∀ (off : ℕ) (Q : Program), Embeds Q (blk off) off →
      ∀ (m n : ℕ) (pts : Fin n → EuclideanSpace ℝ (Fin m)) (s : State),
        1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false →
        LocalPts s (fun i j => pts i j) → s.core.ptrs 13 ≤ 0 →
        ∃ t, (run Q s detTape t).core.pc = off + L ∧ (run Q s detTape t).halted = false ∧
          (run Q s detTape t).core.regs 10 = medThreshold pts ∧
          KeepsLow s (run Q s detTape t) [] [10] ∧
          WritesOnly Q s t (fun c => c.1 = false ∧
            s.core.ptrs 13 - C * (n + 1) ≤ c.2 ∧ c.2 < s.core.ptrs 13) ∧
          (run Q s detTape t).work ≤ s.work + C * (n + 1) ^ 5 * (m + 1) :=
  DetANN.HPIM.MB.median_block'

end DetANN.HPIM
