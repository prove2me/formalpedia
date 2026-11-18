-- Prove2me | solution 1 for DetANN.HPIM.PP.lk_loop
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T09:27:28.931264+00:00
-- url     : https://prove2.me/submissions/e5c5f53a-ee23-4611-826c-47569a58c644

import Mathlib
import Definitions.Def_DetANN_HPIMPreProg
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks
import Theorems.Thm_DetANN_HPIM_build_size

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

/-- Cells outside a write window keep their values. -/
lemma unwritten_of_writesOnly {P : Program} {s : State} {t : ℕ} {W : Bool × ℤ → Prop}
    (h : WritesOnly P s t W) :
    (∀ z, ¬ W (true, z) → (run P s detTape t).core.mem z = s.core.mem z) ∧
    (∀ z, ¬ W (false, z) → (run P s detTape t).integerMemory z = s.integerMemory z) :=
  ⟨fun z hz => run_mem_unwritten P s z t (fun hc => hz (h _ hc)),
   fun z hz => run_im_unwritten P s z t (fun hc => hz (h _ hc))⟩

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

lemma emb6 (hB : B.WF) : Embeds (Blocks.prog B) (seg6 B.o6 B.lbl_LKE) (B.o6) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 8 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5) (seg6 B.o6 B.lbl_LKE)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb7 (hB : B.WF) : Embeds (Blocks.prog B) (B.build B.o7) (B.o7) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 7 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE) (B.build B.o7)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb9 (hB : B.WF) : Embeds (Blocks.prog B) (B.bal B.o9) (B.o9) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 5 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8) (B.bal B.o9)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb10 (hB : B.WF) : Embeds (Blocks.prog B) (seg10 B.o10 B.lbl_LK) (B.o10) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 4 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8 ++ B.bal B.o9) (seg10 B.o10 B.lbl_LK)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

end DetANN.HPIM.PP

-- ===== PP_Sem =====
namespace DetANN.HPIM.PP

open DetANN.HPIM

variable {m : ℕ}

section Comp

variable {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ)

end Comp

section Ladder

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

lemma rhoOf_succ (S : Finset (Fin N)) (k : ℕ) :
    rhoOf Y δ S (k + 1) = rhoOf Y δ S k * (1 + δ / 4) := by
  unfold rhoOf; ring

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

-- ===== PP_Fold =====
namespace DetANN.HPIM.PP

open DetANN.HPIM

/-- Running minimum of `f 0, …, f k` (update `mn := x` when `x − mn ≤ 0`). -/
noncomputable def rmin (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | k + 1 => if f (k + 1) - rmin f k ≤ 0 then f (k + 1) else rmin f k

/-- Running maximum of `f 0, …, f k` (update `mx := x` when `mx − x ≤ 0`). -/
noncomputable def rmax (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | k + 1 => if rmax f k - f (k + 1) ≤ 0 then f (k + 1) else rmax f k

lemma rmin_succ (f : ℕ → ℝ) (k : ℕ) : rmin f (k + 1) = min (f (k + 1)) (rmin f k) := by
  simp only [rmin]
  split_ifs with h
  · exact (min_eq_left (by linarith)).symm
  · exact (min_eq_right (by linarith)).symm

lemma rmax_succ (f : ℕ → ℝ) (k : ℕ) : rmax f (k + 1) = max (f (k + 1)) (rmax f k) := by
  simp only [rmax]
  split_ifs with h
  · exact (max_eq_left (by linarith)).symm
  · exact (max_eq_right (by linarith)).symm

lemma rmin_le (f : ℕ → ℝ) : ∀ k i, i ≤ k → rmin f k ≤ f i := by
  intro k
  induction k with
  | zero => intro i hi; rw [Nat.le_zero.1 hi]; exact le_rfl
  | succ k ih =>
    intro i hi
    rw [rmin_succ]
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact (min_le_right _ _).trans (ih i (by omega))
    · rw [show i = k + 1 by omega]; exact min_le_left _ _

lemma rmin_mem (f : ℕ → ℝ) : ∀ k, ∃ i ≤ k, rmin f k = f i := by
  intro k
  induction k with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ k ih =>
    obtain ⟨i, hi, he⟩ := ih
    rw [rmin_succ]
    rcases min_choice (f (k + 1)) (rmin f k) with h | h
    · exact ⟨k + 1, le_rfl, h⟩
    · exact ⟨i, by omega, h.trans he⟩

lemma rmax_ge (f : ℕ → ℝ) : ∀ k i, i ≤ k → f i ≤ rmax f k := by
  intro k
  induction k with
  | zero => intro i hi; rw [Nat.le_zero.1 hi]; exact le_rfl
  | succ k ih =>
    intro i hi
    rw [rmax_succ]
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact (ih i (by omega)).trans (le_max_right _ _)
    · rw [show i = k + 1 by omega]; exact le_max_left _ _

lemma rmax_mem (f : ℕ → ℝ) : ∀ k, ∃ i ≤ k, rmax f k = f i := by
  intro k
  induction k with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ k ih =>
    obtain ⟨i, hi, he⟩ := ih
    rw [rmax_succ]
    rcases max_choice (f (k + 1)) (rmax f k) with h | h
    · exact ⟨k + 1, le_rfl, h⟩
    · exact ⟨i, by omega, h.trans he⟩

/-- Over `Fin n`, the running minimum to `n − 1` is `Finset.univ.inf'`. -/
lemma rmin_fin {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ) (f : ℕ → ℝ) (hf : ∀ i : Fin n, f i = g i) :
    rmin f (n - 1) = Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ g := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro i _
    rw [← hf i]
    exact rmin_le f _ i (by omega)
  · obtain ⟨i, hi, he⟩ := rmin_mem f (n - 1)
    rw [he, hf ⟨i, by omega⟩]
    exact Finset.inf'_le _ (Finset.mem_univ _)

lemma rmax_fin {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ) (f : ℕ → ℝ) (hf : ∀ i : Fin n, f i = g i) :
    rmax f (n - 1) = Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ g := by
  apply le_antisymm
  · obtain ⟨i, hi, he⟩ := rmax_mem f (n - 1)
    rw [he, hf ⟨i, by omega⟩]
    exact Finset.le_sup' _ (Finset.mem_univ _)
  · apply Finset.sup'_le
    intro i _
    rw [← hf i]
    exact rmax_ge f _ i (by omega)

/-- `sigma` is the running maximum of the side lengths. -/
lemma sigma_eq_rmax {m : ℕ} (hm : 0 < m) (lo hi : Fin m → ℝ) (f : ℕ → ℝ)
    (hf : ∀ j : Fin m, f j = hi j - lo j) : sigma lo hi = rmax f (m - 1) := by
  rw [rmax_fin hm (fun j => hi j - lo j) f hf]
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  unfold sigma
  rw [← Finset.sup'_univ_eq_ciSup]

end DetANN.HPIM.PP

-- ===== PP_Box =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The inner loop `B2`: from point `k ≥ 1` with the running min/max of points `< k`, reach `B2E`
with the running min/max of all `n` points of coordinate `J`. -/
lemma box_B2 (Q : Program) (off LKE : ℕ) (hE : Embeds Q (seg6 off LKE) off) (n : ℕ) (f : ℕ → ℝ)
    (PA Sa J : ℤ) :
    ∀ d k, k + d = n → 1 ≤ k → ∀ s : State, s.core.pc = off + 33 → s.halted = false →
      s.core.ptrs 11 = n → s.core.ptrs 31 = k → s.core.ptrs 12 = PA → s.core.ptrs 10 = Sa →
      s.core.ptrs 22 = J → s.core.regs 20 = 0 →
      (∀ i : ℕ, i < n → s.core.mem (s.integerMemory (PA + s.integerMemory (Sa + i)) + J) = f i) →
      s.core.regs 15 = rmin f (k - 1) → s.core.regs 16 = rmax f (k - 1) →
      (run Q s detTape (15 * d + 1)).core.pc = off + 50 ∧
        (run Q s detTape (15 * d + 1)).halted = false ∧
        (run Q s detTape (15 * d + 1)).core.regs 15 = rmin f (n - 1) ∧
        (run Q s detTape (15 * d + 1)).core.regs 16 = rmax f (n - 1) ∧
        (∀ x, x ∉ [5, 15, 16, 17] → (run Q s detTape (15 * d + 1)).core.regs x = s.core.regs x) ∧
        (∀ x, x ∉ [6, 31] → (run Q s detTape (15 * d + 1)).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape (15 * d + 1)).integerMemory = s.integerMemory ∧
        (run Q s detTape (15 * d + 1)).core.mem = s.core.mem ∧
        (run Q s detTape (15 * d + 1)).work = s.work + (15 * d + 1) ∧
        cellsWritten Q s (15 * d + 1) = ∅ := by
  intro d
  induction d with
  | zero =>
    intro k hk hk1 s hpc hh h11 h31 _ _ _ _ _ h15 h16
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h31 h15 h16; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h31]; omega), run_zero, cw_zero]
    simp only [Nat.add_zero] at hk; subst hk
    refine ⟨rfl, rfl, h15, h16, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, by simp⟩
  | succ d ih =>
    intro k hk hk1 s hpc hh h11 h31 h12 h10 h22 h20 hf h15 h16
    have hkn : k < n := by omega
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h31 h12 h10 h22 h20 hf h15 h16; subst hpc hh
    have hx := hf k hkn
    -- the iteration, as a state equation
    have step15 : ∃ S : State, run Q ⟨⟨off + 33, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 15 = S ∧
        cellsWritten Q ⟨⟨off + 33, regs, ptrs, mem⟩, im, cur, false, w⟩ 15 = ∅ ∧
        S.core.pc = off + 33 ∧ S.halted = false ∧ S.core.regs 15 = rmin f k ∧
        S.core.regs 16 = rmax f k ∧ S.core.ptrs 31 = ((k + 1 : ℕ) : ℤ) ∧
        (∀ x, x ∉ [5, 15, 16, 17] → S.core.regs x = regs x) ∧
        (∀ x, x ∉ [6, 31] → S.core.ptrs x = ptrs x) ∧ S.integerMemory = im ∧ S.core.mem = mem ∧
        S.work = w + 15 := by
      have hx' : mem (im (ptrs 12 + im (ptrs 10 + ptrs 31)) + ptrs 22) = f k := by
        rw [h12, h10, h31, h22]; exact hx
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at h15 h16
      refine ⟨_, rfl, ?_⟩
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell]
      rw [if_neg (by rw [h11, h31]; push_cast; omega)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply,
        if_true, if_false, hx', h15, h20, Nat.add_assoc, Nat.reduceAdd]
      split_ifs with c1
      all_goals (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      all_goals (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      all_goals (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
                 simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply,
                   if_true, if_false, h16, h20, add_zero, Nat.add_assoc, Nat.reduceAdd])
      all_goals split_ifs with c2
      all_goals (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      all_goals (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      all_goals (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      all_goals rw [run_zero, cw_zero]
      all_goals clear hE
      all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (first | rfl | trivial)
      all_goals first
        | (intro x hx
           simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
           simp (config := {decide := true}) [Function.update_apply, hx])
        | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false, h20,
             add_zero, show 1 + k' = k' + 1 from Nat.add_comm 1 k', rmin, rmax, c1, c2, h15, h16]; done)
        | (simp (config := {decide := true}) only [Function.update_apply, if_true, if_false, h31]
           push_cast; ring)
    obtain ⟨S, hS, hcw, a1, a2, a3, a4, a5, a6, a7, a8, a9, aw⟩ := step15
    have e11 : S.core.ptrs 11 = n := by rw [a7 11 (by simp)]; exact h11
    have e12 : S.core.ptrs 12 = PA := by rw [a7 12 (by simp)]; exact h12
    have e10 : S.core.ptrs 10 = Sa := by rw [a7 10 (by simp)]; exact h10
    have e22 : S.core.ptrs 22 = J := by rw [a7 22 (by simp)]; exact h22
    have e20 : S.core.regs 20 = 0 := by rw [a6 20 (by simp)]; exact h20
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, bw, bcw⟩ := ih (k + 1) (by omega) (by omega) S a1 a2 e11
      a5 e12 e10 e22 e20 (by rw [a8, a9]; exact hf) (by simpa using a3) (by simpa using a4)
    rw [show 15 * (d + 1) + 1 = 15 + (15 * d + 1) by ring, run_add, cellsWritten_add, hS, hcw, bcw]
    refine ⟨b1, b2, b3, b4, ?_, ?_, by rw [b7, a8], by rw [b8, a9], by rw [bw, aw]; ring, by simp⟩
    · intro x hx; rw [b5 x hx, a6 x hx]
    · intro x hx; rw [b6 x hx, a7 x hx]

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- Coordinate `j` of local point `i`, as the root-box loops read it. -/
def coordFn (P : ℕ → ℕ → ℝ) (j : ℕ) : ℕ → ℝ := fun i => P i j

/-- The side length `mx_j − mn_j` of the bounding box. -/
noncomputable def sideFn (P : ℕ → ℕ → ℝ) (n : ℕ) : ℕ → ℝ :=
  fun j => rmax (coordFn P j) (n - 1) - rmin (coordFn P j) (n - 1)

/-- The data of the root-box loops: points at `ad i + j` (all below `HRb`), never written. -/
structure BoxData (n m : ℕ) (P : ℕ → ℕ → ℝ) (PA Sa HRb : ℤ) (s : State) : Prop where
  pts : ∀ i < n, ∀ j < m, s.core.mem (s.integerMemory (PA + s.integerMemory (Sa + i)) + j) = P i j
  below : ∀ i < n, ∀ j < m, s.integerMemory (PA + s.integerMemory (Sa + i)) + j < HRb

/-- One iteration of `B1` (coordinate `j < m`). -/
lemma box_B1_iter (Q : Program) (off LKE : ℕ) (hE : Embeds Q (seg6 off LKE) off) (n m : ℕ)
    (hn : 1 ≤ n) (P : ℕ → ℕ → ℝ) (PA Sa HRb : ℤ) (j : ℕ) (hj : j < m) (s : State)
    (hpc : s.core.pc = off + 25) (hh : s.halted = false) (h1 : s.core.ptrs 1 = m)
    (h11 : s.core.ptrs 11 = n) (h12 : s.core.ptrs 12 = PA) (h10 : s.core.ptrs 10 = Sa)
    (h22 : s.core.ptrs 22 = j) (h29 : s.core.ptrs 29 = HRb) (h20 : s.core.regs 20 = 0)
    (hD : BoxData n m P PA Sa HRb s) (h13 : 1 ≤ j → s.core.regs 13 = rmax (sideFn P n) (j - 1)) :
    ∃ t, t ≤ 15 * n + 30 ∧
      (run Q s detTape t).core.pc = off + 25 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 22 = ((j + 1 : ℕ) : ℤ) ∧
      (run Q s detTape t).core.regs 13 = rmax (sideFn P n) j ∧
      (run Q s detTape t).core.mem = Function.update (Function.update s.core.mem (HRb + j)
        (rmin (coordFn P j) (n - 1))) (HRb + j + m) (rmax (coordFn P j) (n - 1)) ∧
      (∀ x, x ∉ [5, 6, 13, 15, 16, 17] → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (∀ x, x ∉ [6, 22, 27, 31] → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t ∧
      cellsWritten Q s t ⊆ {(true, HRb + j), (true, HRb + j + m)} := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h1 h11 h12 h10 h22 h29 h20 h13; subst hpc hh
  have hp0 : mem (im (PA + im (Sa + 0)) + j) = P 0 j := hD.pts 0 hn j hj
  -- steps 25–32
  set S1 := run Q ⟨⟨off + 25, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 8 with hS1
  have e1 : S1 = ⟨⟨off + 33, Function.update (Function.update regs 15 (P 0 j)) 16 (P 0 j),
      Function.update (Function.update ptrs 6 (im (PA + im Sa) + j)) 31 1, mem⟩, im, cur, false,
      w + 8⟩ ∧ cellsWritten Q ⟨⟨off + 25, regs, ptrs, mem⟩, im, cur, false, w⟩ 8 = ∅ := by
    rw [hS1]
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_neg (by rw [h1, h22]; push_cast; omega)]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    simp only [add_zero] at hp0
    refine ⟨?_, by simp⟩
    simp only [h10, h12, h22, hp0, h20, add_zero, Function.update_idem]
  obtain ⟨e1, cw1⟩ := e1
  -- the inner loop B2
  have hf : ∀ i : ℕ, i < n → S1.core.mem (S1.integerMemory (PA + S1.integerMemory (Sa + i)) + j) =
      coordFn P j i := by
    intro i hi; rw [e1]; exact hD.pts i hi j hj
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, bw, bcw⟩ :=
    box_B2 Q off LKE hE n (coordFn P j) PA Sa (j : ℤ) (n - 1) 1 (by omega) le_rfl S1
      (by rw [e1]) (by rw [e1]) (by rw [e1]; simp [h11]) (by rw [e1]; simp)
      (by rw [e1]; simp [h12]) (by rw [e1]; simp [h10]) (by rw [e1]; simp [h22])
      (by rw [e1]; simp [h20]) hf (by rw [e1]; simp [rmin, coordFn])
      (by rw [e1]; simp [rmax, coordFn])
  generalize hS2 : run Q S1 detTape (15 * (n - 1) + 1) = S2 at b1 b2 b3 b4 b5 b6 b7 b8 bw bcw
  obtain ⟨⟨pc2, regs2, ptrs2, mem2⟩, im2, cur2, hlt2, w2⟩ := S2
  simp only at b1 b2 b3 b4 b5 b6 b7 b8 bw; subst b1 b2
  rw [e1] at b5 b6 b7 b8 bw
  simp only at b5 b6 b7 b8 bw
  subst im2 mem2
  -- steps 50–55
  have p29 : ptrs2 29 = HRb := by rw [b6 29 (by simp)]; simp [h29]
  have p22 : ptrs2 22 = j := by rw [b6 22 (by simp)]; simp [h22]
  have p1 : ptrs2 1 = m := by rw [b6 1 (by simp)]; simp [h1]
  have r13 : regs2 13 = regs 13 := by rw [b5 13 (by simp)]; simp
  have r20 : regs2 20 = 0 := by rw [b5 20 (by simp)]; simp [h20]
  have hne : HRb + j ≠ HRb + j + m := by omega
  have hside : rmax (coordFn P j) (n - 1) - rmin (coordFn P j) (n - 1) = sideFn P n j := rfl
  -- the tail, from `off + 50`
  have tail : ∃ u, (u = 10 ∨ u = 12) ∧
      (run Q ⟨⟨off + 50, regs2, ptrs2, mem⟩, im, cur2, false, w2⟩ detTape u).core.pc = off + 25 ∧
      (run Q ⟨⟨off + 50, regs2, ptrs2, mem⟩, im, cur2, false, w2⟩ detTape u).halted = false ∧
      (run Q ⟨⟨off + 50, regs2, ptrs2, mem⟩, im, cur2, false, w2⟩ detTape u).core.ptrs 22 =
        ((j + 1 : ℕ) : ℤ) ∧
      (run Q ⟨⟨off + 50, regs2, ptrs2, mem⟩, im, cur2, false, w2⟩ detTape u).core.regs 13 =
        rmax (sideFn P n) j ∧
      (run Q ⟨⟨off + 50, regs2, ptrs2, mem⟩, im, cur2, false, w2⟩ detTape u).core.mem =
        Function.update (Function.update mem (HRb + j) (rmin (coordFn P j) (n - 1))) (HRb + j + m)
          (rmax (coordFn P j) (n - 1)) ∧
      (∀ x, x ∉ [5, 6, 13] →
        (run Q ⟨⟨off + 50, regs2, ptrs2, mem⟩, im, cur2, false, w2⟩ detTape u).core.regs x = regs2 x) ∧
      (∀ x, x ∉ [6, 22, 27] →
        (run Q ⟨⟨off + 50, regs2, ptrs2, mem⟩, im, cur2, false, w2⟩ detTape u).core.ptrs x = ptrs2 x) ∧
      (run Q ⟨⟨off + 50, regs2, ptrs2, mem⟩, im, cur2, false, w2⟩ detTape u).integerMemory = im ∧
      (run Q ⟨⟨off + 50, regs2, ptrs2, mem⟩, im, cur2, false, w2⟩ detTape u).work = w2 + u ∧
      cellsWritten Q ⟨⟨off + 50, regs2, ptrs2, mem⟩, im, cur2, false, w2⟩ u ⊆
        {(true, HRb + j), (true, HRb + j + m)} := by
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨10, Or.inl rfl, ?_⟩
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply,
        if_true, if_false, p22, Nat.cast_zero, le_refl, Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_zero, cw_zero]
      clear hE
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (first | rfl | trivial)
      all_goals first
        | (intro c hc
           simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union,
             Finset.union_empty, Finset.mem_union, Finset.mem_singleton, p29, p1, add_zero] at hc
           simp only [Finset.mem_insert, Finset.mem_singleton, add_zero]
           rcases hc with h | h <;> simp [h])
        | (intro x hx
           simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
           simp (config := {decide := true}) [Function.update_apply, hx])
        | (simp (config := {decide := true}) [Function.update_apply, p29, p22, p1, b3, b4, r20,
             rmax, hside]; done)
        | (simp (config := {decide := true}) [Function.update_apply, p29, p22, p1, b3, b4, r20]
           push_cast; ring)
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hs13 := h13 (by omega)
      simp only [Nat.add_sub_cancel] at hs13
      refine ⟨12, Or.inr rfl, ?_⟩
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply,
        if_true, if_false, p22]
      rw [if_neg (by push_cast; omega)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply,
        if_true, if_false, r13, hs13, b3, b4, hside, Nat.add_assoc, Nat.reduceAdd]
      split_ifs with c1
      all_goals (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      all_goals (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      all_goals (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      all_goals rw [run_zero, cw_zero]
      all_goals clear hE
      all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (first | rfl | trivial)
      all_goals first
        | (intro c hc
           simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union,
             Finset.union_empty, Finset.mem_union, Finset.mem_singleton, p29, p1, add_zero] at hc
           simp only [Finset.mem_insert, Finset.mem_singleton, add_zero]
           rcases hc with h | h <;> simp [h])
        | (intro x hx
           simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
           simp (config := {decide := true}) [Function.update_apply, hx])
        | (simp (config := {decide := true}) [Function.update_apply, p29, p22, p1, b3, b4, r20,
             rmax, hside, c1, hs13, r13]; done)
        | (simp (config := {decide := true}) [Function.update_apply, p29, p22, p1, b3, b4, r20]
           push_cast; ring)

  obtain ⟨u, hu, c1, c2, c3, c4, c5, c6, c7, c8, cw, ccw⟩ := tail
  refine ⟨8 + (15 * (n - 1) + 1) + u, by omega, ?_⟩
  rw [run_add, run_add, ← hS1, hS2, cellsWritten_add, cellsWritten_add, run_add, ← hS1, hS2, cw1, bcw]
  refine ⟨c1, c2, c3, c4, c5, ?_, ?_, c8, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [c6 x (by simp [hx.1, hx.2.1, hx.2.2.1]), b5 x (by simp [hx.1, hx.2.2.2.1, hx.2.2.2.2.1,
      hx.2.2.2.2.2])]
    simp [Function.update_apply, hx.2.2.2.1, hx.2.2.2.2.1]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [c7 x (by simp [hx.1, hx.2.1, hx.2.2.1]), b6 x (by simp [hx.1, hx.2.2.2])]
    simp [Function.update_apply, hx.1, hx.2.2.2]
  · rw [cw, bw]; ring
  · simpa using ccw

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The loop `B1`: from coordinate `j`, reach `B1E` (`off + 63`) with all `m` coordinates done. -/
lemma box_B1 (Q : Program) (off LKE : ℕ) (hE : Embeds Q (seg6 off LKE) off) (n m : ℕ) (hn : 1 ≤ n)
    (P : ℕ → ℕ → ℝ) (PA Sa HRb : ℤ) :
    ∀ d j, j + d = m → ∀ s : State, s.core.pc = off + 25 → s.halted = false →
      s.core.ptrs 1 = m → s.core.ptrs 11 = n → s.core.ptrs 12 = PA → s.core.ptrs 10 = Sa →
      s.core.ptrs 22 = j → s.core.ptrs 29 = HRb → s.core.regs 20 = 0 → BoxData n m P PA Sa HRb s →
      (1 ≤ j → s.core.regs 13 = rmax (sideFn P n) (j - 1)) →
      (∀ j' < j, s.core.mem (HRb + j') = rmin (coordFn P j') (n - 1) ∧
        s.core.mem (HRb + j' + m) = rmax (coordFn P j') (n - 1)) →
      ∃ t, t ≤ (15 * n + 30) * d + 1 ∧
        (run Q s detTape t).core.pc = off + 63 ∧ (run Q s detTape t).halted = false ∧
        (1 ≤ m → (run Q s detTape t).core.regs 13 = rmax (sideFn P n) (m - 1)) ∧
        (∀ j' < m, (run Q s detTape t).core.mem (HRb + j') = rmin (coordFn P j') (n - 1) ∧
          (run Q s detTape t).core.mem (HRb + j' + m) = rmax (coordFn P j') (n - 1)) ∧
        (∀ z, (z < HRb ∨ HRb + 2 * m ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (∀ x, x ∉ [5, 6, 13, 15, 16, 17] → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (∀ x, x ∉ [6, 22, 27, 31] → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        (∀ c ∈ cellsWritten Q s t, c.1 = true ∧ HRb ≤ c.2 ∧ c.2 < HRb + 2 * m) := by
  intro d
  induction d with
  | zero =>
    intro j hj s hpc hh h1 _ _ _ h22 _ _ _ h13 hc
    simp only [Nat.add_zero] at hj; subst hj
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h1 h22 h13 hc; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h1, h22]), run_zero, cw_zero]
    refine ⟨rfl, rfl, ?_, hc, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, by simp⟩
    intro hm; exact h13 hm
  | succ d ih =>
    intro j hj s hpc hh h1 h11 h12 h10 h22 h29 h20 hD h13 hc
    have hjm : j < m := by omega
    obtain ⟨t1, ht1, a1, a2, a3, a4, a5, a6, a7, a8, aw, acw⟩ :=
      box_B1_iter Q off LKE hE n m hn P PA Sa HRb j hjm s hpc hh h1 h11 h12 h10 h22 h29 h20 hD h13
    set S := run Q s detTape t1 with hS
    have hD' : BoxData n m P PA Sa HRb S := by
      refine ⟨fun i hi j' hj' => ?_, fun i hi j' hj' => ?_⟩
      · rw [a8, a5, Function.update_of_ne, Function.update_of_ne]
        · exact hD.pts i hi j' hj'
        · have := hD.below i hi j' hj'; omega
        · have := hD.below i hi j' hj'; omega
      · rw [a8]; exact hD.below i hi j' hj'
    obtain ⟨t2, ht2, b1, b2, b3, b4, b5, b6, b7, b8, bw, bcw⟩ := ih (j + 1) (by omega) S a1 a2
      (by rw [a7 1 (by simp)]; exact h1) (by rw [a7 11 (by simp)]; exact h11)
      (by rw [a7 12 (by simp)]; exact h12) (by rw [a7 10 (by simp)]; exact h10) a3
      (by rw [a7 29 (by simp)]; exact h29) (by rw [a6 20 (by simp)]; exact h20) hD'
      (fun _ => by simpa using a4)
      (by
        intro j' hj'
        rw [a5]
        rcases Nat.lt_or_ge j' j with h | h
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hc j' h
        · have : j' = j := by omega
          subst this
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega)]; simp
          · simp)
    refine ⟨t1 + t2, ?_, ?_⟩
    · have : (15 * n + 30) * (d + 1) + 1 = (15 * n + 30) + ((15 * n + 30) * d + 1) := by ring
      omega
    rw [run_add, cellsWritten_add, ← hS]
    refine ⟨b1, b2, b3, b4, ?_, ?_, ?_, by rw [b8, a8], by rw [bw, aw]; ring, ?_⟩
    · intro z hz
      rw [b5 z hz, a5, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · intro x hx; rw [b6 x hx, a6 x hx]
    · intro x hx; rw [b7 x hx, a7 x hx]
    · intro c hc'
      rcases Finset.mem_union.1 hc' with h | h
      · have := acw h
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h' | h' <;> subst h' <;> simp <;> omega
      · exact bcw c h

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The loop `B3`: shift every coordinate by `g` (`r14`). -/
lemma box_B3 (Q : Program) (off LKE : ℕ) (hE : Embeds Q (seg6 off LKE) off) (m : ℕ) (HRb : ℤ)
    (g : ℝ) (lo0 hi0 : ℕ → ℝ) :
    ∀ d j, j + d = m → ∀ s : State, s.core.pc = off + 66 → s.halted = false →
      s.core.ptrs 1 = m → s.core.ptrs 22 = j → s.core.ptrs 29 = HRb → s.core.regs 14 = g →
      (∀ j', j ≤ j' → j' < m → s.core.mem (HRb + j') = lo0 j' ∧ s.core.mem (HRb + j' + m) = hi0 j') →
      (run Q s detTape (11 * d + 1)).core.pc = off + 77 ∧
        (run Q s detTape (11 * d + 1)).halted = false ∧
        (∀ j', j ≤ j' → j' < m → (run Q s detTape (11 * d + 1)).core.mem (HRb + j') = lo0 j' - g ∧
          (run Q s detTape (11 * d + 1)).core.mem (HRb + j' + m) = hi0 j' + g) ∧
        (∀ z, (z < HRb + j ∨ (HRb + m ≤ z ∧ z < HRb + j + m) ∨ HRb + 2 * m ≤ z) →
          (run Q s detTape (11 * d + 1)).core.mem z = s.core.mem z) ∧
        (∀ x, x ∉ [15, 16] → (run Q s detTape (11 * d + 1)).core.regs x = s.core.regs x) ∧
        (∀ x, x ∉ [6, 22] → (run Q s detTape (11 * d + 1)).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape (11 * d + 1)).integerMemory = s.integerMemory ∧
        (run Q s detTape (11 * d + 1)).work = s.work + (11 * d + 1) ∧
        (∀ c ∈ cellsWritten Q s (11 * d + 1), c.1 = true ∧ HRb ≤ c.2 ∧ c.2 < HRb + 2 * m) := by
  intro d
  induction d with
  | zero =>
    intro j hj s hpc hh h1 h22 _ _ _
    simp only [Nat.add_zero] at hj; subst hj
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h1 h22; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h1, h22]), run_zero, cw_zero]
    refine ⟨rfl, rfl, fun j' h1 h2 => absurd h2 (by omega), fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, by simp⟩
  | succ d ih =>
    intro j hj s hpc hh h1 h22 h29 h14 hc
    have hjm : j < m := by omega
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h1 h22 h29 h14 hc; subst hpc hh
    obtain ⟨c1, c2⟩ := hc j le_rfl hjm
    set S := run Q ⟨⟨off + 66, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 11 with hS
    have e : S = ⟨⟨off + 66, Function.update (Function.update regs 15 (lo0 j - g)) 16 (hi0 j + g),
        Function.update (Function.update ptrs 6 (HRb + j + m)) 22 (j + 1),
        Function.update (Function.update mem (HRb + j) (lo0 j - g)) (HRb + j + m) (hi0 j + g)⟩,
        im, cur, false, w + 11⟩ ∧
        cellsWritten Q ⟨⟨off + 66, regs, ptrs, mem⟩, im, cur, false, w⟩ 11 ⊆
          {(true, HRb + j), (true, HRb + j + m)} := by
      rw [hS]
      rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
      simp only [exec, coreExec, wcell]
      rw [if_neg (by rw [h1, h22]; push_cast; omega)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
      rw [run_zero, cw_zero]
      have hne : HRb + j + m ≠ HRb + j := by omega
      simp only [h29, h22, h1, h14, c1, Function.update_of_ne hne, Function.update_idem]
      refine ⟨?_, ?_⟩
      · rw [if_neg hne, c2]
      · intro c hc
        simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union,
          Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hc with h | h <;> subst h <;> simp [add_comm, add_assoc]
    obtain ⟨e, ecw⟩ := e
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, bw, bcw⟩ := ih (j + 1) (by omega) S
      (by rw [e]) (by rw [e]) (by rw [e]; simp [h1]) (by rw [e]; simp)
      (by rw [e]; simp [h29]) (by rw [e]; simp [h14])
      (by
        intro j' hj1 hj2
        rw [e]; simp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hc j' (by omega) hj2)
    rw [show 11 * (d + 1) + 1 = 11 + (11 * d + 1) by ring, run_add, cellsWritten_add, ← hS]
    refine ⟨b1, b2, ?_, ?_, ?_, ?_, by rw [b7, e], by rw [bw, e]; ring, ?_⟩
    · intro j' hj1 hj2
      rcases Nat.lt_or_ge j j' with h | h
      · exact b3 j' (by omega) hj2
      · have : j' = j := by omega
        subst this
        rw [b4 _ (Or.inl (by push_cast; omega)), b4 _ (Or.inr (Or.inl ⟨by omega, by push_cast; omega⟩)),
          e]
        simp only
        rw [Function.update_of_ne (by omega)]
        simp
    · intro z hz
      rw [b4 z (by push_cast at hz ⊢; omega), e]
      simp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · intro x hx; rw [b5 x hx, e]; simp only
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [Function.update_apply, hx.1, hx.2]
    · intro x hx; rw [b6 x hx, e]; simp only
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [Function.update_apply, hx.1, hx.2]
    · intro c hc'
      rcases Finset.mem_union.1 hc' with h | h
      · have := ecw h
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h' | h' <;> subst h' <;> simp <;> omega
      · exact bcw c h

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

lemma rmin_coord {n m : ℕ} (hn : 0 < n) (pts : Fin n → Fin m → ℝ) (P : ℕ → ℕ → ℝ)
    (hP : ∀ (i : Fin n) (j : Fin m), P i j = pts i j) (j : Fin m) :
    rmin (coordFn P j) (n - 1) = Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j) :=
  rmin_fin hn _ _ (fun i => hP i j)

lemma rmax_coord {n m : ℕ} (hn : 0 < n) (pts : Fin n → Fin m → ℝ) (P : ℕ → ℕ → ℝ)
    (hP : ∀ (i : Fin n) (j : Fin m), P i j = pts i j) (j : Fin m) :
    rmax (coordFn P j) (n - 1) = Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j) :=
  rmax_fin hn _ _ (fun i => hP i j)

lemma sigma_root {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (pts : Fin n → Fin m → ℝ) (P : ℕ → ℕ → ℝ)
    (hP : ∀ (i : Fin n) (j : Fin m), P i j = pts i j) :
    sigma (fun j => Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j))
      (fun j => Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j)) =
      rmax (sideFn P n) (m - 1) :=
  sigma_eq_rmax hm _ _ _ (fun j => by
    simp only [sideFn]; rw [rmax_coord hn pts P hP j, rmin_coord hn pts P hP j])

/-- **The root box** (`LK` with `i < M`, up to the build call `off + 82`). -/
lemma rootbox (Q : Program) (off LKE : ℕ) (hE : Embeds Q (seg6 off LKE) off) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (pts : Fin n → Fin m → ℝ) (P : ℕ → ℕ → ℝ)
    (hP : ∀ (i : Fin n) (j : Fin m), P i j = pts i j) (PA Sa HRb : ℤ) (s : State)
    (hpc : s.core.pc = off + 22) (hh : s.halted = false) (hlt : s.core.ptrs 3 < s.core.ptrs 4)
    (h1 : s.core.ptrs 1 = m) (h11 : s.core.ptrs 11 = n) (h12 : s.core.ptrs 12 = PA)
    (h10 : s.core.ptrs 10 = Sa) (h16 : s.core.ptrs 16 = HRb) (h20 : s.core.regs 20 = 0)
    (h22 : s.core.regs 22 = 4) (hD : BoxData n m P PA Sa HRb s) :
    ∃ t, t ≤ (15 * n + 30) * m + 11 * m + 13 ∧
      (run Q s detTape t).core.pc = off + 82 ∧ (run Q s detTape t).halted = false ∧
      (∀ j : Fin m, (run Q s detTape t).core.mem (HRb + j) = rootLo hn pts (s.core.regs 4) j ∧
        (run Q s detTape t).core.mem (HRb + m + j) = rootHi hn pts (s.core.regs 4) j) ∧
      (∀ z, (z < HRb ∨ HRb + 2 * m ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).core.ptrs 16 = HRb + 2 * m ∧ (run Q s detTape t).core.ptrs 17 = HRb ∧
      (run Q s detTape t).core.ptrs 29 = HRb ∧
      (run Q s detTape t).core.regs 11 = s.core.regs 4 ∧
      (run Q s detTape t).core.regs 12 = s.core.regs 1 ∧
      (∀ x, x ∉ [5, 6, 11, 12, 13, 14, 15, 16, 17] → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (∀ x, x ∉ [6, 16, 17, 22, 27, 29, 31] → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t ∧
      (∀ c ∈ cellsWritten Q s t, c.1 = true ∧ HRb ≤ c.2 ∧ c.2 < HRb + 2 * m) := by
  -- steps 22–24
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt0, w⟩ := s
  simp only at hpc hh hlt h1 h11 h12 h10 h16 h20 h22; subst hpc hh
  set S0 := run Q ⟨⟨off + 22, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 3 with hS0
  have e0 : S0 = ⟨⟨off + 25, regs, Function.update (Function.update ptrs 29 (ptrs 16)) 22 0, mem⟩,
      im, cur, false, w + 3⟩ ∧ cellsWritten Q ⟨⟨off + 22, regs, ptrs, mem⟩, im, cur, false, w⟩ 3 = ∅ := by
    rw [hS0, run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_neg (by omega)]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]; exact ⟨rfl, by simp⟩
  obtain ⟨e0, cw0⟩ := e0
  obtain ⟨t1, ht1, a1, a2, a3, a4, a5, a6, a7, a8, aw, acw⟩ :=
    box_B1 Q off LKE hE n m hn P PA Sa HRb m 0 (by omega) S0 (by rw [e0]) (by rw [e0])
      (by rw [e0]; simp [h1]) (by rw [e0]; simp [h11]) (by rw [e0]; simp [h12])
      (by rw [e0]; simp [h10]) (by rw [e0]; simp) (by rw [e0]; simp [h16]) (by rw [e0]; simp [h20])
      (by rw [e0]; exact ⟨hD.pts, hD.below⟩) (fun h => absurd h (by omega)) (fun _ h => absurd h (by omega))
  generalize hS1 : run Q S0 detTape t1 = S1 at a1 a2 a3 a4 a5 a6 a7 a8 aw acw
  rw [e0] at a5 a6 a7 a8 aw
  obtain ⟨⟨pc1, regs1, ptrs1, mem1⟩, im1, cur1, hlt1, w1⟩ := S1
  simp only at a1 a2 a3 a4 a5 a6 a7 a8 aw; subst a1 a2; subst im1
  have r22' : regs1 22 = 4 := by rw [a6 22 (by simp)]; exact h22
  have r4' : regs1 4 = regs 4 := a6 4 (by simp)
  have r20' : regs1 20 = 0 := by rw [a6 20 (by simp)]; exact h20
  have r1' : regs1 1 = regs 1 := a6 1 (by simp)
  have p1' : ptrs1 1 = m := by rw [a7 1 (by simp)]; simp [h1]
  have p29' : ptrs1 29 = HRb := by rw [a7 29 (by simp)]; simp [h16]
  have p16' : ptrs1 16 = HRb := by rw [a7 16 (by simp)]; simp [h16]
  set g := regs1 13 + 4 * regs 4 with hg
  -- steps 63–65
  set S2 := run Q ⟨⟨off + 63, regs1, ptrs1, mem1⟩, im, cur1, false, w1⟩ detTape 3 with hS2
  have e2 : S2 = ⟨⟨off + 66, Function.update (Function.update regs1 14 (4 * regs 4)) 14 g,
      Function.update ptrs1 22 0, mem1⟩, im, cur1, false, w1 + 3⟩ ∧
      cellsWritten Q ⟨⟨off + 63, regs1, ptrs1, mem1⟩, im, cur1, false, w1⟩ 3 = ∅ := by
    rw [hS2]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    refine ⟨?_, by simp⟩
    simp only [r22', r4', hg]
  obtain ⟨e2, cw2⟩ := e2
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, bw, bcw⟩ :=
    box_B3 Q off LKE hE m HRb g (fun j => rmin (coordFn P j) (n - 1)) (fun j => rmax (coordFn P j) (n - 1))
      m 0 (by omega) S2 (by rw [e2]) (by rw [e2]) (by rw [e2]; simp [p1']) (by rw [e2]; simp)
      (by rw [e2]; simp [p29']) (by rw [e2]; simp)
      (fun j' _ hj' => by rw [e2]; exact a4 j' hj')
  generalize hS3 : run Q S2 detTape (11 * m + 1) = S3 at b1 b2 b3 b4 b5 b6 b7 bw bcw
  rw [e2] at b4 b5 b6 b7 bw
  obtain ⟨⟨pc3, regs3, ptrs3, mem3⟩, im3, cur3, hlt3, w3⟩ := S3
  simp only at b1 b2 b3 b4 b5 b6 b7 bw; subst b1 b2; subst im3
  -- steps 77–81
  set S4 := run Q ⟨⟨off + 77, regs3, ptrs3, mem3⟩, im, cur3, false, w3⟩ detTape 5 with hS4
  have e4 : S4 = ⟨⟨off + 82, Function.update (Function.update regs3 11 (regs3 4 + regs3 20)) 12
      (regs3 1 + regs3 20), Function.update (Function.update ptrs3 16 (ptrs3 16 + ptrs3 1 + ptrs3 1))
      17 (ptrs3 29), mem3⟩, im, cur3, false, w3 + 5⟩ ∧
      cellsWritten Q ⟨⟨off + 77, regs3, ptrs3, mem3⟩, im, cur3, false, w3⟩ 5 = ∅ := by
    rw [hS4]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    exact ⟨by simp only [Function.update_idem], by simp⟩
  obtain ⟨e4, cw4⟩ := e4
  have q4 : regs3 4 = regs 4 := by rw [b5 4 (by simp)]; simp [r4']
  have q20 : regs3 20 = 0 := by rw [b5 20 (by simp)]; simp [r20']
  have q1 : regs3 1 = regs 1 := by rw [b5 1 (by simp)]; simp [r1']
  have q16 : ptrs3 16 = HRb := by rw [b6 16 (by simp)]; simp [p16']
  have q1p : ptrs3 1 = m := by rw [b6 1 (by simp)]; simp [p1']
  have q29 : ptrs3 29 = HRb := by rw [b6 29 (by simp)]; simp [p29']
  have hσ : regs1 13 = sigma (fun j => Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j))
      (fun j => Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j)) := by
    rw [a3 (by omega), sigma_root hn hm pts P hP]
  generalize hu : 11 * m + 1 = u at hS3 bcw
  have hbu : 3 + t1 + 3 + u + 5 ≤ (15 * n + 30) * m + 11 * m + 13 := by
    rw [← hu]; have := ht1; nlinarith
  refine ⟨3 + t1 + 3 + u + 5, hbu, ?_⟩
  simp only [run_add, cellsWritten_add]
  rw [← hS0, hS1, ← hS2, hS3, ← hS4, e4, cw0, cw2, cw4]
  simp only [Finset.empty_union, Finset.union_empty]
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_, ?_⟩
  · intro j
    obtain ⟨c1, c2⟩ := b3 j (Nat.zero_le _) j.isLt
    refine ⟨?_, ?_⟩
    · rw [c1]; unfold rootLo; rw [rmin_coord hn pts P hP j, hg, hσ]
    · rw [show HRb + (m : ℤ) + ((j : ℕ) : ℤ) = HRb + ((j : ℕ) : ℤ) + m by ring, c2]
      unfold rootHi; rw [rmax_coord hn pts P hP j, hg, hσ]
  · intro z hz
    rw [b4 z (by push_cast; omega), a5 z hz]
  · simp [q16, q1p]; ring
  · simp [q29]
  · simp [q29]
  · simp [q4, q20]
  · simp [q1, q20]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Function.update_apply, hx.2.2.1, hx.2.2.2.1, if_false]
    rw [b5 x (by simp [hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.1])]
    simp only [Function.update_apply, hx.2.2.2.2.2.1, if_false]
    exact a6 x (by simp [hx.1, hx.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.1,
      hx.2.2.2.2.2.2.2.2])
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Function.update_apply, hx.2.1, hx.2.2.1, if_false]
    rw [b6 x (by simp [hx.1, hx.2.2.2.1])]
    simp only [Function.update_apply, hx.2.2.2.1, if_false]
    rw [a7 x (by simp [hx.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.2])]
    simp [Function.update_apply, hx.2.2.2.1, hx.2.2.2.2.2.1]
  · rw [bw, aw, hu]; ring
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    · exact acw c h
    · have := bcw c h; push_cast at this ⊢; omega

end DetANN.HPIM.PP

-- ===== PP_Tail =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The loop tail: write the root test node `w = H` (6 cells), `Z[i] = w`, `H += 6`, restore the
scratch tops, `ρ := ρ e`, `i := i + 1`, back to `LK`. -/
lemma seg10_tail (Q : Program) (off LK : ℕ) (hE : Embeds Q (seg10 off LK) off) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) (H Zarr : ℤ) (hH : s.core.ptrs 15 = H)
    (hZ : s.core.ptrs 18 = Zarr) (hdis : Zarr + s.core.ptrs 3 < H) :
    (run Q s detTape 25).core.pc = LK ∧ (run Q s detTape 25).halted = false ∧
      (run Q s detTape 25).integerMemory =
        Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update s.integerMemory H 1) (H + 1) (s.core.ptrs 29)) (H + 2)
          (s.core.ptrs 17)) (H + 3) (H + 4)) (H + 4) 0) (H + 5) 0) (Zarr + s.core.ptrs 3) H ∧
      (run Q s detTape 25).core.ptrs 15 = H + 6 ∧
      (run Q s detTape 25).core.ptrs 13 = s.core.ptrs 20 ∧
      (run Q s detTape 25).core.ptrs 14 = s.core.ptrs 28 ∧
      (run Q s detTape 25).core.ptrs 3 = s.core.ptrs 3 + 1 ∧
      (∀ x, x ∉ [0, 3, 6, 7, 13, 14, 15, 27] → (run Q s detTape 25).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 25).core.regs 4 = s.core.regs 4 * s.core.regs 1 ∧
      (∀ x, x ≠ 4 → (run Q s detTape 25).core.regs x = s.core.regs x) ∧
      (run Q s detTape 25).core.mem = s.core.mem ∧ (run Q s detTape 25).work = s.work + 25 ∧
      (∀ c ∈ cellsWritten Q s 25, c.1 = false ∧
        ((H ≤ c.2 ∧ c.2 < H + 6) ∨ c.2 = Zarr + s.core.ptrs 3)) := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hH hZ hdis; subst hpc hh hH hZ
  rw [run_exec_at (i := 0) hE rfl (by simp) rfl, cw_exec_at (i := 0) hE rfl (by simp) rfl]
  simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
    if_false]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_pos le_rfl, run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (first | rfl | trivial)
  · simp only [add_assoc, Int.reduceAdd]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp (config := {decide := true}) [Function.update_apply, hx]
  · intro x hx
    simp [Function.update_apply, hx]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    rcases hc with h | h | h | h | h | h | h <;> subst h <;> simp <;> omega

end DetANN.HPIM.PP

-- ===== PP_Env =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- The local points of `S`, as the blocks see them. -/
noncomputable def lpts (S : Finset (Fin N)) : Fin S.card → Fin m → ℝ :=
  fun a j => Y (S.orderEmbOfFin rfl a) j

lemma localPts_of {S : Finset (Fin N)} {v Sa Zn ZRn : ℤ} {s : State}
    (h : NodeEnv Y δ T0 v0 S v Sa Zn ZRn s) : LocalPts s (lpts Y S) := by
  refine ⟨h.g.pm, h.p11, by rw [h.p10]; exact h.sa, by rw [h.g.pPA]; norm_num, fun i => ?_⟩
  have hi := h.slist i
  rw [h.p10, h.g.pPA, hi]
  have hpa := h.g.pa (S.orderEmbOfFin rfl i)
  refine ⟨by positivity, by rw [hpa]; positivity, fun j => ?_⟩
  rw [hpa, h.g.pts]
  rfl

/-- The root-box data: point `i`'s coordinate `j` sits at `1 + g m + j < 1 + N m ≤ HRb`. -/
lemma boxData_of {S : Finset (Fin N)} {v Sa Zn ZRn : ℤ} {s : State}
    (h : NodeEnv Y δ T0 v0 S v Sa Zn ZRn s) (HRb : ℤ) (hHR : 1 + N * m ≤ HRb) :
    BoxData S.card m (fun i j => if hi : i < S.card then if hj : j < m then
        lpts Y S ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) 4 Sa HRb s := by
  refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
  · have hl := (localPts_of Y δ T0 v0 h).2.2.2.2 ⟨i, hi⟩
    rw [h.g.pPA, h.p10] at hl
    simp only [dif_pos hi, dif_pos hj]
    exact hl.2.2 ⟨j, hj⟩
  · have hi' := h.slist ⟨i, hi⟩
    simp only at hi'
    rw [hi', h.g.pa]
    have hg : ((S.orderEmbOfFin rfl ⟨i, hi⟩ : Fin N) : ℕ) < N := Fin.isLt _
    have : ((S.orderEmbOfFin rfl ⟨i, hi⟩ : Fin N) : ℤ) * m + j < N * m := by
      have : ((S.orderEmbOfFin rfl ⟨i, hi⟩ : Fin N) : ℤ) + 1 ≤ N := by exact_mod_cast hg
      nlinarith
    push_cast at this ⊢
    linarith

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

-- ===== PP_LK =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- A stored BSP has nonempty windows. -/
lemma BSPAt.windows {m : ℕ} {s : State} {ilo ihi rlo rhi u : ℤ} {T : BSP m}
    (h : BSPAt m s ilo ihi rlo rhi u T) : ilo < ihi ∧ rlo + 2 * m ≤ rhi := by
  cases h with
  | leaf u lo hi a e1 e2 _ e4 e5 _ _ _ => exact ⟨by omega, by omega⟩
  | cut u lo hi l r e1 e2 _ e4 e5 _ _ _ _ => exact ⟨by omega, by omega⟩

set_option maxHeartbeats 2000000 in
lemma lk_iter (B : Blocks) (hB : B.WF) (ch : ChildOK B) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (S : Finset (Fin N)) (hn : 2 ≤ S.card) (v Sa Zn ZRn Zarr H HR : ℤ) (i M : ℕ) (hiM : i < M)
    (s : State) (hpc : s.core.pc = B.lbl_LK) (hh : s.halted = false)
    (hEnv : NodeEnv Y δ T0 v0 S v Sa Zn ZRn s) (h3 : s.core.ptrs 3 = i) (h4 : s.core.ptrs 4 = M)
    (h18 : s.core.ptrs 18 = Zarr) (h13 : s.core.ptrs 13 = Zn) (h14 : s.core.ptrs 14 = ZRn)
    (h15 : s.core.ptrs 15 = H) (h16 : s.core.ptrs 16 = HR) (hρ : s.core.regs 4 = rhoOf Y δ S i)
    (hρpos : 0 < rhoOf Y δ S i) (hZn : Zn ≤ 0) (hZRn : ZRn ≤ 0) (hHR : 1 + N * m ≤ HR)
    (hZH : Zarr + M ≤ H) (hH0 : 0 ≤ Zarr) (hM : M = MOf Y δ S) (hHb : Hbase N T0 ≤ Sa)
    (hSZ : Sa + S.card ≤ Zarr) :
    ∃ t w, (run (Blocks.prog B) s detTape t).core.pc = B.lbl_LK ∧
      (run (Blocks.prog B) s detTape t).halted = false ∧
      NodeEnv Y δ T0 v0 S v Sa Zn ZRn (run (Blocks.prog B) s detTape t) ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 3 = (i + 1 : ℕ) ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 4 = M ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 18 = Zarr ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 13 = Zn ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 14 = ZRn ∧
      (run (Blocks.prog B) s detTape t).core.regs 4 = rhoOf Y δ S (i + 1) ∧
      H ≤ w ∧ w + 6 ≤ (run (Blocks.prog B) s detTape t).core.ptrs 15 ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 15 ≤ H + ch.Cbal * bspB S.card m δ + 6 ∧
      HR ≤ (run (Blocks.prog B) s detTape t).core.ptrs 16 ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 16 ≤ HR + 2 * m + ch.Cbal * bspB S.card m δ * m ∧
      (run (Blocks.prog B) s detTape t).integerMemory (Zarr + i) = w ∧
      (∀ s'' : State,
        (∀ z, H ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 15 →
          s''.integerMemory z = (run (Blocks.prog B) s detTape t).integerMemory z) →
        (∀ z, HR ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 16 →
          s''.core.mem z = (run (Blocks.prog B) s detTape t).core.mem z) →
        BoxTreeAt m s'' w (ZOf Y δ S ⟨i, hM ▸ hiM⟩)) ∧
      (∀ c ∈ cellsWritten (Blocks.prog B) s t,
        (c.1 = false ∧ ((H ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 15) ∨
          c.2 = Zarr + i ∨ (Zn - (ch.Cb * (m + 1) + ch.Cbal) * bspB S.card m δ ≤ c.2 ∧ c.2 < Zn))) ∨
        (c.1 = true ∧ ((HR ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 16) ∨
          (ZRn - (ch.Cb * (m + 1) + ch.Cbal) * bspB S.card m δ ≤ c.2 ∧ c.2 < ZRn)))) ∧
      (run (Blocks.prog B) s detTape t).work ≤ s.work + ((15 * S.card + 30) * m + 11 * m + 38 +
        ch.Cb * bspB S.card m δ ^ 2 * (S.card + 1) * (m + 1) ^ 2 +
        ch.Cbal * bspB S.card m δ ^ 2 * (m + 1)) ∧
      (∀ x < 40, x ∉ [0, 3, 6, 7, 13, 14, 15, 16, 17, 22, 27, 29, 31] →
        (run (Blocks.prog B) s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (∀ x < 40, x ∉ [4, 5, 6, 11, 12, 13, 14, 15, 16, 17] →
        (run (Blocks.prog B) s detTape t).core.regs x = s.core.regs x) := by
  obtain ⟨hB1, hB2, hB3, hB4⟩ := hB
  set n := S.card with hndef
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := by omega
  set pts := lpts Y S with hpts
  set P : ℕ → ℕ → ℝ := fun i j => if hi : i < n then if hj : j < m then pts ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else 0 with hP
  have hPpts : ∀ (i : Fin n) (j : Fin m), P i j = pts i j := by
    intro i j; simp [hP, i.isLt, j.isLt]
  have g := hEnv.g
  -- Stage A: the root box
  obtain ⟨t1, ht1, a1, a2, a3, a4, a5, a6, a29, a7, a8, a9, a10, a11, aw, acw⟩ :=
    rootbox (Blocks.prog B) B.o6 B.lbl_LKE (emb6 B ⟨hB1, hB2, hB3, hB4⟩) n m hn0 hm0 pts P hPpts 4 Sa HR s
      hpc hh (by rw [h3, h4]; exact_mod_cast hiM) g.pm hEnv.p11 g.pPA hEnv.p10 h16 g.r20 g.r22
      (boxData_of Y δ T0 v0 hEnv HR hHR)
  set S1 := run (Blocks.prog B) s detTape t1 with hS1
  have env1 : NodeEnv Y δ T0 v0 S v Sa Zn ZRn S1 := by
    refine hEnv.transfer Y δ T0 v0 (fun x hx => a10 x (by simp at hx ⊢; omega))
      (fun x hx => a9 x (by simp at hx ⊢; omega)) (fun z _ => by rw [a11])
      (fun z hz hz' => a4 z (Or.inl (by omega)))
  set ρ := rhoOf Y δ S i with hρdef
  set lo := rootLo hn0 pts ρ with hlo
  set hi := rootHi hn0 pts ρ with hhi
  set T := build pts ρ (1 + δ / 4) (bspFuel n m δ) lo hi with hT
  have hbs := build_size hm hn0 pts ρ δ hρpos hδ hδ'
  have hTB : T.paths.card + 1 ≤ bspB n m δ := by
    have h2 : T.paths.card ≤ 2 * bspFuel n m δ := hbs.2
    unfold bspB; omega
  have p13a : S1.core.ptrs 13 = Zn := by rw [a10 13 (by simp)]; exact h13
  have p14a : S1.core.ptrs 14 = ZRn := by rw [a10 14 (by simp)]; exact h14
  -- Stage B: the build block
  obtain ⟨t2, b1, b2, b3, b4, b5, b6, b7, bw⟩ :=
    ch.build B.o7 (Blocks.prog B) (emb7 B ⟨hB1, hB2, hB3, hB4⟩) m n (bspFuel n m δ) pts ρ (1 + δ / 4)
      lo hi S1 hm (by omega) a1 a2 (localPts_of Y δ T0 v0 env1) (by rw [a7, hρ])
      (by rw [a8, g.r1]) (by rw [a6]; linarith [hHR, Nat.zero_le (N * m)])
      (fun j => by rw [a6]; have := (a3 j).1; rw [hρ] at this; exact this)
      (fun j => by rw [a6]; have := (a3 j).2; rw [hρ] at this; exact this)
      (by rw [p13a]; exact hZn) (by rw [p14a]; exact hZRn) hbs.1
  set S2 := run (Blocks.prog B) S1 detTape t2 with hS2
  rw [← hT] at b3 b5 b6 b7 bw
  rw [p13a, p14a] at b3 b7; rw [p13a] at b5; rw [p14a] at b6
  -- Stage C: the balance block
  have hp15 : S2.core.ptrs 15 = H := by
    rw [b4.1 15 (by norm_num) (by simp), a10 15 (by simp)]; exact h15
  have hp16 : S2.core.ptrs 16 = HR + 2 * m := by rw [b4.1 16 (by norm_num) (by simp)]; exact a5
  obtain ⟨t3, c1, c2, c3, c4, c5, c6, c7, c8, c9, cw⟩ :=
    ch.bal B.o9 (Blocks.prog B) (emb9 B ⟨hB1, hB2, hB3, hB4⟩) m T S2 (S2.core.ptrs 13) Zn
      (S2.core.ptrs 14) ZRn hm b1 b2 (by rw [b4.1 1 (by norm_num) (by simp)]; exact env1.g.pm) b3
      hZn hZRn le_rfl le_rfl (by rw [hp15]; omega) (by rw [hp16]; have := Nat.zero_le (N * m); omega)
  set S3 := run (Blocks.prog B) S2 detTape t3 with hS3
  -- frames through B and C
  have kp : ∀ x < 40, x ∉ [6, 13, 14, 15, 16, 17, 22, 27, 29, 31] → S3.core.ptrs x = s.core.ptrs x := by
    intro x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    rw [c4.1 x hx (by simp [hx'.2.2.2.1, hx'.2.2.2.2.1, hx'.2.2.2.2.2.1]),
      b4.1 x hx (by simp [hx'.2.1, hx'.2.2.1, hx'.2.2.2.2.2.1]),
      a10 x (by simp [hx'.1, hx'.2.2.2.2.1, hx'.2.2.2.2.2.1, hx'.2.2.2.2.2.2.1, hx'.2.2.2.2.2.2.2.1,
        hx'.2.2.2.2.2.2.2.2.1, hx'.2.2.2.2.2.2.2.2.2])]
  have kr : ∀ x < 40, x ∉ [5, 6, 11, 12, 13, 14, 15, 16, 17] → S3.core.regs x = s.core.regs x := by
    intro x hx hx'
    rw [c4.2 x hx (by simp), b4.2 x hx (by simp), a9 x hx']
  have q15 : H ≤ S3.core.ptrs 15 := by rw [← hp15]; exact c5
  have q15' : S3.core.ptrs 15 ≤ H + ch.Cbal * bspB n m δ := by
    have h6 := c6; rw [hp15] at h6
    have h7 : ((ch.Cbal * (T.paths.card + 1) : ℕ) : ℤ) ≤ ((ch.Cbal * bspB n m δ : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_left _ hTB
    push_cast at h6 h7 ⊢; linarith
  have q3 : S3.core.ptrs 3 = i := by rw [kp 3 (by norm_num) (by simp)]; exact h3
  have q18 : S3.core.ptrs 18 = Zarr := by rw [kp 18 (by norm_num) (by simp)]; exact h18
  -- Stage D: the tail
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, dw, dcw⟩ :=
    seg10_tail (Blocks.prog B) B.o10 B.lbl_LK (emb10 B ⟨hB1, hB2, hB3, hB4⟩) S3 c1 c2
      (S3.core.ptrs 15) Zarr rfl q18 (by rw [q3]; push_cast; omega)
  set S4 := run (Blocks.prog B) S3 detTape 25 with hS4
  refine ⟨t1 + t2 + t3 + 25, S3.core.ptrs 15, ?_⟩
  have R : run (Blocks.prog B) s detTape (t1 + t2 + t3 + 25) = S4 := by
    rw [run_add, run_add, run_add]
  rw [R]
  -- memory frames
  obtain ⟨bM, bI⟩ := unwritten_of_writesOnly b7
  obtain ⟨cM, cI⟩ := unwritten_of_writesOnly c9
  have hBSPlt : S2.core.ptrs 13 < Zn ∧ S2.core.ptrs 14 < ZRn := by
    obtain ⟨w1, w2⟩ := DetANN.HPIM.PP.BSPAt.windows b3; exact ⟨w1, by have := Nat.zero_le m; omega⟩
  have fIM3 : ∀ z, 0 ≤ z → z < H → S3.integerMemory z = S1.integerMemory z := by
    intro z hz0 hz
    rw [cI z (by
      simp only [Bool.false_eq_true, if_false, not_or, not_and, not_lt]
      refine ⟨fun h => by omega, fun h => by rw [hp15] at h; omega⟩)]
    rw [bI z (by simp only [Bool.false_eq_true, if_false, not_and, not_lt]; intro; omega)]
  have fM3 : ∀ z, 0 ≤ z → z < HR + 2 * m → S3.core.mem z = S1.core.mem z := by
    intro z hz0 hz
    rw [cM z (by
      simp only [if_true, not_or, not_and, not_lt]
      refine ⟨fun h => by omega, fun h => by rw [hp16] at h; omega⟩)]
    rw [bM z (by simp only [if_true, not_and, not_lt]; intro; omega)]
  have fIM4 : ∀ z, z < S3.core.ptrs 15 → z ≠ Zarr + i → S4.integerMemory z = S3.integerMemory z := by
    intro z hz hz'
    rw [d3, q3]
    simp only [Function.update_apply]
    rw [if_neg (by push_cast; exact hz'), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have kp4 : ∀ x < 40, x ∉ [0, 3, 6, 7, 13, 14, 15, 16, 17, 22, 27, 29, 31] →
      S4.core.ptrs x = s.core.ptrs x := by
    intro x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    rw [d8 x (by simp [hx'.1, hx'.2.1, hx'.2.2.1, hx'.2.2.2.1, hx'.2.2.2.2.1, hx'.2.2.2.2.2.1,
      hx'.2.2.2.2.2.2.1, hx'.2.2.2.2.2.2.2.2.2.2.1]),
      kp x hx (by simp [hx'.2.2.1, hx'.2.2.2.2.1, hx'.2.2.2.2.2.1, hx'.2.2.2.2.2.2.1,
        hx'.2.2.2.2.2.2.2.1, hx'.2.2.2.2.2.2.2.2.1, hx'.2.2.2.2.2.2.2.2.2.1,
        hx'.2.2.2.2.2.2.2.2.2.2.1, hx'.2.2.2.2.2.2.2.2.2.2.2.1, hx'.2.2.2.2.2.2.2.2.2.2.2.2])]
  have kr4 : ∀ x < 40, x ∉ [4, 5, 6, 11, 12, 13, 14, 15, 16, 17] → S4.core.regs x = s.core.regs x := by
    intro x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    rw [d10 x hx'.1, kr x hx (by simp [hx'.2.1, hx'.2.2.1, hx'.2.2.2.1, hx'.2.2.2.2.1,
      hx'.2.2.2.2.2.1, hx'.2.2.2.2.2.2.1, hx'.2.2.2.2.2.2.2.1, hx'.2.2.2.2.2.2.2.2.1,
      hx'.2.2.2.2.2.2.2.2.2])]
  have env4 : NodeEnv Y δ T0 v0 S v Sa Zn ZRn S4 := by
    refine hEnv.transfer Y δ T0 v0 (fun x hx => kp4 x ?_ ?_) (fun x hx => kr4 x ?_ ?_) ?_ ?_
    · simp at hx; omega
    · simp at hx ⊢; omega
    · simp at hx; omega
    · simp at hx ⊢; omega
    · intro z hz
      have hzZ : 0 ≤ z ∧ z < Zarr := by unfold Hbase at hz hHb; omega
      rw [fIM4 z (by omega) (by omega), fIM3 z hzZ.1 (by omega), a11]
    · intro z hz0 hz
      rw [d11, fM3 z hz0 (by have := Nat.zero_le (N * m); push_cast at hz ⊢; omega)]
      exact a4 z (Or.inl (by push_cast at hz ⊢; omega))
  refine ⟨d1, d2, env4, ?_, ?_, ?_, ?_, ?_, ?_, q15, by rw [d4], by rw [d4]; push_cast; omega, ?_, ?_,
    ?_, ?_, ?_, ?_, kp4, kr4⟩
  · rw [d7, q3]; push_cast; ring
  · rw [kp4 4 (by norm_num) (by simp)]; exact h4
  · rw [kp4 18 (by norm_num) (by simp)]; exact h18
  · rw [d5, kp 20 (by norm_num) (by simp)]; exact hEnv.p20
  · rw [d6, kp 28 (by norm_num) (by simp)]; exact hEnv.p28
  · rw [d9, kr 4 (by norm_num) (by simp), kr 1 (by norm_num) (by simp), hρ, g.r1, rhoOf_succ]
  · rw [d8 16 (by simp)]; have := c7; rw [hp16] at this; omega
  · rw [d8 16 (by simp)]
    have h8 := c8; rw [hp16] at h8
    have h9 : ((ch.Cbal * (T.paths.card + 1) * m : ℕ) : ℤ) ≤ ((ch.Cbal * bspB n m δ * m : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hTB)
    push_cast at h8 h9 ⊢; linarith
  · rw [d3, q3, Function.update_self]
  · intro s'' hI hM'
    set w := S3.core.ptrs 15 with hw
    have hZw : Zarr + (i : ℤ) < w := by omega
    have im4 : ∀ k : ℕ, k < 6 → S4.integerMemory (w + k) =
        [1, S3.core.ptrs 29, S3.core.ptrs 17, w + 4, 0, 0].getD k 0 := by
      intro k hk
      rw [d3, q3]
      interval_cases k <;> simp [Function.update_apply] <;> omega
    have hI' : ∀ k : ℕ, k < 6 → s''.integerMemory (w + k) = S4.integerMemory (w + k) :=
      fun k hk => hI _ (by omega) (by rw [d4]; push_cast; omega)
    have p29' : S3.core.ptrs 29 = HR := by
      have e1 := c4.1 29 (by norm_num) (by simp)
      have e2 := b4.1 29 (by norm_num) (by simp)
      rw [e1, e2]; exact a29
    have i0 := hI' 0 (by norm_num); rw [im4 0 (by norm_num)] at i0
    have i1 := hI' 1 (by norm_num); rw [im4 1 (by norm_num)] at i1
    have i2 := hI' 2 (by norm_num); rw [im4 2 (by norm_num)] at i2
    have i3 := hI' 3 (by norm_num); rw [im4 3 (by norm_num)] at i3
    have i4 := hI' 4 (by norm_num); rw [im4 4 (by norm_num)] at i4
    have i5 := hI' 5 (by norm_num); rw [im4 5 (by norm_num)] at i5
    simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat, List.getD_cons_zero,
      List.getD_cons_succ] at i0 i1 i2 i3 i4 i5
    have hp16' : HR + 2 * m ≤ S4.core.ptrs 16 := by rw [d8 16 (by simp)]; have := c7; omega
    unfold ZOf lookupTree
    rw [dif_pos hn0]
    refine BoxTreeAt.test w _ _ _ _ i0 (by rw [i1, p29']; have := Nat.zero_le (N * m); omega)
      (fun j => ?_) (fun j => ?_) ?_ ?_
    · have hj := j.isLt
      have hNm : (0 : ℤ) ≤ N * m := by positivity
      rw [i1, p29', hM' _ (by omega) (by omega), d11, fM3 _ (by omega) (by omega)]
      exact (a3 j).1.trans (by rw [hρ]; rfl)
    · have hj := j.isLt
      have hNm : (0 : ℤ) ≤ N * m := by positivity
      rw [i1, p29', hM' _ (by omega) (by omega), d11, fM3 _ (by omega) (by omega)]
      exact (a3 j).2.trans (by rw [hρ]; rfl)
    · rw [i2]
      apply c3 s''
      · intro z hz1 hz2
        rw [hp15] at hz1
        rw [hI z hz1 (by rw [d4]; omega), fIM4 z hz2 (by omega)]
      · intro z hz1 hz2
        rw [hM' z (by rw [hp16] at hz1; omega) (by rw [d8 16 (by simp)]; exact hz2), d11]
    · rw [i3]
      exact BoxTreeAt.leaf _ none (by rw [← i4]) (by rw [show w + 4 + 1 = w + 5 by ring]; exact i5)
  · have kA : ch.Cb * (T.paths.card + 1) * (m + 1) + ch.Cbal * (T.paths.card + 1) ≤
        (ch.Cb * (m + 1) + ch.Cbal) * bspB n m δ := by
      have h1 := Nat.mul_le_mul_left (ch.Cb * (m + 1) + ch.Cbal) hTB
      have h2 : ch.Cb * (T.paths.card + 1) * (m + 1) + ch.Cbal * (T.paths.card + 1) =
          (ch.Cb * (m + 1) + ch.Cbal) * (T.paths.card + 1) := by ring
      rw [h2]; exact h1
    have kA' : ((ch.Cb * (T.paths.card + 1) * (m + 1) + ch.Cbal * (T.paths.card + 1) : ℕ) : ℤ) ≤
        (((ch.Cb * (m + 1) + ch.Cbal) * bspB n m δ : ℕ) : ℤ) := by exact_mod_cast kA
    push_cast at kA'
    have hb5 := b5
    have hb6 := b6
    have hp16' : HR + 2 * m ≤ S4.core.ptrs 16 := by rw [d8 16 (by simp)]; have := c7; omega
    have hd4 : S4.core.ptrs 15 = S3.core.ptrs 15 + 6 := d4
    intro c hc
    rw [show t1 + t2 + t3 + 25 = t1 + t2 + t3 + 25 from rfl, cellsWritten_add, cellsWritten_add,
      cellsWritten_add, run_add, run_add, run_add, ← hS1, ← hS2, ← hS3] at hc
    simp only [Finset.mem_union] at hc
    rcases hc with ((h | h) | h) | h
    · obtain ⟨e1, e2, e3⟩ := acw c h
      right; exact ⟨e1, Or.inl ⟨e2, by omega⟩⟩
    · have := b7 c h
      rcases c with ⟨b, z⟩
      cases b
      · left; refine ⟨rfl, Or.inr (Or.inr ⟨?_, this.2⟩)⟩
        have h1 := this.1; simp only [Bool.false_eq_true, if_false] at h1
        have h0 : (0 : ℤ) ≤ ch.Cbal * ((T.paths.card : ℤ) + 1) :=
          mul_nonneg (Int.natCast_nonneg _) (by have := Int.natCast_nonneg T.paths.card; linarith only [this])
        linarith only [h1, kA', h0]
      · right; refine ⟨rfl, Or.inr ⟨?_, this.2⟩⟩
        have h1 := this.1; simp only [if_true] at h1
        have h0 : (0 : ℤ) ≤ ch.Cbal * ((T.paths.card : ℤ) + 1) :=
          mul_nonneg (Int.natCast_nonneg _) (by have := Int.natCast_nonneg T.paths.card; linarith only [this])
        linarith only [h1, kA', h0]
    · have := c9 c h
      rcases c with ⟨b, z⟩
      cases b
      · simp only [Bool.false_eq_true, if_false] at this
        left; refine ⟨rfl, ?_⟩
        rcases this with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inr (Or.inr ⟨by linarith only [e1, hb5, kA'], by linarith only [e2, hBSPlt.1]⟩)
        · rw [hp15] at e1; exact Or.inl ⟨e1, by omega⟩
      · simp only [if_true] at this
        right; refine ⟨rfl, ?_⟩
        rcases this with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inr ⟨by linarith only [e1, hb6, kA'], by linarith only [e2, hBSPlt.2]⟩
        · rw [hp16] at e1; exact Or.inl ⟨by omega, by rw [d8 16 (by simp)]; exact e2⟩
    · obtain ⟨e1, e2⟩ := dcw c h
      left; refine ⟨e1, ?_⟩
      rcases e2 with ⟨f1, f2⟩ | f
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr (Or.inl (by rw [f, q3]))
  · have hT2 : (T.paths.card + 1) ^ 2 ≤ bspB n m δ ^ 2 := Nat.pow_le_pow_left hTB 2
    have e1 : ch.Cb * (T.paths.card + 1) ^ 2 * (n + 1) * (m + 1) ^ 2 ≤
        ch.Cb * bspB n m δ ^ 2 * (n + 1) * (m + 1) ^ 2 := by gcongr
    have e2 : ch.Cbal * (T.paths.card + 1) ^ 2 * (m + 1) ≤ ch.Cbal * bspB n m δ ^ 2 * (m + 1) := by
      gcongr
    have hdw : S4.work = S3.work + 25 := dw
    rw [hdw]
    have hc := cw; have hb := bw
    have ha : S1.work = s.work + t1 := aw
    linarith only [hc, hb, ha, ht1, e1, e2]

end DetANN.HPIM.PP

-- ===== PP_LKLoop =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

set_option maxHeartbeats 1000000 in
lemma lk_loop (B : Blocks) (hB : B.WF) (ch : ChildOK B) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (S : Finset (Fin N)) (hn : 2 ≤ S.card) (v Sa Zn ZRn Zarr Hl0 HR0 : ℤ) (M : ℕ)
    (hM : M = MOf Y δ S) (hρpos : ∀ k, 0 < rhoOf Y δ S k) (hZn : Zn ≤ 0) (hZRn : ZRn ≤ 0)
    (hHR : 1 + N * m ≤ HR0) (hZH : Zarr + M ≤ Hl0) (hH0 : 0 ≤ Zarr) (hHb : Hbase N T0 ≤ Sa)
    (hSZ : Sa + S.card ≤ Zarr) :
    ∀ d i, (hid : i + d = M) → ∀ s : State, s.core.pc = B.lbl_LK → s.halted = false →
      NodeEnv Y δ T0 v0 S v Sa Zn ZRn s → s.core.ptrs 3 = i → s.core.ptrs 4 = M →
      s.core.ptrs 18 = Zarr → s.core.ptrs 13 = Zn → s.core.ptrs 14 = ZRn →
      s.core.regs 4 = rhoOf Y δ S i →
      Hl0 ≤ s.core.ptrs 15 → HR0 ≤ s.core.ptrs 16 →
      (∀ i' (hi' : i' < i), ∀ s'' : State,
        (∀ z, Hl0 ≤ z → z < s.core.ptrs 15 → s''.integerMemory z = s.integerMemory z) →
        (∀ z, HR0 ≤ z → z < s.core.ptrs 16 → s''.core.mem z = s.core.mem z) →
        BoxTreeAt m s'' (s.integerMemory (Zarr + i')) (ZOf Y δ S ⟨i', hM ▸ (by omega)⟩)) →
      ∃ t, (run (Blocks.prog B) s detTape t).core.pc = B.o11 ∧
        (run (Blocks.prog B) s detTape t).halted = false ∧
        NodeEnv Y δ T0 v0 S v Sa Zn ZRn (run (Blocks.prog B) s detTape t) ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 13 = Zn ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 14 = ZRn ∧
        (∀ x < 40, x ∉ [0, 3, 6, 7, 13, 14, 15, 16, 17, 22, 27, 29, 31] →
          (run (Blocks.prog B) s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x < 40, x ∉ [4, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17] →
          (run (Blocks.prog B) s detTape t).core.regs x = s.core.regs x) ∧
        (run (Blocks.prog B) s detTape t).core.regs 10 = s.core.regs 21 * s.core.regs 3 ∧
        s.core.ptrs 15 ≤ (run (Blocks.prog B) s detTape t).core.ptrs 15 ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 15 ≤ s.core.ptrs 15 + d * lkH ch S.card m δ ∧
        s.core.ptrs 16 ≤ (run (Blocks.prog B) s detTape t).core.ptrs 16 ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 16 ≤ s.core.ptrs 16 + d * lkR ch S.card m δ ∧
        (∀ i' (hi' : i' < M), ∀ s'' : State,
          (∀ z, Hl0 ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 15 →
            s''.integerMemory z = (run (Blocks.prog B) s detTape t).integerMemory z) →
          (∀ z, HR0 ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 16 →
            s''.core.mem z = (run (Blocks.prog B) s detTape t).core.mem z) →
          BoxTreeAt m s'' ((run (Blocks.prog B) s detTape t).integerMemory (Zarr + i'))
            (ZOf Y δ S ⟨i', hM ▸ hi'⟩)) ∧
        (∀ z, z < Zarr ∨ (Zarr + M ≤ z ∧ z < s.core.ptrs 15) →
          0 ≤ z → (run (Blocks.prog B) s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ z, 0 ≤ z → z < s.core.ptrs 16 → (run (Blocks.prog B) s detTape t).core.mem z = s.core.mem z) ∧
        (∀ c ∈ cellsWritten (Blocks.prog B) s t,
          (c.1 = false ∧ ((s.core.ptrs 15 ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 15) ∨
            (Zarr ≤ c.2 ∧ c.2 < Zarr + M) ∨ (Zn - lkD ch S.card m δ ≤ c.2 ∧ c.2 < Zn))) ∨
          (c.1 = true ∧ ((s.core.ptrs 16 ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 16) ∨
            (ZRn - lkD ch S.card m δ ≤ c.2 ∧ c.2 < ZRn)))) ∧
        (run (Blocks.prog B) s detTape t).work ≤ s.work + d * lkW ch S.card m δ + 2 := by
  have hE6 := emb6 B hB
  have hE10 := emb10 B hB
  intro d
  induction d with
  | zero =>
    intro i hid s hpc hh hEnv h3 h4 h18 h13 h14 h4r hH hR hZ
    simp only [Nat.add_zero] at hid; subst hid
    refine ⟨2, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h3 h4 h18 h13 h14 h4r hH hR hZ; subst hpc hh
    have c0 : cellsWritten (Blocks.prog B) ⟨⟨B.lbl_LK, regs, ptrs, mem⟩, im, cur, false, w⟩ 2 = ∅ := by
      rw [cw_exec_at (i := 22) hE6 rfl rfl rfl]
      simp only [exec, coreExec, wcell]
      rw [if_pos (by rw [h3, h4])]
      rw [cw_exec_at (i := 25) hE10 rfl rfl rfl]
      simp [wcell, cw_zero]
    have r0 : run (Blocks.prog B) ⟨⟨B.lbl_LK, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 2 =
        ⟨⟨B.o11, Function.update regs 10 (regs 21 * regs 3), ptrs, mem⟩, im, cur, false, w + 2⟩ := by
      rw [run_exec_at (i := 22) hE6 rfl rfl rfl]
      simp only [exec, coreExec]
      rw [if_pos (by rw [h3, h4])]
      rw [run_exec_at (i := 25) hE10 rfl rfl rfl]
      simp only [exec, coreExec, run_zero]
      rfl
    rw [r0, c0]
    have env' := hEnv.transfer Y δ T0 v0 (s' := ⟨⟨B.o11, Function.update regs 10 (regs 21 * regs 3),
      ptrs, mem⟩, im, cur, false, w + 2⟩) (fun _ _ => rfl)
      (fun x hx => by simp at hx; simp [Function.update_apply]; omega) (fun _ _ => rfl) (fun _ _ _ => rfl)
    refine ⟨rfl, rfl, env', h13, h14, fun _ _ _ => rfl, fun x _ hx => ?_, by simp, le_rfl, by simp,
      le_rfl, by simp, ?_, fun _ _ _ => rfl, fun _ _ _ => rfl, by simp, by simp⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [Function.update_apply, hx.2.2.2.1]
    · intro i' hi' s'' hI hM'
      exact hZ i' hi' s'' hI hM'
  | succ d ih =>
    intro i hid s hpc hh hEnv h3 h4 h18 h13 h14 h4r hH hR hZ
    have hiM : i < M := by omega
    have hNm : (0 : ℤ) ≤ N * m := by positivity
    obtain ⟨t1, w, a1, a2, a3, a4, a5, a6, a7, a8, a9, aw0, aw6, a15, a16l, a16u, aZ, aS, acw, awk, akp, akr⟩ :=
      lk_iter Y δ T0 v0 B hB ch hm hδ hδ' S hn v Sa Zn ZRn Zarr (s.core.ptrs 15) (s.core.ptrs 16) i M
        hiM s hpc hh hEnv h3 h4 h18 h13 h14 rfl rfl h4r (hρpos i) hZn hZRn (by linarith)
        (by linarith) hH0 hM hHb hSZ
    set S1 := run (Blocks.prog B) s detTape t1 with hS1
    have fI : ∀ z, 0 ≤ z → z < s.core.ptrs 15 → z ≠ Zarr + i →
        S1.integerMemory z = s.integerMemory z := by
      intro z hz0 hz hz'
      apply run_im_unwritten
      intro hc
      rcases acw _ hc with ⟨_, h | h | h⟩ | ⟨h, _⟩
      · omega
      · exact hz' h
      · have : (0 : ℤ) ≤ lkD ch S.card m δ := by positivity
        unfold lkD at this; omega
      · simp at h
    have fM : ∀ z, 0 ≤ z → z < s.core.ptrs 16 → S1.core.mem z = s.core.mem z := by
      intro z hz0 hz
      apply run_mem_unwritten
      intro hc
      rcases acw _ hc with ⟨h, _⟩ | ⟨_, h | h⟩
      · simp at h
      · omega
      · omega
    obtain ⟨t2, b1, b2, b3, b4, b5, b6, b7, b8, b15l, b15u, b16l, b16u, bZ, bI, bM, bcw, bwk⟩ :=
      ih (i + 1) (by omega) S1 a1 a2 a3 a4 a5 a6 a7 a8 a9 (by omega) (by omega) (by
        intro i' hi' s'' hI hM'
        rcases Nat.lt_or_ge i' i with h | h
        · rw [fI _ (by omega) (by omega) (by omega)]
          exact hZ i' h s'' (fun z hz1 hz2 => by rw [hI z hz1 (by omega), fI z (by omega) hz2 (by omega)])
            (fun z hz1 hz2 => by rw [hM' z hz1 (by omega), fM z (by omega) hz2])
        · have : i' = i := by omega
          subst this
          rw [aZ]
          exact aS s'' (fun z hz1 hz2 => hI z (by omega) hz2) (fun z hz1 hz2 => hM' z (by omega) hz2))
    refine ⟨t1 + t2, ?_⟩
    rw [run_add, cellsWritten_add, ← hS1]
    have hlkH : (lkH ch S.card m δ : ℤ) = ch.Cbal * bspB S.card m δ + 6 := by unfold lkH; push_cast; ring
    have hlkR : (lkR ch S.card m δ : ℤ) = 2 * m + ch.Cbal * bspB S.card m δ * m := by
      unfold lkR; push_cast; ring
    refine ⟨b1, b2, b3, b4, b5, fun x hx hx' => by rw [b6 x hx hx', akp x hx hx'],
      fun x hx hx' => ?_, ?_, by omega, ?_, by omega, ?_, bZ, fun z hz hz0 => ?_, fun z hz0 hz => ?_,
      ?_, ?_⟩
    · rw [b7 x hx hx', akr x hx (by simp at hx' ⊢; omega)]
    · rw [b8, akr 21 (by norm_num) (by simp), akr 3 (by norm_num) (by simp)]
    · push_cast; linarith only [b15u, a15, hlkH]
    · push_cast; linarith only [b16u, a16u, hlkR]
    · rw [bI z (by omega) hz0, fI z hz0 (by omega) (by omega)]
    · rw [bM z hz0 (by omega), fM z hz0 hz]
    · intro c hc
      rcases Finset.mem_union.1 hc with h | h
      · rcases acw c h with ⟨e1, f | f | f⟩ | ⟨e1, f | f⟩
        · exact Or.inl ⟨e1, Or.inl ⟨f.1, by omega⟩⟩
        · exact Or.inl ⟨e1, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
        · exact Or.inl ⟨e1, Or.inr (Or.inr (by unfold lkD; push_cast; exact f))⟩
        · exact Or.inr ⟨e1, Or.inl ⟨f.1, by omega⟩⟩
        · exact Or.inr ⟨e1, Or.inr (by unfold lkD; push_cast; exact f)⟩
      · rcases bcw c h with ⟨e1, f | f | f⟩ | ⟨e1, f | f⟩
        · exact Or.inl ⟨e1, Or.inl ⟨by omega, f.2⟩⟩
        · exact Or.inl ⟨e1, Or.inr (Or.inl f)⟩
        · exact Or.inl ⟨e1, Or.inr (Or.inr f)⟩
        · exact Or.inr ⟨e1, Or.inl ⟨by omega, f.2⟩⟩
        · exact Or.inr ⟨e1, Or.inr f⟩
    · have : (s.core.ptrs 15 : ℤ) = s.core.ptrs 15 := rfl
      unfold lkW at bwk ⊢
      have hS1w : S1.work ≤ s.work + ((15 * S.card + 30) * m + 11 * m + 38 +
          ch.Cb * bspB S.card m δ ^ 2 * (S.card + 1) * (m + 1) ^ 2 +
          ch.Cbal * bspB S.card m δ ^ 2 * (m + 1)) := awk
      linarith only [bwk, hS1w]

end DetANN.HPIM.PP

theorem solution : type_of% @DetANN.HPIM.PP.lk_loop := @DetANN.HPIM.PP.lk_loop
