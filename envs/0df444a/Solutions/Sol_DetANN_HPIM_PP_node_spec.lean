-- Prove2me | solution 1 for DetANN.HPIM.PP.node_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T09:32:36.35613+00:00
-- url     : https://prove2.me/submissions/f7312d10-12f4-4544-b9c9-2e148a6e6cfc

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
import Theorems.Thm_DetANN_HPIM_PP_lk_loop
import Theorems.Thm_DetANN_HPIM_PP_kids_loop

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

lemma emb2 (hB : B.WF) : Embeds (Blocks.prog B) (seg2 B.o2 B.lbl_RETURN) (B.o2) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 12 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1) (seg2 B.o2 B.lbl_RETURN)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb3 (hB : B.WF) : Embeds (Blocks.prog B) (B.med B.o3) (B.o3) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 11 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN) (B.med B.o3)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb4 (hB : B.WF) : Embeds (Blocks.prog B) (seg4 B.o4) (B.o4) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 10 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3) (seg4 B.o4)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb5 (hB : B.WF) : Embeds (Blocks.prog B) (ladder B.o5) (B.o5) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 9 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4) (ladder B.o5)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb6 (hB : B.WF) : Embeds (Blocks.prog B) (seg6 B.o6 B.lbl_LKE) (B.o6) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 8 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5) (seg6 B.o6 B.lbl_LKE)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb11 (hB : B.WF) : Embeds (Blocks.prog B) (B.comps B.o11) (B.o11) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 3 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8 ++ B.bal B.o9 ++ seg10 B.o10 B.lbl_LK) (B.comps B.o11)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb12 (hB : B.WF) : Embeds (Blocks.prog B) (seg12 B.o12) (B.o12) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 2 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8 ++ B.bal B.o9 ++ seg10 B.o10 B.lbl_LK ++ B.comps B.o11) (seg12 B.o12)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb13 (hB : B.WF) : Embeds (Blocks.prog B) (B.comps B.o13) (B.o13) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 1 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8 ++ B.bal B.o9 ++ seg10 B.o10 B.lbl_LK ++ B.comps B.o11 ++ seg12 B.o12) (B.comps B.o13)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

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

lemma isRep_iff (i : Fin n) : IsRep P d i ↔ compMin P d i = i := by
  constructor
  · intro h
    refine le_antisymm (compMin_le P d i) ?_
    have := h (compMinF P d i) (thrReach_symm P d (reach_compMin P d i))
    exact_mod_cast this
  · intro h j hj
    have h1 := compMin_eq_of_reach P d (thrReach_symm P d hj)
    have h2 := compMin_le P d j
    rw [Fin.le_def]; omega

end Comp

/-- A strictly increasing enumeration of `T` is `T.orderEmbOfFin`. -/
lemma eq_orderEmbOfFin {N k : ℕ} (T : Finset (Fin N)) (hk : T.card = k) (f : Fin k → Fin N)
    (hmem : ∀ x, f x ∈ T) (hmono : StrictMono f) : ∀ x, f x = T.orderEmbOfFin hk x := by
  intro x
  have := Finset.orderEmbOfFin_unique hk hmem hmono
  rw [this]

section Ladder

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

lemma rhoOf_succ (S : Finset (Fin N)) (k : ℕ) :
    rhoOf Y δ S (k + 1) = rhoOf Y δ S k * (1 + δ / 4) := by
  unfold rhoOf; ring

/-- With `r_med > 0` the ladder reaches the top radius. -/
lemma ladder_exists (S : Finset (Fin N)) (hδ : 0 < δ) (hr : 0 < rmedOf Y S) :
    ∃ k, bOf Y δ S ≤ rhoOf Y δ S k := by
  have he : 1 < 1 + δ / 4 := by linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (bOf Y δ S / (rmedOf Y S / 2 / 2 / (1 + δ / 4))) he
  refine ⟨k, ?_⟩
  have hpos : 0 < rmedOf Y S / 2 / 2 / (1 + δ / 4) := by positivity
  rw [div_lt_iff₀ hpos] at hk
  unfold rhoOf
  have : rmedOf Y S / 2 / 2 * (1 + δ / 4) ^ k / (1 + δ / 4) =
      (1 + δ / 4) ^ k * (rmedOf Y S / 2 / 2 / (1 + δ / 4)) := by ring
  rw [this]; exact hk.le

/-- `MOf` is the ladder block's `Nat.find + 1`. -/
lemma MOf_eq (S : Finset (Fin N)) (h : ∃ k, bOf Y δ S ≤ rhoOf Y δ S k) :
    MOf Y δ S = Nat.find h + 1 := by
  unfold MOf; rw [dif_pos h]

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

/-- A single point: `I[v] = 0`, `I[v+1] = I[S]`, then `RETURN`. -/
lemma node_single (Q : Program) (off RET : ℕ) (hE : Embeds Q (seg2 off RET) off) (s : State)
    (hpc : s.core.pc = off + 39) (hh : s.halted = false) (v Sa : ℤ) (hv : s.core.ptrs 2 = v)
    (h3 : s.integerMemory (v + 3) = Sa) (h7 : s.integerMemory (v + 7) = 1) (hv1 : Sa ≠ v) :
    (run Q s detTape 15).core.pc = RET ∧ (run Q s detTape 15).halted = false ∧
      (run Q s detTape 15).integerMemory =
        Function.update (Function.update s.integerMemory v 0) (v + 1) (s.integerMemory Sa) ∧
      (run Q s detTape 15).core.mem = s.core.mem ∧ (run Q s detTape 15).core.regs = s.core.regs ∧
      (∀ x, x ∉ [6, 7, 10, 11, 27] → (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 15).work = s.work + 15 ∧
      cellsWritten Q s 15 ⊆ {(false, v), (false, v + 1)} := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hv h3 h7; subst hpc hh hv
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell, Function.update_apply]
  rw [if_neg (by simp [h7])]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_pos le_rfl, run_zero, cw_zero]
  simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (first | rfl | trivial)
  · rw [h3, if_neg hv1]
  all_goals first
    | (intro c hc
       simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union,
         Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc
       simp only [Finset.mem_insert, Finset.mem_singleton]
       rcases hc with h | h <;> subst h <;> simp)
    | (intro x hx
       simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
       simp (config := {decide := true}) [Function.update_apply, hx])

end DetANN.HPIM.PP

-- ===== PP_Head =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The inner head: from `NODE` with `n ≥ 2` to the median call (`off + 58`), with `I[v] = 1`,
`p10 = S`, `p11 = n`, `p20 = p13`, `p28 = p14`. -/
lemma node_inner (Q : Program) (off RET : ℕ) (hE : Embeds Q (seg2 off RET) off) (s : State)
    (hpc : s.core.pc = off + 39) (hh : s.halted = false) (v Sa : ℤ) (n : ℕ) (hv : s.core.ptrs 2 = v)
    (h3 : s.integerMemory (v + 3) = Sa) (h7 : s.integerMemory (v + 7) = n) (hn : 2 ≤ n) :
    (run Q s detTape 12).core.pc = off + 58 ∧ (run Q s detTape 12).halted = false ∧
      (run Q s detTape 12).integerMemory = Function.update s.integerMemory v 1 ∧
      (run Q s detTape 12).core.mem = s.core.mem ∧ (run Q s detTape 12).core.regs = s.core.regs ∧
      (run Q s detTape 12).core.ptrs 10 = Sa ∧ (run Q s detTape 12).core.ptrs 11 = n ∧
      (run Q s detTape 12).core.ptrs 20 = s.core.ptrs 13 ∧
      (run Q s detTape 12).core.ptrs 28 = s.core.ptrs 14 ∧
      (∀ x, x ∉ [6, 10, 11, 20, 27, 28] → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 12).work = s.work + 12 ∧
      cellsWritten Q s 12 ⊆ {(false, v)} := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hv h3 h7; subst hpc hh hv
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell, Function.update_apply]
  rw [if_pos (by simp [h7]; exact_mod_cast hn)]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at (i := 57) hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
    if_false]
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (first | rfl | trivial)
  (all_goals first
      | rfl | trivial
      | (intro c hc
         simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union,
           Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc
         simp only [Finset.mem_insert, Finset.mem_singleton]
         rcases hc with h | h | h | h <;> subst h <;> simp)
      | (intro x hx
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
         simp (config := {decide := true}) [Function.update_apply, hx])
      | (intro x; intros; simp (config := {decide := true}) only [Function.update_apply, if_false, *])
      | (simp (config := {decide := true}) only [Function.update_apply, if_false, if_true, *]))

/-- `seg4`: `r_med = r10 / 2`, `r40 = 2 n λ r_med`, `r41 = r_med/2/2/e`, `r42 = e`. -/
lemma seg4_spec (Q : Program) (off : ℕ) (hE : Embeds Q (seg4 off) off) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) :
    (run Q s detTape 9).core.pc = off + 9 ∧ (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.regs 3 = s.core.regs 10 / s.core.regs 21 ∧
      (run Q s detTape 9).core.regs 40 = s.core.regs 21 * (s.core.ptrs 11 : ℝ) * s.core.regs 2 *
        (s.core.regs 10 / s.core.regs 21) ∧
      (run Q s detTape 9).core.regs 41 =
        s.core.regs 10 / s.core.regs 21 / s.core.regs 21 / s.core.regs 21 / s.core.regs 1 ∧
      (run Q s detTape 9).core.regs 42 = s.core.regs 1 + s.core.regs 20 ∧
      (∀ x, x ∉ [3, 6, 40, 41, 42] → (run Q s detTape 9).core.regs x = s.core.regs x) ∧
      (run Q s detTape 9).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).core.mem = s.core.mem ∧ (run Q s detTape 9).work = s.work + 9 ∧
      cellsWritten Q s 9 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh; subst hpc hh
  rw [run_exec_at (i := 0) hE rfl (by simp) rfl, cw_exec_at (i := 0) hE rfl (by simp) rfl]
  simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
    if_false]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (first | rfl | trivial)
  (all_goals first
      | rfl | trivial
      | (intro c hc
         simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union,
           Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc
         simp only [Finset.mem_insert, Finset.mem_singleton]
         rcases hc with h | h | h | h <;> subst h <;> simp)
      | (intro x hx
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
         simp (config := {decide := true}) [Function.update_apply, hx])
      | (intro x; intros; simp (config := {decide := true}) only [Function.update_apply, if_false, *])
      | (simp (config := {decide := true}) only [Function.update_apply, if_false, if_true, *]))

end DetANN.HPIM.PP

-- ===== PP_Rec =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

lemma seg6_record (Q : Program) (off LKE : ℕ) (hE : Embeds Q (seg6 off LKE) off) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) (v H : ℤ) (hv : s.core.ptrs 2 = v)
    (hH : s.core.ptrs 15 = H) (hd1 : v + 1 < H) (hd2 : v + 6 < H) (hd3 : v + 2 < H) (hd4 : v + 4 < H) :
    (run Q s detTape 22).core.pc = off + 22 ∧ (run Q s detTape 22).halted = false ∧
      (run Q s detTape 22).integerMemory =
        Function.update (Function.update (Function.update (Function.update s.integerMemory
          (v + 1) (s.core.ptrs 41)) (v + 6) (s.core.ptrs 42)) (v + 2) H) (v + 4)
          (H + s.core.ptrs 41) ∧
      (run Q s detTape 22).core.ptrs 4 = s.core.ptrs 41 ∧
      (run Q s detTape 22).core.ptrs 5 = s.core.ptrs 42 ∧
      (run Q s detTape 22).core.ptrs 18 = H ∧
      (run Q s detTape 22).core.ptrs 19 = H + s.core.ptrs 41 ∧
      (run Q s detTape 22).core.ptrs 15 = H + s.core.ptrs 41 + s.core.ptrs 11 ∧
      (run Q s detTape 22).core.ptrs 3 = 0 ∧
      (∀ x, x ∉ [3, 4, 5, 6, 15, 18, 19, 27] → (run Q s detTape 22).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 22).core.regs 4 =
        s.core.regs 3 / s.core.regs 21 / s.core.regs 21 / s.core.regs 1 ∧
      (∀ x, x ≠ 4 → (run Q s detTape 22).core.regs x = s.core.regs x) ∧
      (run Q s detTape 22).core.mem = s.core.mem ∧ (run Q s detTape 22).work = s.work + 22 ∧
      cellsWritten Q s 22 ⊆ {(false, v + 1), (false, v + 6), (false, v + 2), (false, v + 4)} := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hv hH; subst hpc hh hv hH
  rw [run_exec_at (i := 0) hE rfl (by simp) rfl, cw_exec_at (i := 0) hE rfl (by simp) rfl]
  simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
    if_false]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_zero, cw_zero]
  clear hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (first | rfl | trivial)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h3, h4, h5, h6, h15, h18, h19, h27⟩ := hx
    simp only [Function.update_apply, h3, h4, h5, h6, h15, h18, h19, h27, if_false]
  · intro x hx
    simp only [Function.update_apply, hx, if_false]

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

lemma localPts_of' {S : Finset (Fin N)} {v Sa Zn ZRn : ℤ} {s : State}
    (h : NodeEnv Y δ T0 v0 S v Sa Zn ZRn s) :
    LocalPts s (fun i j => (fun a => Y (S.orderEmbOfFin rfl a)) i j) := localPts_of Y δ T0 v0 h

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

-- ===== PP_Reps =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The selected indices below `i`. -/
def selL (lab : ℕ → ℤ) (i : ℕ) : List ℕ := (List.range i).filter (fun j => decide ((j : ℤ) ≤ lab j))

lemma selL_succ (lab : ℕ → ℤ) (i : ℕ) :
    selL lab (i + 1) = selL lab i ++ (if (i : ℤ) ≤ lab i then [i] else []) := by
  unfold selL
  rw [List.range_succ, List.filter_append]
  split_ifs with h <;> simp [h]

lemma selL_len_mono (lab : ℕ → ℤ) {j j' : ℕ} (h : j ≤ j') :
    (selL lab j).length ≤ (selL lab j').length :=
  ((List.range_sublist.2 h).filter _).length_le

/-- The scan loop `RL`. -/
lemma rl_loop (Q : Program) (off : ℕ) (hE : Embeds Q (seg12 off) off) (n : ℕ) (lab vals : ℕ → ℤ)
    (Zn Sa So : ℤ) (hZn : Zn ≤ 0) (hSo : Sa + n ≤ So) (hSa : 0 ≤ Sa) :
    ∀ d i, i + d = n → ∀ s : State, s.core.pc = off + 3 → s.halted = false →
      s.core.ptrs 11 = n → s.core.ptrs 3 = i → s.core.ptrs 20 = Zn → s.core.ptrs 10 = Sa →
      s.core.ptrs 25 = So → s.core.ptrs 24 = (selL lab i).length →
      (∀ j : ℕ, j < n → s.integerMemory (Zn - 1 - j) = lab j) →
      (∀ j : ℕ, j < n → s.integerMemory (Sa + j) = vals j) →
      (∀ k (hk : k < (selL lab i).length), s.integerMemory (So + k) = vals ((selL lab i)[k])) →
      ∃ t, t ≤ 12 * d + 1 ∧ (run Q s detTape t).core.pc = off + 16 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 24 = (selL lab n).length ∧
        (∀ k (hk : k < (selL lab n).length),
          (run Q s detTape t).integerMemory (So + k) = vals ((selL lab n)[k])) ∧
        (∀ z, (z < So ∨ So + n ≤ z) → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ x, x ∉ [3, 6, 7, 24, 30] → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).work = s.work + t ∧
        (∀ c ∈ cellsWritten Q s t, c.1 = false ∧ So ≤ c.2 ∧ c.2 < So + (selL lab n).length) := by
  intro d
  induction d with
  | zero =>
    intro i hi s hpc hh h11 h3 _ _ _ h24 _ _ hw
    simp only [Nat.add_zero] at hi; subst hi
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h3 h24 hw; subst hpc hh
    rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
    simp only [exec, coreExec, wcell]
    rw [if_pos (by rw [h11, h3]), run_zero, cw_zero]
    exact ⟨rfl, rfl, h24, hw, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, by simp⟩
  | succ d ih =>
    intro i hi s hpc hh h11 h3 h20 h10 h25 h24 hlab hval hw
    have hin : i < n := by omega
    have hlen : (selL lab i).length ≤ i := by
      have := List.length_filter_le (fun j : ℕ => decide ((j : ℤ) ≤ lab j)) (List.range i)
      simpa [selL] using this
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h11 h3 h20 h10 h25 h24 hlab hval hw; subst hpc hh
    have hl : im (ptrs 20 - (i : ℤ) - 1) = lab i := by
      rw [h20, show Zn - (i : ℤ) - 1 = Zn - 1 - i by ring]; exact hlab i hin
    have hv : im (ptrs 10 + ptrs 3) = vals i := by rw [h10, h3]; exact hval i hin
    -- one iteration, either branch
    have step : ∃ u, (u = 12 ∨ u = 8) ∧
        (run Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.pc = off + 3 ∧
        (run Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).halted = false ∧
        (run Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.ptrs 3 = (i + 1 : ℕ) ∧
        (run Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.ptrs 24 =
          (selL lab (i + 1)).length ∧
        (run Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).integerMemory =
          (if (i : ℤ) ≤ lab i then Function.update im (So + (selL lab i).length) (vals i) else im) ∧
        (∀ x, x ∉ [3, 6, 7, 24, 30] →
          (run Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.ptrs x = ptrs x) ∧
        (run Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.regs = regs ∧
        (run Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).core.mem = mem ∧
        (run Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u).work = w + u ∧
        (∀ c ∈ cellsWritten Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ u,
          c = (false, So + (selL lab i).length) ∧ (i : ℤ) ≤ lab i) := by
      have hlen1 : ((selL lab (i + 1)).length : ℤ) =
          (selL lab i).length + (if (i : ℤ) ≤ lab i then 1 else 0) := by
        rw [selL_succ, List.length_append]; split_ifs <;> simp
      by_cases hsel : (i : ℤ) ≤ lab i
      · refine ⟨12, Or.inl rfl, ?_⟩
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]
        rw [if_neg (by rw [h11, h3]; push_cast; omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, hl, h3]
        rw [if_pos hsel]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]; rw [if_pos le_rfl, run_zero, cw_zero]
        clear hE
        refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
        · simp [h3]
        · simp [h24, hlen1, hsel]
        · rw [if_pos hsel]; simp [hv, h25, h24]
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp (config := {decide := true}) [Function.update_apply, hx]
        · intro c hc
          simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
            Finset.mem_union, Finset.mem_singleton] at hc
          subst hc; exact ⟨by simp [h25, h24], hsel⟩
      · refine ⟨8, Or.inr rfl, ?_⟩
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]
        rw [if_neg (by rw [h11, h3]; push_cast; omega)]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp (config := {decide := true}) only [exec, coreExec, wcell, Function.update_apply, if_true,
          if_false, hl, h3]
        rw [if_neg hsel]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
        rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
        simp only [exec, coreExec, wcell]; rw [if_pos le_rfl, run_zero, cw_zero]
        clear hE
        refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, by simp⟩
        · simp [h3]
        · simp [h24, hlen1, hsel]
        · rw [if_neg hsel]
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp (config := {decide := true}) [Function.update_apply, hx]
    obtain ⟨u, hu, a1, a2, a3, a4, a5, a6, a7, a8, aw, acw⟩ := step
    set S1 := run Q ⟨⟨off + 3, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape u with hS1
    have hlen' : (selL lab (i + 1)).length ≤ i + 1 := by
      have := List.length_filter_le (fun j : ℕ => decide ((j : ℤ) ≤ lab j)) (List.range (i + 1))
      simpa [selL] using this
    have fr : ∀ z, z ≠ So + (selL lab i).length → S1.integerMemory z = im z := by
      intro z hz; rw [a5]; split_ifs <;> simp [Function.update_apply, hz]
    obtain ⟨t2, ht2, b1, b2, b3, b4, b5, b6, b7, b8, bw, bcw⟩ := ih (i + 1) (by omega) S1 a1 a2
      (by rw [a6 11 (by simp)]; exact h11) a3 (by rw [a6 20 (by simp)]; exact h20)
      (by rw [a6 10 (by simp)]; exact h10) (by rw [a6 25 (by simp)]; exact h25) a4
      (fun j hj => by rw [fr _ (by omega)]; exact hlab j hj)
      (fun j hj => by rw [fr _ (by omega)]; exact hval j hj)
      (by
        intro k hk
        rw [a5]
        by_cases hsel : (i : ℤ) ≤ lab i
        · rw [if_pos hsel]
          have hs : selL lab (i + 1) = selL lab i ++ [i] := by rw [selL_succ, if_pos hsel]
          simp only [hs, List.length_append, List.length_singleton] at hk ⊢
          rcases Nat.lt_or_ge k (selL lab i).length with h | h
          · rw [Function.update_of_ne (by omega), List.getElem_append_left h]; exact hw k h
          · have : k = (selL lab i).length := by omega
            subst this
            rw [Function.update_self, List.getElem_append_right (le_refl _)]; simp
        · rw [if_neg hsel]
          have hs : selL lab (i + 1) = selL lab i := by rw [selL_succ, if_neg hsel, List.append_nil]
          simp only [hs] at hk ⊢
          exact hw k hk)
    refine ⟨u + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hS1]
    refine ⟨b1, b2, b3, b4, fun z hz => ?_, fun x hx => by rw [b6 x hx, a6 x hx], by rw [b7, a7],
      by rw [b8, a8], by rw [bw, aw]; ring, ?_⟩
    · rw [b5 z hz, fr z (by omega)]
    · intro c hc
      rcases Finset.mem_union.1 hc with h | h
      · obtain ⟨hc', hsel⟩ := acw c h
        have hm : (selL lab (i + 1)).length ≤ (selL lab n).length := selL_len_mono lab (by omega)
        have hs : selL lab (i + 1) = selL lab i ++ [i] := by rw [selL_succ, if_pos hsel]
        rw [hs, List.length_append] at hm
        subst hc'; simp only [List.length_singleton] at hm; simp; omega
      · exact bcw c h

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- `seg12` from its start to the second components call: the representatives' list at
`So = H`, the record `vr = So + cnt` (`I[vr+3] = So`, `I[vr+7] = cnt`), `I[v+5] = vr`, `H = vr + 8`. -/
lemma seg12_spec (Q : Program) (off : ℕ) (hE : Embeds Q (seg12 off) off) (n : ℕ) (lab vals : ℕ → ℤ)
    (Zn Sa v : ℤ) (hZn : Zn ≤ 0) (hSa : 0 ≤ Sa) (s : State) (hpc : s.core.pc = off)
    (hh : s.halted = false) (h11 : s.core.ptrs 11 = n) (h20 : s.core.ptrs 20 = Zn)
    (h10 : s.core.ptrs 10 = Sa) (h2 : s.core.ptrs 2 = v) (hSo : Sa + n ≤ s.core.ptrs 15)
    (hv5 : v + 5 < s.core.ptrs 15)
    (hlab : ∀ j : ℕ, j < n → s.integerMemory (Zn - 1 - j) = lab j)
    (hval : ∀ j : ℕ, j < n → s.integerMemory (Sa + j) = vals j) :
    ∃ t, t ≤ 12 * n + 17 ∧ (run Q s detTape t).core.pc = off + 29 ∧
      (run Q s detTape t).halted = false ∧
      (∀ k (hk : k < (selL lab n).length),
        (run Q s detTape t).integerMemory (s.core.ptrs 15 + k) = vals ((selL lab n)[k])) ∧
      (run Q s detTape t).core.ptrs 21 = s.core.ptrs 15 + (selL lab n).length ∧
      (run Q s detTape t).integerMemory (s.core.ptrs 15 + (selL lab n).length + 3) = s.core.ptrs 15 ∧
      (run Q s detTape t).integerMemory (s.core.ptrs 15 + (selL lab n).length + 7) = (selL lab n).length ∧
      (run Q s detTape t).integerMemory (v + 5) = s.core.ptrs 15 + (selL lab n).length ∧
      (run Q s detTape t).core.ptrs 15 = s.core.ptrs 15 + (selL lab n).length + 8 ∧
      (run Q s detTape t).core.regs 10 = s.core.regs 3 + s.core.regs 20 ∧
      (∀ z, (z < s.core.ptrs 15 ∧ z ≠ v + 5) ∨ s.core.ptrs 15 + n + 8 ≤ z →
        (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ∉ [3, 6, 7, 15, 21, 24, 25, 27, 30] → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 10 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).work = s.work + t ∧
      (∀ c ∈ cellsWritten Q s t, c.1 = false ∧
        ((s.core.ptrs 15 ≤ c.2 ∧ c.2 < s.core.ptrs 15 + (selL lab n).length + 8) ∨ c.2 = v + 5)) := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h11 h20 h10 h2 hSo hv5 hlab hval; subst pc hh
  set H := ptrs 15 with hH
  -- steps 0–2
  set S0 := run Q ⟨⟨off, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 3 with hS0
  have e0 : S0 = ⟨⟨off + 3, regs, Function.update (Function.update (Function.update ptrs 25 H) 24 0) 3 0,
      mem⟩, im, cur, false, w + 3⟩ ∧ cellsWritten Q ⟨⟨off, regs, ptrs, mem⟩, im, cur, false, w⟩ 3 = ∅ := by
    rw [hS0, run_exec_at (i := 0) hE rfl (by simp) rfl, cw_exec_at (i := 0) hE rfl (by simp) rfl]
    simp only [exec, coreExec, wcell]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]; exact ⟨rfl, by simp⟩
  obtain ⟨e0, cw0⟩ := e0
  obtain ⟨t1, ht1, a1, a2, a3, a4, a5, a6, a7, a8, aw, acw⟩ :=
    rl_loop Q off hE n lab vals Zn Sa H hZn hSo hSa n 0 (by omega) S0 (by rw [e0]) (by rw [e0])
      (by rw [e0]; simp [h11]) (by rw [e0]; simp) (by rw [e0]; simp [h20]) (by rw [e0]; simp [h10])
      (by rw [e0]; simp) (by rw [e0]; simp [selL]) (by rw [e0]; exact hlab) (by rw [e0]; exact hval)
      (by intro k hk; simp [selL] at hk)
  generalize hS1 : run Q S0 detTape t1 = S1 at a1 a2 a3 a4 a5 a6 a7 a8 aw acw
  rw [e0] at a5 a6 a7 a8 aw
  obtain ⟨⟨pc1, regs1, ptrs1, mem1⟩, im1, cur1, hlt1, w1⟩ := S1
  simp only at a1 a2 a3 a4 a5 a6 a7 a8 aw; subst a1 a2; subst regs1 mem1
  set c := (selL lab n).length with hc
  have hcn : c ≤ n := by
    have := List.length_filter_le (fun j : ℕ => decide ((j : ℤ) ≤ lab j)) (List.range n)
    simp only [hc, selL]; simpa using this
  have q25 : ptrs1 25 = H := by rw [a6 25 (by simp)]; simp
  have q2 : ptrs1 2 = v := by rw [a6 2 (by simp)]; simp [h2]
  -- steps 16–28
  set S2 := run Q ⟨⟨off + 16, regs, ptrs1, mem⟩, im1, cur1, false, w1⟩ detTape 13 with hS2
  have e2 : S2.core.pc = off + 29 ∧ S2.halted = false ∧ S2.core.ptrs 21 = H + c ∧
      S2.core.ptrs 15 = H + c + 8 ∧
      S2.integerMemory = Function.update (Function.update (Function.update im1 (H + c + 3) H)
        (H + c + 7) c) (v + 5) (H + c) ∧
      S2.core.regs = Function.update regs 10 (regs 3 + regs 20) ∧
      (∀ x, x ∉ [6, 15, 21, 27] → S2.core.ptrs x = ptrs1 x) ∧ S2.core.mem = mem ∧ S2.work = w1 + 13 ∧
      cellsWritten Q ⟨⟨off + 16, regs, ptrs1, mem⟩, im1, cur1, false, w1⟩ 13 ⊆
        {(false, H + c + 3), (false, H + c + 7), (false, v + 5)} := by
    rw [hS2]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
    rw [run_zero, cw_zero]
    clear hE
    refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, ?_, rfl, rfl, ?_⟩
    · simp [q25, a3, hc]
    · simp [q25, a3, hc]
    · simp [q25, a3, hc, q2]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp (config := {decide := true}) [Function.update_apply, hx]
    · intro c' hc'
      simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
        Finset.mem_union, Finset.mem_singleton] at hc'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hc' with h | h | h <;> subst h <;> simp [q25, a3, hc, q2]
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, dw, dcw⟩ := e2
  refine ⟨3 + t1 + 13, by omega, ?_⟩
  rw [run_add, run_add, ← hS0, hS1, ← hS2, cellsWritten_add, cellsWritten_add, run_add, ← hS0, hS1,
    cw0]
  have hvH : v + 5 < H := hv5
  have upd : ∀ z, z ≠ H + c + 3 → z ≠ H + c + 7 → z ≠ v + 5 → S2.integerMemory z = im1 z := by
    intro z h1 h2 h3; rw [d5]; simp [Function.update_apply, h1, h2, h3]
  dsimp only
  refine ⟨d1, d2, ?_, d3, ?_, ?_, ?_, d4, by rw [d6]; simp, ?_, ?_, ?_, d8, by rw [dw, aw]; ring, ?_⟩
  · intro k hk
    rw [upd _ (by omega) (by omega) (by omega)]; exact a4 k hk
  · rw [d5]; simp [Function.update_apply]; omega
  · rw [d5]; simp [Function.update_apply]; omega
  · rw [d5]; simp [hH, hc]
  · intro z hz
    rw [upd _ (by omega) (by omega) (by omega), a5 z (by omega)]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [d7 x (by simp [hx.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.2.2.1]),
      a6 x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2])]
    simp [Function.update_apply, hx.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1]
  · intro x hx; rw [d6]; simp [Function.update_apply, hx]
  · intro c' hc'
    simp only [Finset.empty_union, Finset.mem_union] at hc'
    rcases hc' with h | h
    · obtain ⟨e1, e2, e3⟩ := acw c' h
      exact ⟨e1, Or.inl ⟨e2, by omega⟩⟩
    · have := dcw h
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h' | h' <;> subst h' <;> simp <;> omega

end DetANN.HPIM.PP

-- ===== PP_Size =====
namespace DetANN.HPIM.PP

open DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m))

lemma ptsOf_inj (hY : Function.Injective Y) (S : Finset (Fin N)) : Function.Injective (ptsOf Y S) :=
  fun _ _ h => (S.orderEmbOfFin rfl).injective (hY h)

lemma reps_card_le (hY : Function.Injective Y) (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    (repsOf Y S).card ≤ (S.card + 1) / 2 := by
  obtain ⟨⟨i₀, hbig⟩, _, _⟩ := (median_threshold (ptsOf Y S)).2.2.2 hS (ptsOf_inj Y hY S)
  unfold repsOf
  rw [Finset.card_map]
  apply (median_threshold (ptsOf Y S)).2.2.1 _ i₀
  convert hbig using 4
  unfold rmedOf; ring

lemma rmedOf_pos' (hY : Function.Injective Y) (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    0 < rmedOf Y S := by
  have := ((median_threshold (ptsOf Y S)).2.2.2 hS (ptsOf_inj Y hY S)).2.1
  unfold rmedOf; positivity

lemma rhoOf_pos' (hY : Function.Injective Y) (δ : ℝ) (hδ : 0 < δ) (S : Finset (Fin N))
    (hS : 2 ≤ S.card) (k : ℕ) : 0 < rhoOf Y δ S k := by
  have := rmedOf_pos' Y hY S hS
  unfold rhoOf; positivity

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

lemma slist_of_list {s : State} {a : ℤ} {T : Finset (Fin N)} {L : List ℕ} {vals : ℕ → ℤ}
    (hlen : L.length = T.card)
    (hval : ∀ k (hk : k < L.length), vals L[k] = ((T.orderEmbOfFin rfl ⟨k, hlen ▸ hk⟩ : Fin N) : ℕ))
    (hst : ∀ k (hk : k < L.length), s.integerMemory (a + k) = vals L[k]) : SList s a T := by
  intro i
  have hi : (i : ℕ) < L.length := by rw [hlen]; exact i.isLt
  rw [hst i hi, hval i hi]

lemma slist_reps (S : Finset (Fin N)) {s : State} {a : ℤ} (lab vals : ℕ → ℤ)
    (hlab : ∀ j (hj : j < S.card), lab j = compMin (ptsOf Y S) (2 * rmedOf Y S) ⟨j, hj⟩)
    (hvals : ∀ j (hj : j < S.card), vals j = ((S.orderEmbOfFin rfl ⟨j, hj⟩ : Fin N) : ℕ))
    (hst : ∀ k (hk : k < (selL lab S.card).length),
      s.integerMemory (a + k) = vals (selL lab S.card)[k]) :
    (selL lab S.card).length = (repsOf Y S).card ∧ SList s a (repsOf Y S) := by
  have hp : ∀ j (hj : j < S.card), decide ((j : ℤ) ≤ lab j) = true ↔
      IsRep (ptsOf Y S) (2 * rmedOf Y S) ⟨j, hj⟩ := by
    intro j hj
    rw [decide_eq_true_iff, isRep_iff, hlab j hj]
    have := compMin_le (ptsOf Y S) (2 * rmedOf Y S) ⟨j, hj⟩
    constructor
    · intro h; apply le_antisymm this; exact_mod_cast h
    · intro h; rw [h]
  obtain ⟨hlen, hget⟩ := filter_range_orderEmb (S.orderEmbOfFin rfl)
    (IsRep (ptsOf Y S) (2 * rmedOf Y S)) _ hp
  have hlen' : (selL lab S.card).length = (repsOf Y S).card := hlen
  refine ⟨hlen', slist_of_list hlen' (fun k hk => ?_) hst⟩
  obtain ⟨hj, he⟩ := hget k hk
  exact (hvals _ hj).trans (congrArg (fun x : Fin N => ((x : ℕ) : ℤ)) he.symm)

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

set_option maxHeartbeats 1000000 in
lemma node_head (B : Blocks) (hB : B.WF) (ch : ChildOK B) (hm : 1 ≤ m) (hY : Function.Injective Y)
    (hδ : 0 < δ) (S : Finset (Fin N)) (hn : 2 ≤ S.card) (s : State) (v Sa Zn ZRn H : ℤ)
    (hpc : s.core.pc = B.lbl_NODE) (hh : s.halted = false) (g : GInv Y δ T0 v0 s)
    (h2 : s.core.ptrs 2 = v) (h13 : s.core.ptrs 13 = Zn) (h14 : s.core.ptrs 14 = ZRn)
    (h15 : s.core.ptrs 15 = H) (hv3 : s.integerMemory (v + 3) = Sa)
    (hv7 : s.integerMemory (v + 7) = S.card) (hSL : SList s Sa S) (hHb : Hbase N T0 ≤ Sa)
    (hSv : Sa + S.card ≤ v) (hvH : v + 8 ≤ H) (hZn : Zn ≤ 0) :
    ∃ t, (run (Blocks.prog B) s detTape t).core.pc = B.lbl_LK ∧
      (run (Blocks.prog B) s detTape t).halted = false ∧
      NodeEnv Y δ T0 v0 S v Sa Zn ZRn (run (Blocks.prog B) s detTape t) ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 3 = 0 ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 4 = MOf Y δ S ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 18 = H ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 19 = H + MOf Y δ S ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 15 = H + MOf Y δ S + S.card ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 13 = Zn ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 14 = ZRn ∧
      (∀ x < 40, x ∉ [3, 4, 5, 6, 10, 11, 15, 18, 19, 20, 27, 28] →
        (run (Blocks.prog B) s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (∀ x < 40, x ∉ [3, 4, 6, 10] → (run (Blocks.prog B) s detTape t).core.regs x = s.core.regs x) ∧
      (run (Blocks.prog B) s detTape t).core.regs 4 = rhoOf Y δ S 0 ∧
      (run (Blocks.prog B) s detTape t).core.regs 3 = rmedOf Y S ∧
      (run (Blocks.prog B) s detTape t).integerMemory v = 1 ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 1) = MOf Y δ S ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 2) = H ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 4) = H + MOf Y δ S ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 6) = Nat.clog 2 (MOf Y δ S - 1) ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 3) = Sa ∧
      (∀ c ∈ cellsWritten (Blocks.prog B) s t, c.1 = false ∧
        ((v ≤ c.2 ∧ c.2 < v + 8) ∨ (Zn - ch.Cm * (S.card + 1) ≤ c.2 ∧ c.2 < Zn))) ∧
      (run (Blocks.prog B) s detTape t).work ≤ s.work + headW ch S.card m (MOf Y δ S) := by
  have hHb0 : (0 : ℤ) < Hbase N T0 := by unfold Hbase; positivity
  -- Stage 1: the inner head
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, aw, acw⟩ :=
    node_inner (Blocks.prog B) B.o2 B.lbl_RETURN (emb2 B hB) s hpc hh v Sa S.card h2 hv3 hv7 hn
  set S1 := run (Blocks.prog B) s detTape 12 with hS1
  have g1 : GInv Y δ T0 v0 S1 := GInv.transfer Y δ T0 v0 g
    (fun x hx => a10 x (by simp at hx ⊢; omega)) (fun x _ => by rw [a5])
    (fun z hz0 hz => by rw [a3, Function.update_of_ne (by omega)])
    (fun z _ _ => by rw [a4])
  have env1 : NodeEnv Y δ T0 v0 S v Sa Zn ZRn S1 :=
    ⟨g1, by rw [a10 2 (by simp)]; exact h2, a6, a7, by rw [a8, h13], by rw [a9, h14],
      fun i => by rw [a3, Function.update_of_ne (by have := i.isLt; omega)]; exact hSL i, by omega⟩
  have q13 : S1.core.ptrs 13 = Zn := by rw [a10 13 (by simp)]; exact h13
  have q14 : S1.core.ptrs 14 = ZRn := by rw [a10 14 (by simp)]; exact h14
  have q15 : S1.core.ptrs 15 = H := by rw [a10 15 (by simp)]; exact h15
  -- Stage 2: the median
  obtain ⟨tm, m1, m2, m3, m4, m5, m6⟩ := ch.med B.o3 (Blocks.prog B) (emb3 B hB) m S.card (ptsOf Y S) S1
    hm (by omega) a1 a2 (localPts_of' Y δ T0 v0 env1) (by rw [q13]; exact hZn)
  set S2 := run (Blocks.prog B) S1 detTape tm with hS2
  obtain ⟨mM, mI⟩ := unwritten_of_writesOnly m5
  have env2 : NodeEnv Y δ T0 v0 S v Sa Zn ZRn S2 := env1.transfer Y δ T0 v0
    (fun x hx => m4.1 x (by simp at hx; omega) (by simp)) (fun x hx => m4.2 x (by simp at hx; omega)
      (by simp at hx ⊢; omega))
    (fun z hz => mI z (by rw [q13]; omega)) (fun z _ _ => mM z (by simp))
  have q13b : S2.core.ptrs 13 = Zn := by rw [m4.1 13 (by norm_num) (by simp)]; exact q13
  have q14b : S2.core.ptrs 14 = ZRn := by rw [m4.1 14 (by norm_num) (by simp)]; exact q14
  have q15b : S2.core.ptrs 15 = H := by rw [m4.1 15 (by norm_num) (by simp)]; exact q15
  -- Stage 3: seg4
  obtain ⟨c1, c2, c3, c40, c41, c42, c5, c6, c7, c8, cw, ccw⟩ :=
    seg4_spec (Blocks.prog B) B.o4 (emb4 B hB) S2 m1 m2
  set S3 := run (Blocks.prog B) S2 detTape 9 with hS3
  have env3 : NodeEnv Y δ T0 v0 S v Sa Zn ZRn S3 := env2.transfer Y δ T0 v0
    (fun x _ => by rw [c6]) (fun x hx => c5 x (by simp at hx ⊢; omega))
    (fun z _ => by rw [c7]) (fun z _ _ => by rw [c8])
  have hr21 : S2.core.regs 21 = 2 := env2.g.r21
  have hmed : S2.core.regs 10 = 2 * rmedOf Y S := by rw [m3]; unfold rmedOf; ring
  -- Stage 4: the ladder
  have hrp := rmedOf_pos' Y hY S hn
  have hex := ladder_exists Y δ S hδ hrp
  obtain ⟨nl, hnl, l1, l2, l3, l4, l5, l6, l7, l8, lw, lcw⟩ :=
    ladder_spec_cw (Blocks.prog B) B.o5 (emb5 B hB) (rhoOf Y δ S) (1 + δ / 4) (bOf Y δ S)
      (fun k => rhoOf_succ Y δ S k) hex S3 c1 c2
      (by rw [c40, hr21, env2.p11, env2.g.r2, hmed]; unfold bOf; push_cast; ring)
      (by rw [c41, hr21, hmed, env2.g.r1]; unfold rhoOf; ring)
      (by rw [c42, env2.g.r1, env2.g.r20]; ring)
  set S4 := run (Blocks.prog B) S3 detTape nl with hS4
  have hM : MOf Y δ S = Nat.find hex + 1 := MOf_eq Y δ S hex
  have env4 : NodeEnv Y δ T0 v0 S v Sa Zn ZRn S4 := env3.transfer Y δ T0 v0
    (fun x hx => l7 x (by simp at hx ⊢; omega)) (fun x hx => l8 x (by simp at hx; omega)
      (by simp at hx; omega))
    (fun z _ => by rw [l6]) (fun z _ _ => by rw [l5])
  have q15c : S4.core.ptrs 15 = H := by rw [l7 15 (by simp), c6]; exact q15b
  have q2c : S4.core.ptrs 2 = v := env4.p2
  -- Stage 5: the record
  obtain ⟨d1, d2, d3, d4, d5, d18, d19, d15, d3', d6, d7, d8, dmem, dw, dcw⟩ :=
    seg6_record (Blocks.prog B) B.o6 B.lbl_LKE (emb6 B hB) S4 l1 l2 v H q2c q15c (by omega) (by omega)
      (by omega) (by omega)
  set S5 := run (Blocks.prog B) S4 detTape 22 with hS5
  have hM1 : MOf Y δ S - 1 = Nat.find hex := by omega
  have p41 : S4.core.ptrs 41 = MOf Y δ S := by rw [l3, hM]; push_cast; ring
  have p42 : S4.core.ptrs 42 = Nat.clog 2 (MOf Y δ S - 1) := by rw [l4, hM1]
  have I4 : ∀ z, 0 ≤ z → S4.integerMemory z = S1.integerMemory z := by
    intro z hz; rw [l6, c7, mI z (by rw [q13]; omega)]
  refine ⟨12 + tm + 9 + nl + 22, ?_⟩
  have R : run (Blocks.prog B) s detTape (12 + tm + 9 + nl + 22) = S5 := by
    rw [run_add, run_add, run_add, run_add]
  have CW : cellsWritten (Blocks.prog B) s (12 + tm + 9 + nl + 22) =
      cellsWritten (Blocks.prog B) s 12 ∪ cellsWritten (Blocks.prog B) S1 tm ∪
        cellsWritten (Blocks.prog B) S2 9 ∪ cellsWritten (Blocks.prog B) S3 nl ∪
        cellsWritten (Blocks.prog B) S4 22 := by
    rw [cellsWritten_add, cellsWritten_add, cellsWritten_add, cellsWritten_add, run_add, run_add,
      run_add, run_add, run_add, run_add]
  rw [R, CW]
  have nI : ∀ z, z < v → S5.integerMemory z = S4.integerMemory z := by
    intro z hz; rw [d3]; simp only [Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨d1, d2, ?_, d3', by rw [d4, p41], d18, by rw [d19, p41], by rw [d15, p41, env4.p11],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact env4.transfer Y δ T0 v0 (fun x hx => d6 x (by simp at hx ⊢; omega))
      (fun x hx => d8 x (by simp at hx; omega)) (fun z hz => nI z (by omega)) (fun z _ _ => by rw [dmem])
  · rw [d6 13 (by simp), l7 13 (by simp), c6]; exact q13b
  · rw [d6 14 (by simp), l7 14 (by simp), c6]; exact q14b
  · intro x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    rw [d6 x (by simp; omega), l7 x (by simp; omega), c6, m4.1 x hx (by simp), a10 x (by simp; omega)]
  · intro x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    rw [d8 x (by omega), l8 x (by omega) (by omega), c5 x (by simp; omega), m4.2 x hx (by simp; omega),
      a5]
  · rw [d7, l8 3 (by norm_num) (by norm_num), c3, hmed, l8 21 (by norm_num) (by norm_num),
      c5 21 (by simp), hr21, l8 1 (by norm_num) (by norm_num), c5 1 (by simp), env2.g.r1]
    unfold rhoOf; simp only [pow_zero]; ring
  · rw [d8 3 (by norm_num), l8 3 (by norm_num) (by norm_num), c3, hmed, hr21]; ring
  · rw [d3]; simp only [Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), I4 v (by omega), a3,
      Function.update_self]
  · rw [d3]; simp only [Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos trivial, p41]
  · rw [d3]; simp only [Function.update_apply]
    rw [if_neg (by omega), if_pos trivial]
  · rw [d3]; simp only [Function.update_apply]
    rw [if_pos trivial, p41]
  · rw [d3]; simp only [Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega), if_pos trivial, p42]
  · rw [d3]; simp only [Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), I4 (v + 3) (by omega),
      a3, Function.update_of_ne (by omega)]
    exact hv3
  · intro c hc
    simp only [Finset.mem_union] at hc
    rcases hc with (((h | h) | h) | h) | h
    · have := acw h; simp only [Finset.mem_singleton] at this; subst this
      exact ⟨rfl, Or.inl ⟨le_rfl, by omega⟩⟩
    · obtain ⟨e1, e2, e3⟩ := m5 c h
      rw [q13] at e2 e3; exact ⟨e1, Or.inr ⟨e2, e3⟩⟩
    · rw [ccw] at h; simp at h
    · rw [lcw] at h; simp at h
    · have := dcw h
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h' | h' | h' <;> subst h' <;> exact ⟨rfl, Or.inl ⟨by omega, by omega⟩⟩
  · unfold headW
    rw [dw, lw, hnl, cw, ← hM1]
    have := m6; rw [aw] at this
    omega

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

lemma compsFrom_zero (S : Finset (Fin N)) :
    compsFrom Y S 0 = (Finset.univ : Finset (Fin S.card)).image (compBotOf Y S) := by
  unfold compsFrom; congr 1; ext j; simp

lemma dn_mono (WbI : ℕ) {a b : ℕ} (h : a ≤ b) : Dn WbI a ≤ Dn WbI b := by
  unfold Dn
  have := Nat.clog_mono_right 2 h
  omega

end DetANN.HPIM.PP

-- ===== PP_Kids =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

lemma comps_card_sum (S : Finset (Fin N)) :
    ∑ C ∈ (Finset.univ : Finset (Fin S.card)).image (compBotOf Y S), C.card ≤ S.card := by
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro x hx
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hC
    rw [compBotOf_eq] at hxC
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hxC
    exact Finset.orderEmbOfFin_mem S rfl a
  · intro C hC C' hC' hne
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hC
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hC'
    show Disjoint (compBotOf Y S j) (compBotOf Y S j')
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [compBotOf_eq] at hx hx'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨a', ha', hae⟩ := Finset.mem_map.1 hx'
    have : a' = a := (S.orderEmbOfFin rfl).injective hae
    subst this
    apply hne
    rw [compBotOf_eq, compBotOf_eq, compSet_eq _ _ (thrReach_trans _ _ ((mem_compSet _ _).1 ha)
      (thrReach_symm _ _ ((mem_compSet _ _).1 ha')))]

lemma kidSumH_zero_le (f KH : ℕ) (S : Finset (Fin N)) :
    kidSumH Y f S 0 KH ≤ 9 * S.card + kidSum Y f S 0 * KH := by
  unfold kidSumH kidSum
  rw [compsFrom_zero, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_mul]
  have h1 := comps_card_sum Y S
  have h2 : ∑ C ∈ (Finset.univ : Finset (Fin S.card)).image (compBotOf Y S), 8 ≤ 8 * S.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
    exact Nat.mul_le_mul_left 8 (Finset.card_image_le.trans (by simp))
  omega

end DetANN.HPIM.PP

-- ===== PP_NodeMid =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

lemma kid_entry (Q : Program) (off KN : ℕ) (hE : Embeds Q (seg14 off KN) off) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) :
    (run Q s detTape 1).core.pc = off + 1 ∧ (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs 3 = 0 ∧
      (∀ x, x ≠ 3 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh; subst pc hh
  rw [run_exec_at (i := 0) hE (by simp) (by simp) rfl, cw_exec_at (i := 0) hE (by simp) (by simp) rfl]
  simp only [exec, coreExec, wcell, run_zero, cw_zero]
  refine ⟨?_, ?_, by simp, fun x hx => by simp [Function.update_apply, hx], ?_, ?_, ?_, ?_,
    by simp⟩ <;> first | trivial | rfl

set_option maxHeartbeats 2000000 in
lemma node_mid (B : Blocks) (hB : B.WF) (ch : ChildOK B) (hm : 1 ≤ m) (hY : Function.Injective Y)
    (S : Finset (Fin N)) (hn : 2 ≤ S.card) (v Sa Zn ZRn : ℤ) (s : State)
    (hpc : s.core.pc = B.o11) (hh : s.halted = false) (hEnv : NodeEnv Y δ T0 v0 S v Sa Zn ZRn s)
    (h13 : s.core.ptrs 13 = Zn) (h3r : s.core.regs 3 = rmedOf Y S)
    (h10r : s.core.regs 10 = 2 * rmedOf Y S) (hv5 : v + 5 < s.core.ptrs 15)
    (hSo : Sa + S.card ≤ s.core.ptrs 15) (hZn : Zn ≤ 0) (hHb : Hbase N T0 ≤ Sa)
    (hSv : Sa + S.card ≤ v) :
    ∃ t, (run (Blocks.prog B) s detTape t).core.pc = B.o14 + 1 ∧
      (run (Blocks.prog B) s detTape t).halted = false ∧
      NodeEnv Y δ T0 v0 S v Sa Zn ZRn (run (Blocks.prog B) s detTape t) ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 3 = 0 ∧
      (∀ k : ℕ, k < S.card → (run (Blocks.prog B) s detTape t).integerMemory (Zn - 1 - k) = labOf Y S k) ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 21 = s.core.ptrs 15 + (repsOf Y S).card ∧
      (run (Blocks.prog B) s detTape t).integerMemory (s.core.ptrs 15 + (repsOf Y S).card + 3) =
        s.core.ptrs 15 ∧
      (run (Blocks.prog B) s detTape t).integerMemory (s.core.ptrs 15 + (repsOf Y S).card + 7) =
        (repsOf Y S).card ∧
      SList (run (Blocks.prog B) s detTape t) (s.core.ptrs 15) (repsOf Y S) ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 5) = s.core.ptrs 15 + (repsOf Y S).card ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 15 = s.core.ptrs 15 + (repsOf Y S).card + 8 ∧
      (∀ x < 40, x ∉ [3, 6, 7, 15, 21, 24, 25, 27, 30] →
        (run (Blocks.prog B) s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (∀ x < 40, x ≠ 10 → (run (Blocks.prog B) s detTape t).core.regs x = s.core.regs x) ∧
      (∀ z, 0 ≤ z → z < s.core.ptrs 15 → z ≠ v + 5 →
        (run (Blocks.prog B) s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ z, (run (Blocks.prog B) s detTape t).core.mem z = s.core.mem z) ∧
      (∀ c ∈ cellsWritten (Blocks.prog B) s t, c.1 = false ∧
        ((Zn - ch.Cc * (S.card + 1) ≤ c.2 ∧ c.2 < Zn) ∨
          (s.core.ptrs 15 ≤ c.2 ∧ c.2 < s.core.ptrs 15 + (repsOf Y S).card + 8) ∨ c.2 = v + 5)) ∧
      (run (Blocks.prog B) s detTape t).work ≤ s.work + midW ch S.card m := by
  have hrp := rmedOf_pos' Y hY S hn
  have hSa0 := hEnv.sa
  set H := s.core.ptrs 15 with hH
  -- comps at 2 r_med
  obtain ⟨t1, a1, a2, a3, a4, a5, aw⟩ := ch.comps B.o11 (Blocks.prog B) (emb11 B hB) m S.card (ptsOf Y S)
    (2 * rmedOf Y S) s hm (by omega) hpc hh (localPts_of' Y δ T0 v0 hEnv) h10r (by positivity)
    (by rw [h13]; exact hZn)
  set S1 := run (Blocks.prog B) s detTape t1 with hS1
  obtain ⟨aM, aI⟩ := unwritten_of_writesOnly a5
  rw [h13] at a3 aI
  have env1 : NodeEnv Y δ T0 v0 S v Sa Zn ZRn S1 := hEnv.transfer Y δ T0 v0
    (fun x hx => a4.1 x (by simp at hx; omega) (by simp)) (fun x hx => a4.2 x (by simp at hx; omega) (by simp))
    (fun z hz => aI z (by
      simp only [true_and, not_and, not_lt]
      intro; unfold Hbase at hz; omega)) (fun z _ _ => aM z (by simp))
  have q15 : S1.core.ptrs 15 = H := a4.1 15 (by norm_num) (by simp)
  -- reps scan
  set lab1 : ℕ → ℤ := fun j => if h : j < S.card then
    (compMin (ptsOf Y S) (2 * rmedOf Y S) ⟨j, h⟩ : ℤ) else 0 with hlab1
  obtain ⟨t2, ht2, b1, b2, bL, b21, b3, b7, b5, b15, b10, bI, bP, bR, bM, bw, bcw⟩ :=
    seg12_spec (Blocks.prog B) B.o12 (emb12 B hB) S.card lab1 (valsOf S) Zn Sa v hZn hSa0 S1 a1 a2
      env1.p11 env1.p20 env1.p10 env1.p2 (by rw [q15]; exact hSo) (by rw [q15]; exact hv5)
      (fun j hj => by rw [a3 ⟨j, hj⟩]; simp [hlab1, hj])
      (fun j hj => by
        rw [show Sa + (j : ℤ) = Sa + ((⟨j, hj⟩ : Fin S.card) : ℕ) from rfl, env1.slist ⟨j, hj⟩]
        unfold valsOf; rw [dif_pos hj])
  rw [q15] at bL b21 b3 b7 b5 b15 bI bcw
  set S2 := run (Blocks.prog B) S1 detTape t2 with hS2
  obtain ⟨hlenR, hSLR⟩ := slist_reps Y S lab1 (valsOf S) (fun j hj => by simp [hlab1, hj])
    (fun j hj => by unfold valsOf; rw [dif_pos hj]) bL
  rw [hlenR] at b21 b3 b7 b5 b15 bcw
  have hR1 : (repsOf Y S).card ≤ S.card := by
    rw [← hlenR]
    have := List.length_filter_le (fun j : ℕ => decide ((j : ℤ) ≤ lab1 j)) (List.range S.card)
    simpa [selL] using this
  have env2 : NodeEnv Y δ T0 v0 S v Sa Zn ZRn S2 := env1.transfer Y δ T0 v0
    (fun x hx => bP x (by simp at hx ⊢; omega)) (fun x hx => bR x (by simp at hx; omega))
    (fun z hz => bI z (Or.inl ⟨by omega, by omega⟩))
    (fun z _ _ => by rw [bM])
  have p13b : S2.core.ptrs 13 = Zn := by rw [bP 13 (by simp), a4.1 13 (by norm_num) (by simp), h13]
  -- comps at r_med
  obtain ⟨t3, c1, c2, c3, c4, c5, cw⟩ := ch.comps B.o13 (Blocks.prog B) (emb13 B hB) m S.card (ptsOf Y S)
    (dK Y S) S2 hm (by omega) b1 b2 (localPts_of' Y δ T0 v0 env2)
    (by rw [b10, a4.2 3 (by norm_num) (by simp), h3r, env1.g.r20]; unfold dK; ring)
    (by unfold dK; positivity) (by rw [p13b]; exact hZn)
  set S3 := run (Blocks.prog B) S2 detTape t3 with hS3
  obtain ⟨cM, cI⟩ := unwritten_of_writesOnly c5
  rw [p13b] at c3 cI
  have fI3 : ∀ z, 0 ≤ z → S3.integerMemory z = S2.integerMemory z := fun z hz =>
    cI z (by simp only [true_and, not_and, not_lt]; intro; omega)
  -- the kids loop entry
  obtain ⟨d1, d2, d3, dP, dR, dI, dM, dw, dcw⟩ :=
    kid_entry (Blocks.prog B) B.o14 B.lbl_NODE (emb14 B hB) S3 c1 c2
  set S4 := run (Blocks.prog B) S3 detTape 1 with hS4
  refine ⟨t1 + t2 + t3 + 1, ?_⟩
  have R1 : run (Blocks.prog B) s detTape (t1 + t2) = S2 := by rw [run_add]
  have R2 : run (Blocks.prog B) s detTape (t1 + t2 + t3) = S3 := by rw [run_add, R1]
  have R : run (Blocks.prog B) s detTape (t1 + t2 + t3 + 1) = S4 := by rw [run_add, R2]
  have CW : cellsWritten (Blocks.prog B) s (t1 + t2 + t3 + 1) = cellsWritten (Blocks.prog B) s t1 ∪
      cellsWritten (Blocks.prog B) S1 t2 ∪ cellsWritten (Blocks.prog B) S2 t3 ∪
      cellsWritten (Blocks.prog B) S3 1 := by
    rw [cellsWritten_add, R2, cellsWritten_add, R1, cellsWritten_add]
  rw [R, CW, dcw, Finset.union_empty]
  have kp : ∀ x < 40, x ∉ [3, 6, 7, 15, 21, 24, 25, 27, 30] → S4.core.ptrs x = s.core.ptrs x := by
    intro x hx hx'
    rw [dP x (by intro h; subst h; simp at hx'), c4.1 x hx (by simp), bP x hx', a4.1 x hx (by simp)]
  have kr : ∀ x < 40, x ≠ 10 → S4.core.regs x = s.core.regs x := by
    intro x hx hx'
    rw [dR, c4.2 x hx (by simp), bR x hx', a4.2 x hx (by simp)]
  refine ⟨d1, d2, ?_, d3, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, kp, kr, fun z h0 h1 h2 => ?_,
    fun z => ?_, fun c hc => ?_, ?_⟩
  · have hp : ∀ x ∈ [1, 2, 10, 11, 12, 20, 23, 28], S4.core.ptrs x = S2.core.ptrs x := by
      intro x hx
      have hx' : x < 40 ∧ x ≠ 3 := by simp at hx; omega
      rw [dP x hx'.2]; exact c4.1 x hx'.1 (by simp)
    have hr : ∀ x ∈ [0, 1, 2, 20, 21, 22], S4.core.regs x = S2.core.regs x := by
      intro x hx
      have hx' : x < 40 := by simp at hx; omega
      rw [dR]; exact c4.2 x hx' (by simp)
    have hNm : (0 : ℤ) ≤ N * m := by positivity
    exact env2.transfer Y δ T0 v0 hp hr (fun z hz => by rw [dI, fI3 z (by have := hEnv.sa; omega)])
      (fun z _ _ => by rw [dM, cM z (by simp)])
  · rw [dI, show Zn - 1 - (k : ℤ) = Zn - 1 - ((⟨k, hk⟩ : Fin S.card) : ℕ) from rfl, c3 ⟨k, hk⟩]
    unfold labOf; rw [dif_pos hk]
  · rw [dP 21 (by simp), c4.1 21 (by norm_num) (by simp), b21]
  · rw [dI, fI3 _ (by omega), b3]
  · rw [dI, fI3 _ (by omega), b7]
  · intro k; rw [dI, fI3 _ (by omega)]; exact hSLR k
  · rw [dI, fI3 _ (by omega), b5]
  · rw [dP 15 (by simp), c4.1 15 (by norm_num) (by simp), b15]
  · rw [dI, fI3 z h0, bI z (Or.inl ⟨by omega, h2⟩), aI z (by simp only [true_and, not_and, not_lt]; intro; omega)]
  · rw [dM, cM z (by simp), bM, aM z (by simp)]
  · simp only [Finset.mem_union] at hc
    rcases hc with (h | h) | h
    · obtain ⟨e1, e2, e3⟩ := a5 c h; rw [h13] at e2 e3; exact ⟨e1, Or.inl ⟨e2, e3⟩⟩
    · obtain ⟨e1, e2⟩ := bcw c h; exact ⟨e1, Or.inr e2⟩
    · obtain ⟨e1, e2, e3⟩ := c5 c h; rw [p13b] at e2 e3; exact ⟨e1, Or.inl ⟨e2, e3⟩⟩
  · unfold midW
    have h1 := aw; have h2 : S2.work = S1.work + t2 := bw; have h3 := cw; have h4 : S4.work = S3.work + 1 := dw
    omega

end DetANN.HPIM.PP

-- ===== PP_Node =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

section

variable {Y δ T0}

theorem Budgets.w1 {B : Blocks} {ch : ChildOK B} {KW KH KR WbI WbR : ℕ} (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    15 ≤ KW := bu.1

theorem Budgets.w {B : Blocks} {ch : ChildOK B} {KW KH KR WbI WbR : ℕ} (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    ∀ S : Finset (Fin N), 2 ≤ S.card →
    headW ch S.card m (MOf Y δ S) + MOf Y δ S * lkW ch S.card m δ + 2 + midW ch S.card m +
      S.card * kidW S.card + 5 ≤ S.card * KW := bu.2.1

theorem Budgets.h {B : Blocks} {ch : ChildOK B} {KW KH KR WbI WbR : ℕ} (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    ∀ S : Finset (Fin N), 2 ≤ S.card →
    MOf Y δ S + MOf Y δ S * lkH ch S.card m δ + 11 * S.card + 8 ≤ S.card * KH := bu.2.2.1

theorem Budgets.r {B : Blocks} {ch : ChildOK B} {KW KH KR WbI WbR : ℕ} (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    ∀ S : Finset (Fin N), 2 ≤ S.card → MOf Y δ S * lkR ch S.card m δ ≤ S.card * KR := bu.2.2.2.1

theorem Budgets.dm {B : Blocks} {ch : ChildOK B} {KW KH KR WbI WbR : ℕ} (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    ∀ S : Finset (Fin N), 2 ≤ S.card → ch.Cm * (S.card + 1) ≤ WbI := bu.2.2.2.2.1

theorem Budgets.dc {B : Blocks} {ch : ChildOK B} {KW KH KR WbI WbR : ℕ} (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    ∀ S : Finset (Fin N), 2 ≤ S.card → ch.Cc * (S.card + 1) ≤ WbI := bu.2.2.2.2.2.1

theorem Budgets.dl {B : Blocks} {ch : ChildOK B} {KW KH KR WbI WbR : ℕ} (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    ∀ S : Finset (Fin N), 2 ≤ S.card → lkD ch S.card m δ ≤ WbI := bu.2.2.2.2.2.2.1

theorem Budgets.dlr {B : Blocks} {ch : ChildOK B} {KW KH KR WbI WbR : ℕ} (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    ∀ S : Finset (Fin N), 2 ≤ S.card → lkD ch S.card m δ ≤ WbR := bu.2.2.2.2.2.2.2.1

theorem Budgets.w10 {B : Blocks} {ch : ChildOK B} {KW KH KR WbI WbR : ℕ} (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    10 ≤ WbI := bu.2.2.2.2.2.2.2.2.1

theorem Budgets.t0 {B : Blocks} {ch : ChildOK B} {KW KH KR WbI WbR : ℕ} (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    ∀ S : Finset (Fin N), 2 ≤ S.card → Nat.clog 2 (MOf Y δ S - 1) ≤ T0 := bu.2.2.2.2.2.2.2.2.2

end

lemma wb_le_dn (WbI n : ℕ) : WbI ≤ Dn WbI n := by unfold Dn; omega

lemma reps_card_pos (S : Finset (Fin N)) (hS : 1 ≤ S.card) : 1 ≤ (repsOf Y S).card := by
  unfold repsOf
  rw [Finset.card_map]
  exact Finset.card_pos.2 ⟨⟨0, hS⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j _ => Nat.zero_le _⟩⟩

lemma treePts_succ (f : ℕ) (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    treePts Y (f + 1) S = S.card + kidSum Y f S 0 + treePts Y f (repsOf Y S) := by
  rw [treePts, if_neg (by omega)]
  unfold kidSum
  rw [compsFrom_zero]

lemma hpimNode_succ (f : ℕ) (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    hpimNode Y δ (f + 1) S = .node S.card (MOf Y δ S) (Nat.clog 2 (MOf Y δ S - 1)) (ZOf Y δ S)
      (fun i => ((S.orderEmbOfFin rfl i : Fin N) : ℕ))
      (fun i => hpimNode Y δ f (compBotOf Y S i)) (hpimNode Y δ f (repsOf Y S)) := by
  rw [hpimNode, if_neg (by omega)]

lemma hpimNode_one (f : ℕ) (S : Finset (Fin N)) (hS : S.card = 1) (hne : S.Nonempty) :
    hpimNode Y δ f S = .single (S.min' hne : ℕ) := by
  cases f with
  | zero => rw [hpimNode, dif_pos hne]
  | succ f => rw [hpimNode, if_pos (by omega), dif_pos hne]

lemma treePts_one (f : ℕ) (S : Finset (Fin N)) (hS : S.card = 1) : treePts Y f S = 1 := by
  cases f with
  | zero => rw [treePts, hS]
  | succ f => rw [treePts, if_pos (by omega), hS]

/-- A single point satisfies the node contract at every fuel. -/
lemma node_single_ok (B : Blocks) (hB : B.WF) (KW KH KR WbI WbR f : ℕ) (hKW : 15 ≤ KW)
    (S : Finset (Fin N)) (hS : S.card = 1) : NodeOKAt Y δ T0 v0 B KW KH KR WbI WbR f S := by
  intro s v Sa Zn ZRn FP H HR hpc hh g h2 h13 h14 h8 h15 h16 hv3 hv7 hSL hHb hSv hvH hHR hZn hZRn
  have hHb0 : (0 : ℤ) < Hbase N T0 := by unfold Hbase; positivity
  have hne : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨a1, a2, a3, a4, a5, a6, aw, acw⟩ :=
    node_single (Blocks.prog B) B.o2 B.lbl_RETURN (emb2 B hB) s hpc hh v Sa h2 hv3
      (by rw [hv7, hS]; norm_num) (by rw [hS] at hSv; push_cast at hSv; omega)
  have hk : s.integerMemory Sa = ((S.min' hne : Fin N) : ℕ) := by
    have := hSL ⟨0, by omega⟩
    simp only [Fin.val_mk, Nat.cast_zero, add_zero] at this
    rw [this, Finset.orderEmbOfFin_zero rfl (by omega)]
  rw [hS] at hSv; push_cast at hSv
  have hT := treePts_one Y f S hS
  refine ⟨15, a1, a2, ?_, by rw [a6 8 (by simp)]; exact h8, by rw [a6 15 (by simp), h15],
    by rw [a6 15 (by simp), h15, hT]; push_cast; nlinarith, by rw [a6 16 (by simp), h16],
    by rw [a6 16 (by simp), h16, hT]; push_cast; nlinarith, by rw [aw, hT]; omega, ?_, ?_⟩
  · exact GInv.transfer Y δ T0 v0 g (fun x hx => a6 x (by simp at hx ⊢; omega)) (fun x _ => by rw [a5])
      (fun z h0 h1 => by
        rw [a3, Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
      (fun z _ _ => by rw [a4])
  · intro c hc
    have := acw hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h <;> subst h <;> exact Or.inl ⟨rfl, Or.inl ⟨by simp, by simp⟩⟩
  · intro s'' hI _ _
    rw [hpimNode_one Y δ f S hS hne]
    have e15 : (run (Blocks.prog B) s detTape 15).core.ptrs 15 = H := by rw [a6 15 (by simp), h15]
    refine HTreeAt.single v _ ?_ ?_
    · rw [hI v (by omega) (by omega), a3]; simp
    · rw [hI (v + 1) (by omega) (by omega), a3, Function.update_self, hk]

set_option maxHeartbeats 2000000 in
/-- The node from `NODE` to the entry of the kids loop: head, lookup loop and middle. -/
lemma node_pre (B : Blocks) (hB : B.WF) (ch : ChildOK B) (hm : 1 ≤ m) (hY : Function.Injective Y)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) (S : Finset (Fin N)) (hn : 2 ≤ S.card) (W : ℕ)
    (hW1 : ch.Cm * (S.card + 1) ≤ W) (hW2 : ch.Cc * (S.card + 1) ≤ W) (hW3 : lkD ch S.card m δ ≤ W)
    (s : State) (v Sa Zn ZRn FP H HR : ℤ)
    (hpc : s.core.pc = B.lbl_NODE) (hh : s.halted = false) (g : GInv Y δ T0 v0 s)
    (h2 : s.core.ptrs 2 = v) (h13 : s.core.ptrs 13 = Zn) (h14 : s.core.ptrs 14 = ZRn)
    (h8 : s.core.ptrs 8 = FP) (h15 : s.core.ptrs 15 = H) (h16 : s.core.ptrs 16 = HR)
    (hv3 : s.integerMemory (v + 3) = Sa) (hv7 : s.integerMemory (v + 7) = S.card)
    (hSL : SList s Sa S) (hHb : Hbase N T0 ≤ Sa) (hSv : Sa + S.card ≤ v) (hvH : v + 8 ≤ H)
    (hHR : 1 + (N : ℤ) * m ≤ HR) (hZn : Zn ≤ 0) (hZRn : ZRn ≤ 0) :
    ∃ t, ∃ L : ℤ, (run (Blocks.prog B) s detTape t).core.pc = B.o14 + 1 ∧
      (run (Blocks.prog B) s detTape t).halted = false ∧
      NodeEnv Y δ T0 v0 S v Sa Zn ZRn (run (Blocks.prog B) s detTape t) ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 3 = 0 ∧
      (∀ k : ℕ, k < S.card → (run (Blocks.prog B) s detTape t).integerMemory (Zn - 1 - k) = labOf Y S k) ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 19 = H + MOf Y δ S ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 21 = L + (repsOf Y S).card ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 8 = FP ∧
      (run (Blocks.prog B) s detTape t).integerMemory (L + (repsOf Y S).card + 3) = L ∧
      (run (Blocks.prog B) s detTape t).integerMemory (L + (repsOf Y S).card + 7) = (repsOf Y S).card ∧
      SList (run (Blocks.prog B) s detTape t) L (repsOf Y S) ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 5) = L + (repsOf Y S).card ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 15 = L + (repsOf Y S).card + 8 ∧
      H + MOf Y δ S + S.card ≤ L ∧
      L ≤ H + MOf Y δ S + S.card + MOf Y δ S * lkH ch S.card m δ ∧
      HR ≤ (run (Blocks.prog B) s detTape t).core.ptrs 16 ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 16 ≤ HR + MOf Y δ S * lkR ch S.card m δ ∧
      (run (Blocks.prog B) s detTape t).integerMemory v = 1 ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 1) = MOf Y δ S ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 2) = H ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 3) = Sa ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 4) = H + MOf Y δ S ∧
      (run (Blocks.prog B) s detTape t).integerMemory (v + 6) = Nat.clog 2 (MOf Y δ S - 1) ∧
      (∀ i (hi : i < MOf Y δ S), ∀ s'' : State,
        (∀ z, H + MOf Y δ S + S.card ≤ z → z < L →
          s''.integerMemory z = (run (Blocks.prog B) s detTape t).integerMemory z) →
        (∀ z, HR ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 16 →
          s''.core.mem z = (run (Blocks.prog B) s detTape t).core.mem z) →
        BoxTreeAt m s'' ((run (Blocks.prog B) s detTape t).integerMemory (H + i))
          (ZOf Y δ S ⟨i, hi⟩)) ∧
      (∀ c ∈ cellsWritten (Blocks.prog B) s t,
        (c.1 = false ∧ ((v ≤ c.2 ∧ c.2 < v + 8) ∨ (H ≤ c.2 ∧ c.2 < L + (repsOf Y S).card + 8) ∨
          (Zn - W ≤ c.2 ∧ c.2 < Zn))) ∨
        (c.1 = true ∧ ((HR ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 16) ∨
          (ZRn - lkD ch S.card m δ ≤ c.2 ∧ c.2 < ZRn)))) ∧
      (run (Blocks.prog B) s detTape t).work ≤ s.work + (headW ch S.card m (MOf Y δ S) +
        MOf Y δ S * lkW ch S.card m δ + 2 + midW ch S.card m) := by
  have hHb0 : (0 : ℤ) < Hbase N T0 := by unfold Hbase; positivity
  -- Stage 1: the head
  obtain ⟨t1, a1, a2, aE, a3, a4, a18, a19, a15, a13, a14, aP, aR, ar4, ar3, aI0, aI1, aI2, aI4, aI6,
      aI3, acw, aw⟩ :=
    node_head Y δ T0 v0 B hB ch hm hY hδ S hn s v Sa Zn ZRn H hpc hh g h2 h13 h14 h15 hv3 hv7 hSL hHb
      hSv hvH hZn
  set S1 := run (Blocks.prog B) s detTape t1 with hS1
  have q16a : S1.core.ptrs 16 = HR := by rw [aP 16 (by norm_num) (by simp), h16]
  have q8a : S1.core.ptrs 8 = FP := by rw [aP 8 (by norm_num) (by simp), h8]
  -- Stage 2: the lookup loop
  obtain ⟨t2, b1, b2, bE, b13, b14, bP, bR, b10, b15l, b15u, b16l, b16u, bZ, bI, bM, bcw, bw⟩ :=
    lk_loop Y δ T0 v0 B hB ch hm hδ hδ' S hn v Sa Zn ZRn H (H + MOf Y δ S + S.card) HR (MOf Y δ S) rfl
      (rhoOf_pos' Y hY δ hδ S hn) hZn hZRn hHR (by omega) (by omega) hHb (by omega)
      (MOf Y δ S) 0 (by omega) S1 a1 a2 aE (by rw [a3]; simp) a4 a18 a13 a14 ar4 (by rw [a15])
      (by rw [q16a]) (fun i' hi' => absurd hi' (Nat.not_lt_zero _))
  set S2 := run (Blocks.prog B) S1 detTape t2 with hS2
  have h3r : S2.core.regs 3 = rmedOf Y S := by rw [bR 3 (by norm_num) (by simp), ar3]
  have h10r : S2.core.regs 10 = 2 * rmedOf Y S := by rw [b10, ar3, aE.g.r21]
  -- Stage 3: the middle
  obtain ⟨t3, c1, c2, cE, c3, cL, c21, cR3, cR7, cSL, c5, c15, cP, cR, cI, cM, ccw, cw⟩ :=
    node_mid Y δ T0 v0 B hB ch hm hY S hn v Sa Zn ZRn S2 b1 b2 bE b13 h3r h10r (by omega) (by omega)
      hZn hHb hSv
  set S3 := run (Blocks.prog B) S2 detTape t3 with hS3
  refine ⟨t1 + t2 + t3, S2.core.ptrs 15, ?_⟩
  have R3 : run (Blocks.prog B) s detTape (t1 + t2 + t3) = S3 := by rw [run_add, run_add]
  have CW : cellsWritten (Blocks.prog B) s (t1 + t2 + t3) =
      cellsWritten (Blocks.prog B) s t1 ∪ cellsWritten (Blocks.prog B) S1 t2 ∪
        cellsWritten (Blocks.prog B) S2 t3 := by
    rw [cellsWritten_add, cellsWritten_add, run_add]
  rw [R3, CW]
  have q16c : S3.core.ptrs 16 = S2.core.ptrs 16 := cP 16 (by norm_num) (by simp)
  have V : ∀ z, 0 ≤ z → z < H → z ≠ v + 5 → S3.integerMemory z = S1.integerMemory z := by
    intro z h0 h1 h2
    rw [cI z h0 (by omega) h2, bI z (Or.inl h1) h0]
  refine ⟨c1, c2, cE, c3, cL, by rw [cP 19 (by norm_num) (by simp), bP 19 (by norm_num) (by simp), a19],
    c21, by rw [cP 8 (by norm_num) (by simp), bP 8 (by norm_num) (by simp), q8a], cR3, cR7, cSL, c5,
    c15, by rw [a15] at b15l; exact b15l, by rw [a15] at b15u; push_cast at b15u ⊢; exact b15u,
    by rw [q16c, ← q16a]; exact b16l, by rw [q16c, ← q16a]; push_cast at b16u ⊢; exact b16u,
    by rw [V v (by omega) (by omega) (by omega), aI0],
    by rw [V (v + 1) (by omega) (by omega) (by omega), aI1],
    by rw [V (v + 2) (by omega) (by omega) (by omega), aI2],
    by rw [V (v + 3) (by omega) (by omega) (by omega), aI3],
    by rw [V (v + 4) (by omega) (by omega) (by omega), aI4],
    by rw [V (v + 6) (by omega) (by omega) (by omega), aI6], ?_, ?_, ?_⟩
  · intro i hi s'' hI hM
    rw [cI (H + i) (by omega) (by omega) (by omega)]
    exact bZ i hi s'' (fun z h0 h1 => by rw [hI z h0 h1, cI z (by omega) h1 (by omega)])
      (fun z h0 h1 => by rw [hM z h0 (by rw [q16c]; exact h1), cM])
  · intro c hc
    simp only [Finset.mem_union] at hc
    have W1 : (ch.Cm : ℤ) * (S.card + 1) ≤ W := by exact_mod_cast hW1
    have W2 : (ch.Cc : ℤ) * (S.card + 1) ≤ W := by exact_mod_cast hW2
    have W3 : (lkD ch S.card m δ : ℤ) ≤ W := by exact_mod_cast hW3
    rcases hc with (h | h) | h
    · obtain ⟨e1', e | e⟩ := acw c h
      · exact Or.inl ⟨e1', Or.inl e⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inr ⟨by linarith [e.1], e.2⟩)⟩
    · rcases bcw c h with ⟨e1', e | e | e⟩ | ⟨e1', e | e⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inr ⟨by linarith [e.1], e.2⟩)⟩
      · exact Or.inr ⟨e1', Or.inl ⟨by omega, by omega⟩⟩
      · exact Or.inr ⟨e1', Or.inr e⟩
    · obtain ⟨e1', e | e | e⟩ := ccw c h
      · exact Or.inl ⟨e1', Or.inr (Or.inr ⟨by linarith [e.1], e.2⟩)⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
      · exact Or.inl ⟨e1', Or.inl ⟨by omega, by omega⟩⟩
  · have := aw; have := bw; have := cw
    omega

set_option maxHeartbeats 4000000 in
/-- An inner node satisfies the contract at fuel `f + 1`, given the contract at fuel `f`. -/
lemma node_full (B : Blocks) (hB : B.WF) (ch : ChildOK B) (hm : 1 ≤ m) (hY : Function.Injective Y)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) (KW KH KR WbI WbR f : ℕ)
    (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) (IH : NodeOK Y δ T0 v0 B KW KH KR WbI WbR f)
    (S : Finset (Fin N)) (hn : 2 ≤ S.card) (hnf : S.card ≤ f + 2) :
    NodeOKAt Y δ T0 v0 B KW KH KR WbI WbR (f + 1) S := by
  intro s v Sa Zn ZRn FP H HR hpc hh g h2 h13 h14 h8 h15 h16 hv3 hv7 hSL hHb hSv hvH hHR hZn hZRn
  have hHb0 : (0 : ℤ) < Hbase N T0 := by unfold Hbase; positivity
  have hNm : (0 : ℤ) ≤ (N : ℤ) * m := by positivity
  have hD := wb_le_dn WbI S.card
  obtain ⟨t3, L, c1, c2, cE, c3, cL, c19, c21, c8, cR3, cR7, cSL, c5, c15, cLl, cLu, c16l, c16u, cV0,
      cV1, cV2, cV3, cV4, cV6, cZ, ccw, cw⟩ :=
    node_pre Y δ T0 v0 B hB ch hm hY hδ hδ' S hn (Dn WbI S.card) ((bu.dm S hn).trans hD)
      ((bu.dc S hn).trans hD) ((bu.dl S hn).trans hD) s v Sa Zn ZRn FP H HR hpc hh g h2 h13 h14 h8 h15
      h16 hv3 hv7 hSL hHb hSv hvH hHR hZn hZRn
  set S3 := run (Blocks.prog B) s detTape t3 with hS3
  set R := repsOf Y S with hR
  set vr := L + R.card with hvr
  have hR1 : 1 ≤ R.card := reps_card_pos Y S (by omega)
  have hR2 : R.card ≤ (S.card + 1) / 2 := reps_card_le Y hY S hn
  -- Stage 4: the kids loop
  obtain ⟨t4, d1, d2, dG, d2', d13, d14, d8, d15l, d15u, d16l, d16u, dw, dI, dL, dK, dM, dS, dcw⟩ :=
    kids_loop Y δ T0 v0 B hB KW KH KR WbI WbR f IH hY S hn hnf v Sa Zn ZRn FP (H + MOf Y δ S) vr hHb
      (by omega) hZn hZRn bu.w10 S.card 0 (by omega) S3 c1 c2 cE (by rw [c3]; simp) c19 c21 c8 cL
      (by rw [c15]; omega) (by omega)
  set S4 := run (Blocks.prog B) S3 detTape t4 with hS4
  have dI' : ∀ z, 0 ≤ z → z < S3.core.ptrs 15 → (z < H + MOf Y δ S ∨ H + MOf Y δ S + S.card ≤ z) →
      S4.integerMemory z = S3.integerMemory z := fun z h0 h1 h2 => dI z h0 h1 (by push_cast; omega)
  have v3' : S4.integerMemory (vr + 3) = L := by rw [dI' _ (by omega) (by omega) (by omega), cR3]
  have v7' : S4.integerMemory (vr + 7) = R.card := by rw [dI' _ (by omega) (by omega) (by omega), cR7]
  have sl4 : SList S4 L R := fun i => by
    rw [dI' _ (by omega) (by have := i.isLt; omega) (by omega)]; exact cSL i
  -- Stage 5: the representatives (tail call)
  obtain ⟨t5, e1, e2, eG, e8, e15l, e15u, e16l, e16u, ew, ecw, eS⟩ :=
    IH R hR1 (by omega) S4 vr L Zn ZRn FP (S4.core.ptrs 15) (S4.core.ptrs 16) d1 d2 dG d2' d13 d14 d8
      rfl rfl v3' v7' sl4 (by omega) le_rfl (by omega) (by omega) hZn hZRn
  set S5 := run (Blocks.prog B) S4 detTape t5 with hS5
  -- preservation through the tail call
  have P5 : ∀ z, 0 ≤ z → (z < vr ∨ vr + 8 ≤ z) → z < S4.core.ptrs 15 →
      S5.integerMemory z = S4.integerMemory z := by
    intro z h0 h1 h2
    apply run_im_unwritten
    intro hc
    rcases ecw _ hc with ⟨_, e | e | e⟩ | ⟨e, _⟩
    · omega
    · omega
    · omega
    · simp at e
  have M5 : ∀ z, 1 ≤ z → z < S4.core.ptrs 16 → S5.core.mem z = S4.core.mem z := by
    intro z h0 h1
    apply run_mem_unwritten
    intro hc
    rcases ecw _ hc with ⟨e, _⟩ | ⟨_, e | e⟩
    · simp at e
    · omega
    · omega
  refine ⟨t3 + t4 + t5, ?_⟩
  have RR : run (Blocks.prog B) s detTape (t3 + t4 + t5) = S5 := by rw [run_add, run_add]
  have CW : cellsWritten (Blocks.prog B) s (t3 + t4 + t5) =
      cellsWritten (Blocks.prog B) s t3 ∪ cellsWritten (Blocks.prog B) S3 t4 ∪
        cellsWritten (Blocks.prog B) S4 t5 := by
    rw [cellsWritten_add, cellsWritten_add, run_add]
  rw [RR, CW]
  -- accounting
  have htp := treePts_succ Y f S hn
  have ehtp : (treePts Y (f + 1) S : ℤ) = S.card + kidSum Y f S 0 + treePts Y f R := by
    rw [htp]; push_cast; ring
  refine ⟨e1, e2, eG, e8, by omega, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · -- integer heap
    have k1 : ((kidSumH Y f S 0 KH : ℕ) : ℤ) ≤ 9 * S.card + (kidSum Y f S 0 : ℤ) * KH := by
      exact_mod_cast kidSumH_zero_le Y f KH S
    have k2 : ((MOf Y δ S + MOf Y δ S * lkH ch S.card m δ + 11 * S.card + 8 : ℕ) : ℤ) ≤
        ((S.card * KH : ℕ) : ℤ) := by exact_mod_cast bu.h S hn
    push_cast at k2 cLu
    have k3 : (R.card : ℤ) ≤ S.card := by exact_mod_cast (show R.card ≤ S.card by omega)
    have k4 : (treePts Y (f + 1) S : ℤ) * KH =
        (S.card : ℤ) * KH + (kidSum Y f S 0 : ℤ) * KH + (treePts Y f R : ℤ) * KH := by
      rw [ehtp]; ring
    linarith only [k1, k2, k3, k4, cLu, c15, d15u, e15u]
  · -- real heap
    have k2 : ((MOf Y δ S * lkR ch S.card m δ : ℕ) : ℤ) ≤ ((S.card * KR : ℕ) : ℤ) := by
      exact_mod_cast bu.r S hn
    push_cast at k2 c16u
    have k4 : (treePts Y (f + 1) S : ℤ) * KR =
        (S.card : ℤ) * KR + (kidSum Y f S 0 : ℤ) * KR + (treePts Y f R : ℤ) * KR := by
      rw [ehtp]; ring
    linarith only [k2, k4, c16u, d16u, e16u]
  · -- work
    have bw' := bu.w S hn
    have e3 : treePts Y (f + 1) S * KW =
        S.card * KW + kidSum Y f S 0 * KW + treePts Y f R * KW := by rw [htp]; ring
    rw [e3]
    have := cw; have := dw; have := ew
    omega
  · -- the write window
    have D4 : (lkD ch S.card m δ : ℤ) ≤ (WbR : ℤ) := by exact_mod_cast bu.dlr S hn
    have D5 : (Dn WbI R.card : ℤ) ≤ (Dn WbI S.card : ℤ) := by
      exact_mod_cast dn_mono WbI (show R.card ≤ S.card by omega)
    intro c hc
    simp only [Finset.mem_union] at hc
    rcases hc with (h | h) | h
    · rcases ccw c h with ⟨e1', e | e | e⟩ | ⟨e1', e | e⟩
      · exact Or.inl ⟨e1', Or.inl e⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨e.1, by omega⟩)⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inr e)⟩
      · exact Or.inr ⟨e1', Or.inl ⟨e.1, by omega⟩⟩
      · exact Or.inr ⟨e1', Or.inr ⟨by linarith [e.1], e.2⟩⟩
    · rcases dcw c h with ⟨e1', e | e | e⟩ | ⟨e1', e | e⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨by push_cast at e; omega, by push_cast at e; omega⟩)⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inr ⟨e.1, by omega⟩)⟩
      · exact Or.inr ⟨e1', Or.inl ⟨by omega, by omega⟩⟩
      · exact Or.inr ⟨e1', Or.inr e⟩
    · rcases ecw c h with ⟨e1', e | e | e⟩ | ⟨e1', e | e⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inl ⟨by omega, e.2⟩)⟩
      · exact Or.inl ⟨e1', Or.inr (Or.inr ⟨by linarith [e.1], e.2⟩)⟩
      · exact Or.inr ⟨e1', Or.inl ⟨by omega, e.2⟩⟩
      · exact Or.inr ⟨e1', Or.inr e⟩
  · -- stability of the stored tree
    intro s'' hI hH hMm
    have hW : ∀ z, Sa ≤ z → z < L → (z < H + MOf Y δ S ∨ H + MOf Y δ S + S.card ≤ z) →
        s''.integerMemory z = S3.integerMemory z := by
      intro z h0 h1 h2
      rw [hI z h0 (by omega), P5 z (by omega) (Or.inl (by omega)) (by omega),
        dI' z (by omega) (by omega) h2]
    have hV : ∀ z, Sa ≤ z → z < H → s''.integerMemory z = S3.integerMemory z :=
      fun z h0 h1 => hW z h0 (by omega) (Or.inl (by omega))
    rw [hpimNode_succ Y δ f S hn]
    refine HTreeAt.node v _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hV v (by omega) (by omega), cV0]
    · rw [hV (v + 1) (by omega) (by omega), cV1]
    · rw [hV (v + 6) (by omega) (by omega), cV6]
    · intro t ht
      have ht' := ht.trans (bu.t0 S hn)
      have g3 : s''.integerMemory 3 = 4 + N := by
        rw [hH 3 (by norm_num) (by unfold Hbase; omega)]; exact eG.i3
      rw [g3, hH _ (by omega) (by unfold Hbase; omega)]
      exact eG.pow t ht'
    · intro i
      have hi := i.isLt
      rw [hV (v + 2) (by omega) (by omega), cV2, hW _ (by omega) (by omega) (Or.inl (by omega))]
      exact cZ i hi s'' (fun z h0 h1 => hW z (by omega) h1 (Or.inr h0))
        (fun z h0 h1 => by
          rw [hMm z h0 (by omega), M5 z (by omega) (by omega), dM z (by omega) h1])
    · intro i
      have hi := i.isLt
      rw [hV (v + 3) (by omega) (by omega), cV3, hV _ (by omega) (by omega)]
      exact cE.slist i
    · intro i
      have hi := i.isLt
      rw [hV (v + 4) (by omega) (by omega), cV4,
        hI _ (by omega) (by omega), P5 _ (by omega) (Or.inl (by omega)) (by omega)]
      exact dS i hi (Nat.zero_le _) s''
        (fun z h0 h1 => by
          rw [hI z (by omega) (by omega), P5 z (by omega) (Or.inr (by omega)) h1])
        (fun z h0 h1 => by
          rw [hH z h0 h1, P5 z h0 (Or.inl (by omega)) (by omega)])
        (fun z h0 h1 => by
          rw [hMm z (by omega) (by omega), M5 z (by omega) h1])
    · have : s''.integerMemory (v + 5) = vr := by
        rw [hI _ (by omega) (by omega), P5 _ (by omega) (Or.inl (by omega)) (by omega),
          dI' _ (by omega) (by omega) (Or.inl (by omega)), c5]
      rw [this]
      exact eS s'' (fun z h0 h1 => hI z (by omega) h1) hH (fun z h0 h1 => hMm z (by omega) h1)

/-- **The node contract at every fuel.** -/
theorem node_spec (B : Blocks) (hB : B.WF) (ch : ChildOK B) (hm : 1 ≤ m)
    (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (KW KH KR WbI WbR : ℕ)
    (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    ∀ f, NodeOK Y δ T0 v0 B KW KH KR WbI WbR f := by
  intro f
  induction f with
  | zero =>
    intro S h1 h2
    exact node_single_ok Y δ T0 v0 B hB KW KH KR WbI WbR 0 bu.w1 S (by omega)
  | succ f ih =>
    intro S h1 h2
    rcases (show S.card = 1 ∨ 2 ≤ S.card by omega) with h | h
    · exact node_single_ok Y δ T0 v0 B hB KW KH KR WbI WbR (f + 1) bu.w1 S h
    · exact node_full Y δ T0 v0 B hB ch hm hY hδ hδ' KW KH KR WbI WbR f bu ih S h h2

end DetANN.HPIM.PP

theorem solution : type_of% @DetANN.HPIM.PP.node_spec := @DetANN.HPIM.PP.node_spec
