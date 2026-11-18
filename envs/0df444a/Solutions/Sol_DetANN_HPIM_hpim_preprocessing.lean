-- Prove2me | solution 1 for DetANN.HPIM.hpim_preprocessing
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T09:37:16.569302+00:00
-- url     : https://prove2.me/submissions/1788df52-c388-405d-9e52-1436bdd4868f

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
import Theorems.Thm_DetANN_HPIM_median_block
import Theorems.Thm_DetANN_HPIM_comps_block
import Theorems.Thm_DetANN_HPIM_build_block
import Theorems.Thm_DetANN_HPIM_balance_block
import Theorems.Thm_DetANN_HPIM_tree_points
import Theorems.Thm_DetANN_HPIM_PP_init_spec
import Theorems.Thm_DetANN_HPIM_PP_node_spec
import Theorems.Thm_DetANN_HPIM_PP_pre_bounds

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

end Comp

section Ladder

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

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

-- ===== PP_Ret =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- Code `0`: halt. -/
lemma ret_halt (Q : Program) (off KN : ℕ) (hE : Embeds Q (seg14 off KN) off) (s : State)
    (hpc : s.core.pc = off + 82) (hh : s.halted = false) (hc : s.integerMemory (s.core.ptrs 8) = 0) :
    (run Q s detTape 4).halted = true ∧ (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧ (run Q s detTape 4).work = s.work + 4 := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hc; subst hpc hh
  (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
  rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Function.update_apply]
  rw [if_pos (by simp [hc])]
  rw [run_exec_at (i := 106) hE rfl rfl rfl]; simp only [exec, run_zero]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

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

-- ===== PP_Size =====
namespace DetANN.HPIM.PP

open DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m))

lemma ptsOf_inj (hY : Function.Injective Y) (S : Finset (Fin N)) : Function.Injective (ptsOf Y S) :=
  fun _ _ h => (S.orderEmbOfFin rfl).injective (hY h)

lemma rmedOf_pos' (hY : Function.Injective Y) (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    0 < rmedOf Y S := by
  have := ((median_threshold (ptsOf Y S)).2.2.2 hS (ptsOf_inj Y hY S)).2.1
  unfold rmedOf; positivity

end DetANN.HPIM.PP

-- ===== PP_Init =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM Classical

section Input

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

end Input

lemma gCond_ex (δ : ℝ) (N : ℕ) (hδ : 0 < δ) : ∃ k, gCond N δ k := by
  have he : 1 < 1 + δ / 4 := by linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (8 * (N : ℝ) * lamOf N δ * (1 + δ / 4)) he
  refine ⟨k, ?_⟩
  unfold gCond
  rw [one_div_mul_eq_div, le_div_iff₀ (by linarith)]
  linarith

lemma MOf_le_KG {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (hY : Function.Injective Y)
    (hδ : 0 < δ) (S : Finset (Fin N)) (hS : 2 ≤ S.card) : MOf Y δ S ≤ KG N δ + 1 := by
  have hr := rmedOf_pos' Y hY S hS
  have hex := ladder_exists Y δ S hδ hr
  have hg := gCond_ex δ N hδ
  rw [MOf_eq Y δ S hex]
  unfold KG; rw [dif_pos hg]
  have hle : Nat.find hex ≤ Nat.find hg := by
    apply Nat.find_min'
    have h1 : 8 * (N : ℝ) * lamOf N δ ≤ 1 / (1 + δ / 4) * (1 + δ / 4) ^ Nat.find hg := Nat.find_spec hg
    have hlam : 0 ≤ lamOf N δ := by unfold lamOf; positivity
    have hn : (S.card : ℝ) ≤ N := by
      exact_mod_cast (Finset.card_le_univ S).trans (by simp)
    have h2 : 8 * (S.card : ℝ) * lamOf N δ ≤ 1 / (1 + δ / 4) * (1 + δ / 4) ^ Nat.find hg :=
      le_trans (by gcongr) h1
    unfold bOf rhoOf
    calc 2 * (S.card : ℝ) * lamOf N δ * rmedOf Y S
        = rmedOf Y S / 4 * (8 * (S.card : ℝ) * lamOf N δ) := by ring
      _ ≤ rmedOf Y S / 4 * (1 / (1 + δ / 4) * (1 + δ / 4) ^ Nat.find hg) := by gcongr
      _ = rmedOf Y S / 2 / 2 * (1 + δ / 4) ^ Nat.find hg / (1 + δ / 4) := by ring
  omega

lemma clog_MOf_le {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (hY : Function.Injective Y)
    (hδ : 0 < δ) (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    Nat.clog 2 (MOf Y δ S - 1) ≤ T0G N δ := by
  unfold T0G
  exact Nat.clog_mono_right 2 (by have := MOf_le_KG Y δ hY hδ S hS; omega)

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

end DetANN.HPIM.PP

-- ===== PP_Run =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM Classical

/-- The final `RETURN` stores nothing. -/
lemma ret_halt_cw (Q : Program) (off KN : ℕ) (hE : Embeds Q (seg14 off KN) off) (s : State)
    (hpc : s.core.pc = off + 82) (hh : s.halted = false) (hc : s.integerMemory (s.core.ptrs 8) = 0) :
    cellsWritten Q s 4 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hc; subst hpc hh
  rw [cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Option.toFinset_none,
    Finset.empty_union]
  rw [cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Option.toFinset_none,
    Finset.empty_union]
  rw [cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell, Function.update_apply, Option.toFinset_none, Finset.empty_union]
  rw [if_pos (by simp [hc])]
  rw [cw_exec_at (i := 106) hE rfl rfl rfl]
  simp [wcell, cw_zero]

/-- A set of cells inside one integer and two real intervals. -/
lemma card_window (C : Finset (Bool × ℤ)) (a b c d e f : ℤ)
    (h : ∀ x ∈ C, (x.1 = false ∧ a ≤ x.2 ∧ x.2 < b) ∨
      (x.1 = true ∧ ((c ≤ x.2 ∧ x.2 < d) ∨ (e ≤ x.2 ∧ x.2 < f)))) :
    C.card ≤ (b - a).toNat + (d - c).toNat + (f - e).toNat := by
  have hsub : C ⊆ ((Finset.Ico a b).image (fun z => (false, z)) ∪
      (Finset.Ico c d).image (fun z => (true, z))) ∪ (Finset.Ico e f).image (fun z => (true, z)) := by
    intro x hx
    obtain ⟨x1, x2⟩ := x
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
    rcases h _ hx with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩ <;> simp only at h1 h2 <;> subst h1
    · exact Or.inl (Or.inl ⟨x2, h2, rfl, rfl⟩)
    · exact Or.inl (Or.inr ⟨x2, h2, rfl, rfl⟩)
    · exact Or.inr ⟨x2, h2, rfl, rfl⟩
  calc C.card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := add_le_add (Finset.card_union_le _ _) le_rfl
    _ ≤ (Finset.Ico a b).card + (Finset.Ico c d).card + (Finset.Ico e f).card :=
        add_le_add (add_le_add Finset.card_image_le Finset.card_image_le) Finset.card_image_le
    _ = _ := by rw [Int.card_Ico, Int.card_Ico, Int.card_Ico]

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

set_option maxHeartbeats 2000000 in
/-- **The preprocessing run**, for blocks meeting the child contracts and budgets that fit. -/
theorem pre_run (B : Blocks) (hB : B.WF) (ch : ChildOK B) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (KW KH KR WbI WbR : ℕ)
    (bu : Budgets Y δ (T0G N δ) B ch KW KH KR WbI WbR) :
    ∃ t, (run (Blocks.prog B) (inputState Y δ) detTape t).halted = true ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).work ≤
        79 + 4 * Nat.clog 2 N + 11 * N + 5 * KG N δ + 10 * T0G N δ +
          treePts Y (N + 1) Finset.univ * KW ∧
      ((cellsWritten (Blocks.prog B) (inputState Y δ) t).card : ℤ) ≤
        v0G N δ + 18 + Dn WbI N + (treePts Y (N + 1) Finset.univ : ℤ) * KH +
          (treePts Y (N + 1) Finset.univ : ℤ) * KR + WbR ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).integerMemory 1 = m ∧
      HTreeAt m (run (Blocks.prog B) (inputState Y δ) detTape t)
        ((run (Blocks.prog B) (inputState Y δ) detTape t).integerMemory 2) (hpimTree Y δ) := by
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  obtain ⟨t1, a1, a2, aG, a2', a13, a14, a8, a15, a16, a3, a7, aSL, a10, aw, acw⟩ :=
    init_spec Y δ B hB hN hδ
  set s1 := run (Blocks.prog B) (inputState Y δ) detTape t1 with hs1
  have hv0 : v0G N δ = Hbase N (T0G N δ) + N := rfl
  have hHb0 : (0 : ℤ) < Hbase N (T0G N δ) := by unfold Hbase; positivity
  have NS := node_spec Y δ (T0G N δ) (v0G N δ) B hB ch hm hY hδ hδ' KW KH KR WbI WbR bu (N + 1)
    Finset.univ (by omega) (by omega)
  obtain ⟨t2, b1, b2, bG, b8, b15l, b15u, b16l, b16u, bw, bcw, bS⟩ :=
    NS s1 (v0G N δ) (Hbase N (T0G N δ)) (-10) 0 (-10) (v0G N δ + 8) (1 + (N : ℤ) * m) a1 a2 aG a2' a13
      a14 a8 a15 a16 a3 (by rw [a7, hcard]) aSL le_rfl (by rw [hcard, hv0]) le_rfl le_rfl
      (by norm_num) le_rfl
  set s2 := run (Blocks.prog B) s1 detTape t2 with hs2
  rw [hcard] at bcw
  have hFP : s2.integerMemory (s2.core.ptrs 8) = 0 := by
    rw [b8, run_im_unwritten _ _ _ _ (fun hc => by
      rcases bcw _ hc with ⟨_, e | e | e⟩ | ⟨e, _⟩
      · simp only at e; omega
      · simp only at e; omega
      · simp only at e; omega
      · simp at e)]
    exact a10
  obtain ⟨c1, c2, c3, cw⟩ := ret_halt (Blocks.prog B) B.o14 B.lbl_NODE (emb14 B hB) s2 b1 b2 hFP
  have ccw := ret_halt_cw (Blocks.prog B) B.o14 B.lbl_NODE (emb14 B hB) s2 b1 b2 hFP
  set s3 := run (Blocks.prog B) s2 detTape 4 with hs3
  refine ⟨t1 + t2 + 4, ?_⟩
  have RR : run (Blocks.prog B) (inputState Y δ) detTape (t1 + t2 + 4) = s3 := by rw [run_add, run_add]
  have CW : cellsWritten (Blocks.prog B) (inputState Y δ) (t1 + t2 + 4) =
      cellsWritten (Blocks.prog B) (inputState Y δ) t1 ∪ cellsWritten (Blocks.prog B) s1 t2 ∪
        cellsWritten (Blocks.prog B) s2 4 := by
    rw [cellsWritten_add, cellsWritten_add, run_add]
  rw [RR, CW, ccw, Finset.union_empty]
  have hI2 : s3.integerMemory 2 = v0G N δ := by rw [c2]; exact bG.i2
  refine ⟨c1, ?_, ?_, by rw [c2]; exact bG.i1, ?_⟩
  · rw [cw]
    have := aw
    omega
  · have hwin := card_window (cellsWritten (Blocks.prog B) (inputState Y δ) t1 ∪
      cellsWritten (Blocks.prog B) s1 t2) (-10 - Dn WbI N) (s2.core.ptrs 15) (1 + (N : ℤ) * m)
      (s2.core.ptrs 16) (0 - WbR) 0 (by
        intro x hx
        simp only [Finset.mem_union] at hx
        rcases hx with hx | hx
        · obtain ⟨e1, e2, e3⟩ := acw x hx
          exact Or.inl ⟨e1, by omega, by omega⟩
        · rcases bcw x hx with ⟨e1, e | e | e⟩ | ⟨e1, e | e⟩
          · exact Or.inl ⟨e1, by omega, by omega⟩
          · exact Or.inl ⟨e1, by omega, by omega⟩
          · exact Or.inl ⟨e1, by omega, by omega⟩
          · exact Or.inr ⟨e1, Or.inl e⟩
          · exact Or.inr ⟨e1, Or.inr e⟩)
    have e1 : ((s2.core.ptrs 15 - (-10 - Dn WbI N)).toNat : ℤ) = s2.core.ptrs 15 + 10 + Dn WbI N := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have e2 : ((s2.core.ptrs 16 - (1 + (N : ℤ) * m)).toNat : ℤ) = s2.core.ptrs 16 - (1 + (N : ℤ) * m) := by
      rw [Int.toNat_of_nonneg (by omega)]
    have e3 : ((0 - (0 - (WbR : ℤ))).toNat : ℤ) = WbR := by simp
    have hwin' : ((cellsWritten (Blocks.prog B) (inputState Y δ) t1 ∪
        cellsWritten (Blocks.prog B) s1 t2).card : ℤ) ≤
        ((s2.core.ptrs 15 - (-10 - Dn WbI N)).toNat : ℤ) + ((s2.core.ptrs 16 - (1 + (N : ℤ) * m)).toNat : ℤ) +
          ((0 - (0 - (WbR : ℤ))).toNat : ℤ) := by exact_mod_cast hwin
    rw [e1, e2, e3] at hwin'
    linarith
  · rw [hI2]
    exact bS s3 (fun z _ _ => by rw [c2]) (fun z _ _ => by rw [c2]) (fun z _ _ => by rw [c3])

end DetANN.HPIM.PP

-- ===== PP_Budget =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM Classical

lemma bspFuel_mono {m n n' : ℕ} {δ : ℝ} (hδ : 0 < δ) (h : n ≤ n') : bspFuel n m δ ≤ bspFuel n' m δ := by
  unfold bspFuel
  have : (n : ℝ) * ((2 : ℝ) ^ 12 / (δ / 4)) ^ (2 * m) ≤ (n' : ℝ) * ((2 : ℝ) ^ 12 / (δ / 4)) ^ (2 * m) := by
    gcongr
  have := Nat.ceil_mono this
  omega

lemma bspFuel_le (n m : ℕ) {δ : ℝ} (hδ : 0 < δ) : bspFuel n m δ ≤ n * Gn m δ + 1 := by
  unfold bspFuel Gn
  have : ⌈(n : ℝ) * ((2 : ℝ) ^ 12 / (δ / 4)) ^ (2 * m)⌉₊ ≤ n * ⌈((2 : ℝ) ^ 12 / (δ / 4)) ^ (2 * m)⌉₊ :=
    Nat.ceil_le.2 (by push_cast; exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _))
  omega

lemma bspB_mono {m n n' : ℕ} {δ : ℝ} (hδ : 0 < δ) (h : n ≤ n') : bspB n m δ ≤ bspB n' m δ := by
  unfold bspB; have := bspFuel_mono (m := m) hδ h; omega

lemma bspB_le {m n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hn : 1 ≤ n) : bspB n m δ ≤ n * (2 * Gn m δ + 3) := by
  unfold bspB
  have := bspFuel_le n m hδ
  have e : n * (2 * Gn m δ + 3) = 2 * (n * Gn m δ) + 3 * n := by ring
  omega

section

variable {B : Blocks} (ch : ChildOK B)

lemma headW_mono {n n' m M M' : ℕ} (hn : n ≤ n') (hM : M ≤ M') : headW ch n m M ≤ headW ch n' m M' := by
  unfold headW
  have h1 : ch.Cm * (n + 1) ^ 5 * (m + 1) ≤ ch.Cm * (n' + 1) ^ 5 * (m + 1) := by gcongr
  have h2 := Nat.clog_mono_right 2 (show M - 1 ≤ M' - 1 by omega)
  omega

lemma lkW_mono {n n' m : ℕ} {δ : ℝ} (hδ : 0 < δ) (hn : n ≤ n') : lkW ch n m δ ≤ lkW ch n' m δ := by
  unfold lkW
  have hb := bspB_mono (m := m) hδ hn
  have h1 : (15 * n + 30) * m ≤ (15 * n' + 30) * m := by gcongr
  have h2 : ch.Cb * bspB n m δ ^ 2 * (n + 1) * (m + 1) ^ 2 ≤ ch.Cb * bspB n' m δ ^ 2 * (n' + 1) * (m + 1) ^ 2 := by
    gcongr
  have h3 : ch.Cbal * bspB n m δ ^ 2 * (m + 1) ≤ ch.Cbal * bspB n' m δ ^ 2 * (m + 1) := by gcongr
  omega

lemma midW_mono {n n' m : ℕ} (hn : n ≤ n') : midW ch n m ≤ midW ch n' m := by
  unfold midW
  have h1 : ch.Cc * (n + 1) ^ 3 * (m + 1) ≤ ch.Cc * (n' + 1) ^ 3 * (m + 1) := by gcongr
  omega

lemma lkD_mono {n n' m : ℕ} {δ : ℝ} (hδ : 0 < δ) (hn : n ≤ n') : lkD ch n m δ ≤ lkD ch n' m δ := by
  unfold lkD; exact Nat.mul_le_mul_left _ (bspB_mono hδ hn)

end

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

theorem budgets_ok (B : Blocks) (ch : ChildOK B) (hY : Function.Injective Y) (hδ : 0 < δ) :
    Budgets Y δ (T0G N δ) B ch (KWc ch N m δ) (KHc ch N m δ) (KRc ch N m δ) (WbIc ch N m δ)
      (WbRc ch N m δ) := by
  have hcard : ∀ S : Finset (Fin N), S.card ≤ N := fun S => (Finset.card_le_univ S).trans (by simp)
  have hM : ∀ S : Finset (Fin N), 2 ≤ S.card → MOf Y δ S ≤ MGG N δ :=
    fun S hS => MOf_le_KG Y δ hY hδ S hS
  refine ⟨?_, fun S hS => ?_, fun S hS => ?_, fun S hS => ?_, fun S hS => ?_, fun S hS => ?_,
    fun S hS => ?_, fun S hS => ?_, ?_, fun S hS => clog_MOf_le Y δ hY hδ S hS⟩
  · unfold KWc headW; omega
  · have hn := hcard S
    have h1 := headW_mono ch hn (hM S hS) (m := m)
    have h2 : MOf Y δ S * lkW ch S.card m δ ≤ MGG N δ * lkW ch N m δ :=
      Nat.mul_le_mul (hM S hS) (lkW_mono ch hδ hn)
    have h3 := midW_mono ch hn (m := m)
    have h4 : S.card * kidW S.card ≤ N * kidW N := Nat.mul_le_mul hn (by unfold kidW; omega)
    have h5 : KWc ch N m δ ≤ S.card * KWc ch N m δ := Nat.le_mul_of_pos_left _ (by omega)
    unfold KWc at h5 ⊢
    omega
  · have hb := bspB_le (m := m) hδ (show 1 ≤ S.card by omega)
    have hMS := hM S hS
    unfold lkH KHc
    have e1 : MOf Y δ S * (ch.Cbal * bspB S.card m δ + 6) ≤
        MGG N δ * (ch.Cbal * (S.card * (2 * Gn m δ + 3))) + 6 * MGG N δ := by
      have := Nat.mul_le_mul hMS (Nat.add_le_add_right (Nat.mul_le_mul_left ch.Cbal hb) 6)
      nlinarith
    have e2 : MGG N δ * (ch.Cbal * (S.card * (2 * Gn m δ + 3))) =
        S.card * (MGG N δ * (ch.Cbal * (2 * Gn m δ + 3))) := by ring
    have e3 : S.card * (MGG N δ * (ch.Cbal * (2 * Gn m δ + 3)) + 7 * MGG N δ + 19) =
        S.card * (MGG N δ * (ch.Cbal * (2 * Gn m δ + 3))) + S.card * (7 * MGG N δ) + 19 * S.card := by
      ring
    have e4 : 7 * MGG N δ ≤ S.card * (7 * MGG N δ) := Nat.le_mul_of_pos_left _ (by omega)
    rw [e3]
    omega
  · have hb := bspB_le (m := m) hδ (show 1 ≤ S.card by omega)
    have hMS := hM S hS
    unfold lkR KRc
    have e1 : 2 * m + ch.Cbal * bspB S.card m δ * m ≤ S.card * (2 * m + ch.Cbal * (2 * Gn m δ + 3) * m) := by
      have h1 : ch.Cbal * bspB S.card m δ * m ≤ ch.Cbal * (S.card * (2 * Gn m δ + 3)) * m := by gcongr
      have h2 : 2 * m ≤ S.card * (2 * m) := Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
    calc MOf Y δ S * (2 * m + ch.Cbal * bspB S.card m δ * m)
        ≤ MGG N δ * (S.card * (2 * m + ch.Cbal * (2 * Gn m δ + 3) * m)) := Nat.mul_le_mul hMS e1
      _ = S.card * (MGG N δ * (2 * m + ch.Cbal * (2 * Gn m δ + 3) * m)) := by ring
  · have := Nat.mul_le_mul_left ch.Cm (Nat.add_le_add_right (hcard S) 1)
    unfold WbIc; omega
  · have := Nat.mul_le_mul_left ch.Cc (Nat.add_le_add_right (hcard S) 1)
    unfold WbIc; omega
  · have := lkD_mono ch (m := m) hδ (hcard S); unfold WbIc; omega
  · exact lkD_mono ch hδ (hcard S)
  · unfold WbIc; omega

end DetANN.HPIM.PP

-- ===== PP_Final =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM Classical

/-- **The preprocessing program meets the bounds of `hpim_preprocessing`**, for blocks satisfying
the child contracts and given the `tree_points` bound. -/
theorem pre_spec (B : Blocks) (hB : B.WF) (ch : ChildOK B)
    (TP : ∀ {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)), Function.Injective Y →
      treePts Y (N + 1) Finset.univ ≤ 4 * N * (Nat.clog 2 N + 1)) :
    ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
      ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ t : ℕ,
          (run (Blocks.prog B) (inputState Y δ) detTape t).halted = true ∧
          ((run (Blocks.prog B) (inputState Y δ) detTape t).work : ℝ) ≤
            ((256 * 100000 * Acon ch : ℕ) : ℝ) * ((N : ℝ) + m) ^ 8 *
              ((2 : ℝ) ^ 14 / δ) ^ (((8 : ℕ) : ℝ) * m) * Real.log (N / δ) ^ 8 ∧
          ((cellsWritten (Blocks.prog B) (inputState Y δ) t).card : ℝ) ≤
            ((256 * 100000 * Acon ch : ℕ) : ℝ) * N *
              ((2 : ℝ) ^ 14 / δ) ^ (((8 : ℕ) : ℝ) * m) * Real.log (N / δ) ^ 8 ∧
          (run (Blocks.prog B) (inputState Y δ) detTape t).integerMemory 1 = m ∧
          HTreeAt m (run (Blocks.prog B) (inputState Y δ) detTape t)
            ((run (Blocks.prog B) (inputState Y δ) detTape t).integerMemory 2) (hpimTree Y δ) := by
  intro m N hm hN Y hY δ hδ hδ'
  obtain ⟨t, h1, hw, hc, hI, hT⟩ := pre_run Y δ B hB ch hm hN hY hδ hδ' _ _ _ _ _
    (budgets_ok Y δ B ch hY hδ)
  obtain ⟨b1, b2⟩ := pre_bounds ch hm hN δ hδ hδ' _ (TP Y hY)
  refine ⟨t, h1, ?_, ?_, hI, hT⟩
  · have hw2 : ((run (Blocks.prog B) (inputState Y δ) detTape t).work : ℝ) ≤
        ((79 + 4 * Nat.clog 2 N + 11 * N + 5 * KG N δ + 10 * T0G N δ +
          treePts Y (N + 1) Finset.univ * KWc ch N m δ : ℕ) : ℝ) := by exact_mod_cast hw
    exact hw2.trans b1
  · have hc2 : ((cellsWritten (Blocks.prog B) (inputState Y δ) t).card : ℝ) ≤
        (((v0G N δ + 18 + Dn (WbIc ch N m δ) N + (treePts Y (N + 1) Finset.univ : ℤ) * KHc ch N m δ +
          (treePts Y (N + 1) Finset.univ : ℤ) * KRc ch N m δ + WbRc ch N m δ : ℤ)) : ℝ) := by
      exact_mod_cast hc
    exact hc2.trans b2

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

lemma det_seg0 (off : ℕ) : DetProgram (seg0 off) := by
  apply det_of_good
  intro op hop
  unfold seg0 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_ladder (off : ℕ) : DetProgram (ladder off) := by
  apply det_of_good
  intro op hop
  unfold ladder at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg2 (off R : ℕ) : DetProgram (seg2 off R) := by
  apply det_of_good
  intro op hop
  unfold seg2 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg4 (off : ℕ) : DetProgram (seg4 off) := by
  apply det_of_good
  intro op hop
  unfold seg4 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg6 (off R : ℕ) : DetProgram (seg6 off R) := by
  apply det_of_good
  intro op hop
  unfold seg6 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg8 (off : ℕ) : DetProgram (seg8 off) := by
  apply det_of_good
  intro op hop
  unfold seg8 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg10 (off R : ℕ) : DetProgram (seg10 off R) := by
  apply det_of_good
  intro op hop
  unfold seg10 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg12 (off : ℕ) : DetProgram (seg12 off) := by
  apply det_of_good
  intro op hop
  unfold seg12 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg14 (off R : ℕ) : DetProgram (seg14 off R) := by
  apply det_of_good
  intro op hop
  unfold seg14 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

theorem det_prog (B : Blocks) (h1 : ∀ off, DetProgram (B.med off)) (h2 : ∀ off, DetProgram (B.comps off))
    (h3 : ∀ off, DetProgram (B.build off)) (h4 : ∀ off, DetProgram (B.bal off)) :
    DetProgram (Blocks.prog B) := by
  unfold Blocks.prog
  repeat' apply det_append
  all_goals first
    | exact det_seg0 _ | exact det_ladder _ | exact det_seg2 _ _ | exact det_seg4 _
    | exact det_seg6 _ _ | exact det_seg8 _ | exact det_seg10 _ _ | exact det_seg12 _
    | exact det_seg14 _ _ | exact h1 _ | exact h2 _ | exact h3 _ | exact h4 _

end DetANN.HPIM.PP

-- ===== PP_Top =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib DetANN DetANN.HPIM

theorem top : ∃ Pre : PNormReg.Program, DetProgram Pre ∧ ∃ C : ℝ, 1 < C ∧ ∃ K C' : ℕ,
      ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
        ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
          ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ t : ℕ,
            (PNormReg.run Pre (inputState Y δ) detTape t).halted = true ∧
            ((PNormReg.run Pre (inputState Y δ) detTape t).work : ℝ) ≤
              (C' : ℝ) * ((N : ℝ) + m) ^ K * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K ∧
            ((cellsWritten Pre (inputState Y δ) t).card : ℝ) ≤
              (C' : ℝ) * N * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K ∧
            (PNormReg.run Pre (inputState Y δ) detTape t).integerMemory 1 = m ∧
            HTreeAt m (PNormReg.run Pre (inputState Y δ) detTape t)
              ((PNormReg.run Pre (inputState Y δ) detTape t).integerMemory 2) (hpimTree Y δ) := by
  obtain ⟨med, Lm, Cm, hmB, hm⟩ := median_block
  obtain ⟨comps, Lc, Cc, hcB, hc⟩ := comps_block
  obtain ⟨bld, Lb, Cb, hbB, hb⟩ := build_block
  obtain ⟨bal, Lbal, Cbal, hbalB, hbal⟩ := balance_block
  let B : Blocks := ⟨med, comps, bld, bal, Lm, Lc, Lb, Lbal⟩
  have hWF : B.WF := ⟨fun off => (hmB off).1, fun off => (hcB off).1, fun off => (hbB off).1,
    fun off => (hbalB off).1⟩
  let ch : ChildOK B := ⟨Cm, Cc, Cb, Cbal, hm, hc, hb, hbal⟩
  refine ⟨Blocks.prog B, det_prog B (fun off => (hmB off).2) (fun off => (hcB off).2)
    (fun off => (hbB off).2) (fun off => (hbalB off).2), (2 : ℝ) ^ 14, by norm_num, 8,
    256 * 100000 * Acon ch, ?_⟩
  intro m N hm1 hN Y hY δ hδ hδ'
  exact pre_spec B hWF ch (fun Y hY => tree_points Y hY) m N hm1 hN Y hY δ hδ hδ'

end DetANN.HPIM.PP

open DetANN DetANN.HPIM PNormReg in
theorem solution :
    ∃ Pre : PNormReg.Program, DetProgram Pre ∧ ∃ C : ℝ, 1 < C ∧ ∃ K C' : ℕ,
      ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
        ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
          ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ t : ℕ,
            (PNormReg.run Pre (inputState Y δ) detTape t).halted = true ∧
            ((PNormReg.run Pre (inputState Y δ) detTape t).work : ℝ) ≤
              (C' : ℝ) * ((N : ℝ) + m) ^ K * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K ∧
            ((cellsWritten Pre (inputState Y δ) t).card : ℝ) ≤
              (C' : ℝ) * N * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K ∧
            (PNormReg.run Pre (inputState Y δ) detTape t).integerMemory 1 = m ∧
            HTreeAt m (PNormReg.run Pre (inputState Y δ) detTape t)
              ((PNormReg.run Pre (inputState Y δ) detTape t).integerMemory 2) (hpimTree Y δ) :=
  DetANN.HPIM.PP.top
