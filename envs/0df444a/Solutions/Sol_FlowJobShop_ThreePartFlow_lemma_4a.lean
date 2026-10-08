-- Prove2me | solution 1 for FlowJobShop.ThreePartFlow.lemma_4a
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:51:57.88739+00:00
-- url     : https://prove2.me/submissions/cf02780f-fbaf-4acd-9f66-eef4c9509906

import Mathlib
import Definitions.Def_FlowJobShop_ThreePartFlow_FlowShop
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_FlowJobShop_ThreePartFlow_Instance

open ResourceScheduling.Chain
open FlowJobShop.ThreePartFlow.FlowShop


namespace FlowJobShop.ThreePartFlow

def fjOffs (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t) (j : Fin (3 * C.t)) : ℕ :=
  ∑ j' ∈ Finset.univ.filter (fun j' => j' < j ∧ σ j' = σ j), C.a j'

theorem fj_offs_add_le (C : ThreePartition)  (σ : Fin (3 * C.t) → Fin C.t)
    (hσ : C.IsSolution σ) (j : Fin (3 * C.t)) : fjOffs C σ j + C.a j ≤ C.b := by
  have h1 : j ∉ Finset.univ.filter (fun j' => j' < j ∧ σ j' = σ j) := by simp
  have h2 : insert j (Finset.univ.filter (fun j' => j' < j ∧ σ j' = σ j)) ⊆
      Finset.univ.filter (fun j' => σ j' = σ j) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨_, h⟩ <;> simp [*]
  have := Finset.sum_le_sum_of_subset (f := C.a) h2
  rw [Finset.sum_insert h1] at this
  have h3 := (hσ (σ j)).2
  unfold fjOffs
  omega

theorem fj_offs_mono (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t)
    (j j' : Fin (3 * C.t)) (hlt : j < j') (hs : σ j = σ j') :
    fjOffs C σ j + C.a j ≤ fjOffs C σ j' := by
  have h1 : j ∉ Finset.univ.filter (fun x => x < j ∧ σ x = σ j) := by simp
  have h2 : insert j (Finset.univ.filter (fun x => x < j ∧ σ x = σ j)) ⊆
      Finset.univ.filter (fun x => x < j' ∧ σ x = σ j') := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨h, h'⟩
    · exact ⟨hlt, hs⟩
    · exact ⟨lt_trans h hlt, h'.trans hs⟩
  have := Finset.sum_le_sum_of_subset (f := C.a) h2
  rw [Finset.sum_insert h1] at this
  unfold fjOffs
  omega

/-- block index of task j of job i -/
def fBlk (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t) (j : Fin 3) : FSJob C.t → ℕ
  | .elem i => if j.val = 1 then 0 else if j.val = 0 then 2 * (σ i).val else 2 * (σ i).val + 1
  | .first => if j.val = 1 then 0 else 2
  | .middle k => if j.val = 0 then 2 * k.val + 1 else if j.val = 1 then 2 * k.val + 2
      else 2 * k.val + 4
  | .last => if j.val = 0 then 2 * C.t - 3 else 2 * C.t - 2
  | .tail3 => 0
  | .tail1 => 2 * C.t - 1

/-- width in blocks -/
def fWid (C : ThreePartition) (j : Fin 3) (_ : FSJob C.t) : ℕ := if j.val = 1 then 2 else 1

def fOff (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t) (j : Fin 3) : FSJob C.t → ℕ
  | .elem i => if j.val = 1 then 0 else fjOffs C σ i
  | _ => 0

noncomputable def fSt (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t) (j : Fin 3)
    (i : FSJob C.t) : ℝ := (C.b : ℝ) * (fBlk C σ j i : ℝ) + (fOff C σ j i : ℝ)

theorem fOff_add_le (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t) (hσ : C.IsSolution σ)
    (j : Fin 3) (i : FSJob C.t) :
    (fOff C σ j i : ℝ) + (FS C).t j i ≤ (C.b : ℝ) * (fWid C j i : ℝ) := by
  have hb : (0:ℝ) ≤ C.b := by positivity
  cases i with
  | elem i =>
    have h := fj_offs_add_le C σ hσ i
    have h' : ((fjOffs C σ i : ℕ) : ℝ) + (C.a i : ℝ) ≤ (C.b : ℝ) := by exact_mod_cast h
    fin_cases j <;> simp [fOff, fWid, FS, fsTime] <;> nlinarith
  | first => fin_cases j <;> simp [fOff, fWid, FS, fsTime] <;> nlinarith
  | middle k => fin_cases j <;> simp [fOff, fWid, FS, fsTime] <;> nlinarith
  | last => fin_cases j <;> simp [fOff, fWid, FS, fsTime] <;> nlinarith
  | tail3 => fin_cases j <;> simp [fOff, fWid, FS, fsTime] <;> nlinarith
  | tail1 => fin_cases j <;> simp [fOff, fWid, FS, fsTime] <;> nlinarith

theorem blk_wid_le (C : ThreePartition) (ht : 2 ≤ C.t) (σ : Fin (3 * C.t) → Fin C.t) (j : Fin 3)
    (i : FSJob C.t) (h : (FS C).t j i ≠ 0) : fBlk C σ j i + fWid C j i ≤ 2 * C.t := by
  cases i with
  | elem i =>
    have := (σ i).isLt
    fin_cases j <;> simp [fBlk, fWid, FS, fsTime] at h ⊢ <;> omega
  | first => fin_cases j <;> simp [fBlk, fWid, FS, fsTime] at h ⊢ <;> omega
  | middle k =>
    have := k.isLt
    fin_cases j <;> simp [fBlk, fWid, FS, fsTime] at h ⊢ <;> omega
  | last => fin_cases j <;> simp [fBlk, fWid, FS, fsTime] at h ⊢ <;> omega
  | tail3 => fin_cases j <;> simp [fBlk, fWid, FS, fsTime] at h ⊢ <;> omega
  | tail1 => fin_cases j <;> simp [fBlk, fWid, FS, fsTime] at h ⊢ <;> omega


theorem blk_sep (C : ThreePartition) (ht : 2 ≤ C.t) (σ : Fin (3 * C.t) → Fin C.t) (j : Fin 3)
    (i i' : FSJob C.t) (hne : i ≠ i') (h : (FS C).t j i ≠ 0) (h' : (FS C).t j i' ≠ 0) :
    fBlk C σ j i + fWid C j i ≤ fBlk C σ j i' ∨ fBlk C σ j i' + fWid C j i' ≤ fBlk C σ j i ∨
      (∃ g g', i = FSJob.elem g ∧ i' = FSJob.elem g' ∧ σ g = σ g' ∧ j ≠ 1) := by
  rcases i with g | _ | k | _ | _ | _ <;> rcases i' with g' | _ | k' | _ | _ | _ <;>
    first
    | (exfalso; exact hne rfl)
    | skip
  all_goals
    try have := (σ g).isLt
  all_goals
    try have := (σ g').isLt
  all_goals
    try have := k.isLt
  all_goals
    try have := k'.isLt
  all_goals first
    | (by_cases hs : σ g = σ g'
       · right; right; refine ⟨g, g', rfl, rfl, hs, ?_⟩
         intro hj; subst hj; simp [FS, fsTime] at h
       · have : (σ g).val ≠ (σ g').val := fun e => hs (Fin.ext e)
         fin_cases j <;> simp [fBlk, fWid, FS, fsTime] at h h' ⊢ <;> omega)
    | (have hk : k.val ≠ k'.val := fun e => hne (by rw [Fin.ext e])
       fin_cases j <;> simp [fBlk, fWid, FS, fsTime] at h h' ⊢ <;> omega)
    | (fin_cases j <;> simp [fBlk, fWid, FS, fsTime] at h h' ⊢ <;> omega)

theorem blk_prec (C : ThreePartition) (ht : 2 ≤ C.t) (σ : Fin (3 * C.t) → Fin C.t) (j j' : Fin 3)
    (hjj : j < j') (i : FSJob C.t) (h : (FS C).t j i ≠ 0) (h' : (FS C).t j' i ≠ 0) :
    fBlk C σ j i + fWid C j i ≤ fBlk C σ j' i := by
  have := (σ (match i with | .elem g => g | _ => ⟨0, by omega⟩)).isLt
  rcases i with g | _ | k | _ | _ | _ <;>
  · try have := (σ g).isLt
    try have := k.isLt
    fin_cases j <;> fin_cases j' <;> simp [fBlk, fWid, FS, fsTime] at h h' hjj ⊢ <;> omega


theorem fSt_end_le (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t) (hσ : C.IsSolution σ)
    (j : Fin 3) (i : FSJob C.t) :
    fSt C σ j i + (FS C).t j i ≤ (C.b : ℝ) * ((fBlk C σ j i + fWid C j i : ℕ) : ℝ) := by
  have := fOff_add_le C σ hσ j i
  unfold fSt
  push_cast
  linarith

theorem fSt_ge (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t) (j : Fin 3) (i : FSJob C.t) :
    (C.b : ℝ) * (fBlk C σ j i : ℝ) ≤ fSt C σ j i := by
  unfold fSt
  have : (0:ℝ) ≤ (fOff C σ j i : ℝ) := by positivity
  linarith

theorem fSt_nonneg (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t) (j : Fin 3) (i : FSJob C.t) :
    0 ≤ fSt C σ j i := by
  have := fSt_ge C σ j i
  have : (0:ℝ) ≤ (C.b : ℝ) * (fBlk C σ j i : ℝ) := by positivity
  linarith

theorem end_le_of_blk (C : ThreePartition) (hC : C.Valid) (σ : Fin (3 * C.t) → Fin C.t)
    (hσ : C.IsSolution σ) (j j' : Fin 3) (i i' : FSJob C.t)
    (h : fBlk C σ j i + fWid C j i ≤ fBlk C σ j' i') :
    fSt C σ j i + (FS C).t j i ≤ fSt C σ j' i' := by
  have h1 := fSt_end_le C σ hσ j i
  have h2 := fSt_ge C σ j' i'
  have hb : (0:ℝ) < C.b := by exact_mod_cast hC.1
  have h3 : ((fBlk C σ j i + fWid C j i : ℕ) : ℝ) ≤ (fBlk C σ j' i' : ℝ) := by exact_mod_cast h
  nlinarith

open Classical in
noncomputable def fSched (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t)
    (σ : Fin (3 * C.t) → Fin C.t) (hσ : C.IsSolution σ) : PreemptiveSchedule (FS C) where
  pieces j i := if (FS C).t j i = 0 then ∅ else {(fSt C σ j i, fSt C σ j i + (FS C).t j i)}
  start_nonneg := by
    intro j i p hp
    by_cases h : (FS C).t j i = 0
    · simp [h] at hp
    · simp only [h, if_false, Finset.mem_singleton] at hp
      subst hp; exact fSt_nonneg C σ j i
  start_lt_end := by
    intro j i p hp
    by_cases h : (FS C).t j i = 0
    · simp [h] at hp
    · simp only [h, if_false, Finset.mem_singleton] at hp
      subst hp
      have := (FS C).t_nonneg j i
      have : 0 < (FS C).t j i := lt_of_le_of_ne this (Ne.symm h)
      simp only; linarith
  disjoint := by
    intro j i i' p p' hp hp' hne
    by_cases h : (FS C).t j i = 0
    · simp [h] at hp
    by_cases h' : (FS C).t j i' = 0
    · simp [h'] at hp'
    simp only [h, h', if_false, Finset.mem_singleton] at hp hp'
    subst hp; subst hp'
    have hii : i ≠ i' := by
      rintro rfl; exact hne rfl
    rcases blk_sep C ht σ j i i' hii h h' with h1 | h1 | ⟨g, g', rfl, rfl, hs, hj⟩
    · left; exact end_le_of_blk C hC σ hσ j j i i' h1
    · right; exact end_le_of_blk C hC σ hσ j j i' i h1
    · have hgg : g ≠ g' := fun e => hii (by rw [e])
      have hblk : fBlk C σ j (FSJob.elem g) = fBlk C σ j (FSJob.elem g') := by
        simp [fBlk, hs]
      have ht1 : (FS C).t j (FSJob.elem g) = (C.a g : ℝ) := by
        fin_cases j <;> simp [FS, fsTime] at hj ⊢
      have ht2 : (FS C).t j (FSJob.elem g') = (C.a g' : ℝ) := by
        fin_cases j <;> simp [FS, fsTime] at hj ⊢
      have hoff : ∀ x, fOff C σ j (FSJob.elem x) = fjOffs C σ x := by
        intro x; simp [fOff]; intro h1; exact absurd (by omega) hj
      rcases lt_or_gt_of_ne hgg with hl | hl
      · left
        have := fj_offs_mono C σ g g' hl hs
        have : ((fjOffs C σ g : ℕ) : ℝ) + (C.a g : ℝ) ≤ (fjOffs C σ g' : ℕ) := by exact_mod_cast this
        unfold fSt; rw [hblk, hoff, hoff, ht1]; linarith
      · right
        have := fj_offs_mono C σ g' g hl hs.symm
        have : ((fjOffs C σ g' : ℕ) : ℝ) + (C.a g' : ℝ) ≤ (fjOffs C σ g : ℕ) := by exact_mod_cast this
        unfold fSt; rw [hblk, hoff, hoff, ht2]; linarith
  total_length := by
    intro j i
    by_cases h : (FS C).t j i = 0
    · simp [h]
    · simp [h]
  precedence := by
    intro i j j' hjj p hp p' hp'
    by_cases h : (FS C).t j i = 0
    · simp [h] at hp
    by_cases h' : (FS C).t j' i = 0
    · simp [h'] at hp'
    simp only [h, h', if_false, Finset.mem_singleton] at hp hp'
    subst hp; subst hp'
    exact end_le_of_blk C hC σ hσ j j' i i (blk_prec C ht σ j j' hjj i h h')

theorem fSched_nonpre (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t)
    (σ : Fin (3 * C.t) → Fin C.t) (hσ : C.IsSolution σ) : (fSched C hC ht σ hσ).IsNonPreemptive := by
  intro j i
  unfold fSched
  simp only
  split_ifs <;> simp

theorem fSched_ft (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t)
    (σ : Fin (3 * C.t) → Fin C.t) (hσ : C.IsSolution σ) :
    (fSched C hC ht σ hσ).finishTime ≤ tau C := by
  have hb : (0:ℝ) < C.b := by exact_mod_cast hC.1
  have htau : 0 ≤ tau C := by unfold tau; positivity
  unfold PreemptiveSchedule.finishTime
  rw [Finset.fold_max_le]
  refine ⟨htau, fun i _ => ?_⟩
  unfold PreemptiveSchedule.jobFinish
  rw [Finset.fold_max_le]
  refine ⟨htau, fun p hp => ?_⟩
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
  obtain ⟨j, hj⟩ := hp
  by_cases h : (FS C).t j i = 0
  · simp [fSched, h] at hj
  · simp only [fSched, h, if_false, Finset.mem_singleton] at hj
    subst hj
    have h1 := fSt_end_le C σ hσ j i
    have h2 := blk_wid_le C ht σ j i h
    have h3 : ((fBlk C σ j i + fWid C j i : ℕ) : ℝ) ≤ ((2 * C.t : ℕ) : ℝ) := by exact_mod_cast h2
    have h4 := mul_le_mul_of_nonneg_left h3 hb.le
    unfold tau
    push_cast at h4 h1 ⊢
    linarith

theorem lemma4a_core (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t) (hsol : C.HasSolution) :
    ∃ S : PreemptiveSchedule (FS C), S.IsNonPreemptive ∧ S.finishTime ≤ tau C := by
  obtain ⟨σ, hσ⟩ := hsol
  exact ⟨fSched C hC ht σ hσ, fSched_nonpre C hC ht σ hσ, fSched_ft C hC ht σ hσ⟩

end FlowJobShop.ThreePartFlow

open FlowJobShop.ThreePartFlow


theorem solution (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t) (hsol : C.HasSolution) :
    ∃ S : PreemptiveSchedule (FS C), S.IsNonPreemptive ∧ S.finishTime ≤ tau C := by
  exact lemma4a_core C hC ht hsol
