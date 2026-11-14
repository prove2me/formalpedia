-- Prove2me | solution 1 for GenCountSampleLLL.insertion_output_row_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:02:08.874287+00:00
-- url     : https://prove2.me/submissions/e8b4b1c6-c5cd-46ca-8bd4-b1267889752e

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal
open GenCountSampleLLL

private theorem dirac_sum_state (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (s : I.St) (hs : s ∈ I.states D.card D a) :
    (∑ Y : I.S D a, I.dirac s Y.1) = 1 := by
  let s' : I.S D a := ⟨s,hs⟩
  have heq (Y : I.S D a) : (Y.1 = s) ↔ Y = s' := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  simp only [Inst.dirac, heq]
  simp

private theorem output_state_assignment_good (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (σ : I.Assign) (X : I.S D a) (hX : X.1 = ⟨[], Inst.Base.out σ⟩) :
    σ ∈ I.Good D := by
  have hstate := X.2
  rw [hX] at hstate
  cases hc : D.card with
  | zero => simp [hc, Inst.states] at hstate
  | succ k =>
    rw [hc, Inst.states] at hstate
    simp only [Finset.mem_union] at hstate
    rcases hstate with ((((hi | ho) | ht) | hl) | hin)
    · obtain ⟨τ,hτ,he⟩ := Finset.mem_image.mp hi
      have hh := congrArg Inst.St.base he
      cases hh
    · obtain ⟨τ,hτ,he⟩ := Finset.mem_image.mp ho
      have hh := congrArg Inst.St.base he
      simp only [Inst.Base.out.injEq] at hh
      simpa [hh] using hτ
    · obtain ⟨T,hT,hm⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨τ,hτ,he⟩ := Finset.mem_image.mp hm
      have hh := congrArg Inst.St.base he
      cases hh
    · obtain ⟨T,hT,hm⟩ := Finset.mem_biUnion.mp hl
      obtain ⟨z,hz,hm⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨τ,hτ,he⟩ := Finset.mem_image.mp hm
      have hh := congrArg Inst.St.base he
      cases hh
    · obtain ⟨T,hT,hm⟩ := Finset.mem_biUnion.mp hin
      obtain ⟨z,hz,hm⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨Y,hY,he⟩ := Finset.mem_image.mp hm
      have hh := congrArg Inst.St.labels he
      cases hh

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (X : I.S D a)
    (hX : X.1 = ⟨[], Inst.Base.out σ⟩) :
    (∀ Y : I.S D a, 0 ≤ I.Pker D a X Y) ∧
      (∑ Y : I.S D a, I.Pker D a X Y) = 1 := by
  have hgood : σ ∈ I.Good D := output_state_assignment_good I D a σ X hX
  have hσ : σ ∈ I.Good (D.erase a) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro b hb
    exact (Finset.mem_filter.mp hgood).2 b (Finset.mem_erase.mp hb).2
  have hinput : (⟨[], Inst.Base.inp σ⟩ : I.St) ∈ I.states D.card D a := by
    have hD : 0 < D.card := Finset.card_pos.mpr ⟨a,ha⟩
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
    rw [hk, Inst.states]
    simp [hσ]
  have houtput : (⟨[], Inst.Base.out σ⟩ : I.St) ∈ I.states D.card D a := by
    have hv := X.2
    rwa [hX] at hv
  have hi := dirac_sum_state I D a _ hinput
  have ho := dirac_sum_state I D a _ houtput
  constructor
  · intro Y
    simp only [Inst.Pker, hX, Inst.stepRule, Inst.baseRule, Inst.dirac]
    split_ifs <;> positivity
  · simp only [Inst.Pker, hX, Inst.stepRule, Inst.baseRule]
    rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    simp_rw [Finset.sum_add_distrib]
    rw [ho, hi]
    simp
    norm_num
