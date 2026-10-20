-- Prove2me | solution 1 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genDomain_eq_domain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:23:37.239366+00:00
-- url     : https://prove2.me/submissions/ab864de4-5bf6-4479-9d4f-f8fa36e54cbc

-- Generated from ChapterStoneTheorem.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genDomain_eq_domain
import Mathlib
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_hasDerivAt_stoneU_zero
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint in
theorem solution (T : UnboundedSelfAdjoint H) :
    T.stoneGroup.genDomain = T.domain := by 
  apply le_antisymm
  · intro y hy
    refine T.mem_domain_of_inner (eta := T.stoneGroup.genOp ⟨y, hy⟩) ?_
    intro psi
    have hpsi : (psi : H) ∈ T.stoneGroup.genDomain :=
      (BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero T psi).differentiableAt
    have hgen : T.stoneGroup.genOp ⟨psi, hpsi⟩ = T.op psi := by
      have hd := (BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero T psi).deriv
      show Complex.I • deriv (fun t : ℝ => T.stoneU t (psi : H)) 0 = T.op psi
      rw [hd, smul_smul]
      simp
    have := BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.symmetric T.stoneGroup ⟨psi, hpsi⟩ ⟨y, hy⟩
    rw [← hgen]
    exact this
  · intro x hx
    exact (BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero T ⟨x, hx⟩).differentiableAt
