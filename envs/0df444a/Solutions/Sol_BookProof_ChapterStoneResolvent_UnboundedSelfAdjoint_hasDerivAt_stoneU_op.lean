-- Prove2me | solution 1 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_op
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:12:59.940357+00:00
-- url     : https://prove2.me/submissions/56439647-8160-42a4-9751-0f2abad60fcc

import Mathlib
import Definitions.Def_ChapterStoneGenerator
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_hasDerivAt_stoneU_const_sub
-- Generated from ChapterStoneGenerator.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_op
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace
open Filter Topology NormedSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


variable (T : UnboundedSelfAdjoint H)
theorem h42s_deriv_gen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint H) (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => T.stoneU s (x : H))
      ((-Complex.I) • T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩) t := by
  have h := BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub T x 0 (-t)
  have h2 := HasDerivAt.scomp t h (hasDerivAt_neg t)
  have e1 : ((fun r : ℝ => T.stoneU (0 - r) (x : H)) ∘ Neg.neg)
      = fun s : ℝ => T.stoneU s (x : H) := by
    funext s; simp
  rw [e1] at h2
  convert h2 using 1
  have e2 : (⟨T.stoneU (0 - -t) (x : H), T.stoneU_mem_domain (0 - -t) x⟩ : T.domain)
      = ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩ := by
    apply Subtype.ext; simp
  rw [e2]
  simp [neg_smul]

theorem solution (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => T.stoneU s (x : H))
      ((-Complex.I) • T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩) t := by
  exact h42s_deriv_gen T x t

