-- Prove2me | solution 1 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_op
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:13:42.229097+00:00
-- url     : https://prove2.me/submissions/6cb8551c-3dff-46f8-932b-d70411d7f2bd

import Mathlib
import Definitions.Def_ChapterStoneGenerator
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_hasDerivAt_stoneU_const_sub
-- Generated from ChapterStoneGenerator.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_op
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

theorem h42s_op0 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint H) (x : T.domain) :
    T.op ⟨T.stoneU 0 (x : H), T.stoneU_mem_domain 0 x⟩ = T.op x := by
  have e2 : (⟨T.stoneU 0 (x : H), T.stoneU_mem_domain 0 x⟩ : T.domain) = x := by
    apply Subtype.ext; simp
  rw [e2]

theorem h42s_op {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint H) (t : ℝ) (x : T.domain) :
    T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩ = T.stoneU t (T.op x) := by
  have h1 := h42s_deriv_gen T x t
  have h0 : HasDerivAt (fun s : ℝ => T.stoneU (s - t) (x : H))
      ((-Complex.I) • T.op x) t := by
    have h00 := h42s_deriv_gen T x 0
    rw [h42s_op0] at h00
    exact HasDerivAt.comp_sub_const (f := fun s : ℝ => T.stoneU s (x : H)) t t (by rw [sub_self]; exact h00)
  have h3 := HasFDerivAt.comp_hasDerivAt t (((T.stoneU t).restrictScalars ℝ).hasFDerivAt) h0
  have e1 : (((T.stoneU t).restrictScalars ℝ) ∘ fun s : ℝ => T.stoneU (s - t) (x : H)) = fun s : ℝ => T.stoneU s (x : H) := by
    funext s; simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']; rw [T.stoneU_apply_stoneU]; congr 2; ring
  rw [e1] at h3
  have hu := h1.unique h3
  rw [ContinuousLinearMap.coe_restrictScalars', map_smul] at hu
  exact smul_right_injective H (by simp : (-Complex.I) ≠ 0) hu

theorem solution (t : ℝ) (x : T.domain) :
    T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩ = T.stoneU t (T.op x) := by
  exact h42s_op T t x

