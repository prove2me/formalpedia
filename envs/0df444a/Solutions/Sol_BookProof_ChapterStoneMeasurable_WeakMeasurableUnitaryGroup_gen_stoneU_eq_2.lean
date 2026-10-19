-- Prove2me | solution 2 for BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:20:31.701254+00:00
-- url     : https://prove2.me/submissions/7ab07896-12ab-44d1-a3cf-a712f3168492

import Mathlib
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneUnitary
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_hasDerivAt_stoneU_const_sub
-- Generated from ChapterStoneConverse.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)
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

theorem h42s_gen_eq_dom {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (G : BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup H) (t : ℝ) (x : G.genDomain) :
    G.gen.stoneU t (x : H) = G.U t (x : H) := by
  let w : ℝ → G.genDomain := fun s =>
    (⟨G.gen.stoneU s (x : H), G.gen.stoneU_mem_domain s x⟩ : G.genDomain) -
      ⟨G.U s (x : H), G.apply_mem_genDomain s x⟩
  have hv : ∀ s, HasDerivAt (fun r : ℝ => G.gen.stoneU r (x : H) - G.U r (x : H))
      ((-Complex.I) • G.genOp (w s)) s := by
    intro s
    have h1 := h42s_deriv_gen G.gen x s
    have h2 := G.hasDerivAt_orbit x s
    rw [← G.genOp_apply_comm] at h2
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    simp only [w, map_sub, smul_sub]
    rfl
  have hw : ∀ s, ((w s : G.genDomain) : H) = G.gen.stoneU s (x : H) - G.U s (x : H) := fun s => rfl
  have hphi : ∀ s, HasDerivAt
      (fun r : ℝ => ⟪G.gen.stoneU r (x : H) - G.U r (x : H), G.gen.stoneU r (x : H) - G.U r (x : H)⟫_ℂ)
      0 s := by
    intro s
    have h := (hv s).inner ℂ (hv s)
    refine h.congr_deriv ?_
    rw [← hw s, inner_smul_right, inner_smul_left, G.symmetric (w s) (w s)]
    simp
  have hc := is_const_of_deriv_eq_zero (fun s => (hphi s).differentiableAt) (fun s => (hphi s).deriv) t 0
  simp only [BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_zero, G.map_zero,
    sub_self, inner_zero_left] at hc
  rw [inner_self_eq_zero, sub_eq_zero] at hc
  exact hc

theorem solution (t : ℝ) : G.gen.stoneU t = G.U t := by
  apply DFunLike.coe_injective
  refine Continuous.ext_on G.denseDomain (G.gen.stoneU t).continuous (G.U t).continuous ?_
  intro y hy
  exact h42s_gen_eq_dom G t ⟨y, hy⟩

