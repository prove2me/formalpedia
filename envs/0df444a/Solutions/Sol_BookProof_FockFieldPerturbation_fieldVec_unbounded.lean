-- Prove2me | solution 1 for BookProof.FockFieldPerturbation.fieldVec_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:39:42.362693+00:00
-- url     : https://prove2.me/submissions/730de90b-2714-4658-b2a4-8df76f1dc4c3

-- Generated from ChapterFockFieldPerturbation.lean — solution of BookProof.FockFieldPerturbation.fieldVec_unbounded
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
import Theorems.Thm_BookProof_FockFieldPerturbation_annVec_apply
import Theorems.Thm_BookProof_FockFieldPerturbation_fieldVec_apply
import Theorems.Thm_BookProof_FockOneParticleGap_norm_toLp_sq
import Theorems.Thm_BookProof_FockSecondQuantization_annA_apply
import Theorems.Thm_BookProof_FockSecondQuantization_creA_apply
import Theorems.Thm_BookProof_FockSecondQuantization_creVec_apply
import Theorems.Thm_BookProof_FockSecondQuantization_dn_up
import Theorems.Thm_BookProof_FockSecondQuantization_up_self
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockFieldPerturbation



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.FockSecondQuantization

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (C : ℝ) :
    ∃ u : FockAlg, ‖toLp u‖ = 1 ∧ C ≤ ‖toLp (fieldVec (Finsupp.single k 1) u)‖ := by

  classical
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2)
  set al : Conf := Finsupp.single k n with hal
  set u : FockAlg := Finsupp.single al 1 with hu
  have halk : al k = n := by simp [hal]
  have husupp : u.support = {al} := Finsupp.support_single_ne_zero al one_ne_zero
  have hval : u al = 1 := by simp [hu]
  have hu1 : ‖toLp u‖ = 1 := by
    have h : ‖toLp u‖ ^ 2 = 1 := by
      rw [norm_toLp_sq, husupp, Finset.sum_singleton, hval]
      simp
    have hx : (0 : ℝ) ≤ ‖toLp u‖ := norm_nonneg _
    have hfac : (‖toLp u‖ - 1) * (‖toLp u‖ + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h2
    · linarith
    · linarith
  refine ⟨u, hu1, ?_⟩
  set v : FockAlg := fieldVec (Finsupp.single k (1 : ℂ)) u with hv
  have hsupp : (Finsupp.single k (1 : ℂ)).support = {k} :=
    Finsupp.support_single_ne_zero k one_ne_zero
  have hvsplit : v = creA k u + annA k u := by
    rw [hv, fieldVec_apply, creVec_apply, annVec_apply, hsupp]
    simp
  have hupk : (up k al) k = n + 1 := by rw [up_self, halk]
  have hne : up k (up k al) ≠ al := by
    intro hcontra
    have := congrArg (fun β : Conf => β k) hcontra
    simp only [up_self, halk] at this
    omega
  have hcoord : v (up k al) = ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) := by
    rw [hvsplit, Finsupp.add_apply, creA_apply, annA_apply, dn_up, hupk]
    have h2 : u (up k (up k al)) = 0 := by
      simp [hu, Ne.symm hne]
    rw [hval, h2, mul_zero, add_zero, mul_one]
    push_cast
    ring_nf
  have hcoordne : v (up k al) ≠ 0 := by
    rw [hcoord]
    have : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    simpa using ne_of_gt this
  have hmem : up k al ∈ v.support := Finsupp.mem_support_iff.mpr hcoordne
  have hge : (n : ℝ) + 1 ≤ ‖toLp v‖ ^ 2 := by
    rw [norm_toLp_sq]
    have hterm : ‖v (up k al)‖ ^ 2 = (n : ℝ) + 1 := by
      rw [hcoord]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (by positivity)]
    calc (n : ℝ) + 1 = ‖v (up k al)‖ ^ 2 := hterm.symm
      _ ≤ ∑ β ∈ v.support, ‖v β‖ ^ 2 :=
          Finset.single_le_sum (f := fun β => ‖v β‖ ^ 2) (fun _ _ => sq_nonneg _) hmem
  have hvn : (0 : ℝ) ≤ ‖toLp v‖ := norm_nonneg _
  nlinarith [sq_nonneg C]
