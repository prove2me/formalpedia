-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.off_diagonal_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:23.755121+00:00
-- url     : https://prove2.me/submissions/b47f0dac-5baa-45f7-a62e-f68cead4fd44

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensDiv
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensBlock
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_offdiag_term
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_zero_spacing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution : Offdiag := by
  intro M _ S σ T U hU hT hσ hS hsp p hp
  classical
  have hU0 : (0 : ℝ) ≤ U := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hterm := fun p' (hp' : p' ∈ S) =>
    offdiag_term σ T U hU hT hσ p p' (hS p hp) (hS p' hp') (hsp p hp p' hp')
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq' S p, if_pos hp,
    ← sum_filter, ← mul_sum]
  set Fib : Finset (DirichletCharacter ℂ M × ℂ) := S.filter (fun p' => p'.1 = p.1) with hFib
  set P : Finset ℝ := Fib.image (fun p' => p'.2.im) with hP
  have hinj : Set.InjOn (fun p' : DirichletCharacter ℂ M × ℂ => p'.2.im) (Fib : Set _) := by
    intro a ha b hb hab
    have ha' := mem_filter.1 (mem_coe.1 ha)
    have hb' := mem_filter.1 (mem_coe.1 hb)
    by_contra hne
    have := hsp a ha'.1 b hb'.1 hne (ha'.2.trans hb'.2.symm)
    simp only at hab
    rw [hab, sub_self, abs_zero] at this
    linarith
  have hpF : p ∈ Fib := mem_filter.2 ⟨hp, rfl⟩
  have htP : p.2.im ∈ P := mem_image_of_mem _ hpF
  have hsp' := (zero_spacing P T (by linarith)
    (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      exact (hS a (mem_filter.1 ha).1).2.2)
    (by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hy
      have ha' := mem_filter.1 ha
      have hb' := mem_filter.1 hb
      exact hsp a ha'.1 b hb'.1 (fun h => hxy (by rw [h])) (ha'.2.trans hb'.2.symm))).2 _ htP
  have hsumeq : ∑ p' ∈ Fib, 1 / |p.2.im - p'.2.im| = ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| := by
    rw [← add_zero (∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x|)]
    have h0 : (0 : ℝ) = 1 / |p.2.im - p.2.im| := by simp
    rw [h0, sum_erase_add P _ htP, hP, sum_image hinj]
  rw [hsumeq]
  have hc0 : (0 : ℝ) ≤ S.card := by positivity
  have hB0 : 0 ≤ ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have h1 : 4 * (U : ℝ) * ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| ≤
      4 * (U : ℝ) * (2 * (1 + Real.log (2 * T + 1))) := by gcongr
  have h2 : (S.card : ℝ) * (4 * ((M : ℝ) + 1) * (2 + 2 * T)) ≤
      (S.card : ℝ) * (8 * ((M : ℝ) + 1) * (2 + 2 * T)) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    nlinarith
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
