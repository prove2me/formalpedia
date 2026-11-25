-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.trivial_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:30:56.204526+00:00
-- url     : https://prove2.me/submissions/804d0289-9801-4739-a49e-4e598b51a90e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_zero_spacing
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_space_card_char_le

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
theorem _root_.solution : Triv := by
  intro M _ T S hT hS hsp
  classical
  have hfib : ∀ χ : DirichletCharacter ℂ M, ((S.filter (fun p => p.1 = χ)).card : ℝ) ≤ 2 * T + 1 := by
    intro χ
    set F := S.filter (fun p => p.1 = χ) with hF
    have hinj : Set.InjOn (fun p : DirichletCharacter ℂ M × ℂ => p.2.im) F := by
      intro p hp p' hp' h
      by_contra hne
      rw [hF, coe_filter] at hp hp'
      have := hsp p hp.1 p' hp'.1 hne (hp.2.trans hp'.2.symm)
      simp only at h
      rw [h, sub_self, abs_zero] at this
      linarith
    have hsp' := (zero_spacing (F.image (fun p => p.2.im)) T hT
      (fun x hx => by
        rw [mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact hS p (mem_of_mem_filter _ hp))
      (fun x hx y hy hne => by
        rw [mem_image] at hx hy
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨p', hp', rfl⟩ := hy
        have hpp : p ≠ p' := fun h => hne (by rw [h])
        rw [hF, mem_filter] at hp hp'
        exact hsp p hp.1 p' hp'.1 hpp (hp.2.trans hp'.2.symm))).1
    rwa [card_image_of_injOn hinj] at hsp'
  have hsum : (S.card : ℝ) = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)),
      ((S.filter (fun p => p.1 = χ)).card : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := fun p : DirichletCharacter ℂ M × ℂ => p.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast; rfl
  rw [hsum]
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)), ((S.filter (fun p => p.1 = χ)).card : ℝ)
      ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)), (2 * T + 1) := sum_le_sum (fun χ _ => hfib χ)
    _ = ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) * (2 * T + 1) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) * (2 * T + 1) := mul_le_mul_of_nonneg_right (space_card_char_le M) (by linarith)
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
