-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_deriv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:23.874125+00:00
-- url     : https://prove2.me/submissions/facdb700-ca14-4fb9-ae03-b2a7f57dc08b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_of_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_char
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
variable {M : ℕ} [NeZero M]
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0)
    (hd : deriv (DirichletCharacter.LFunction χ) ρ ≠ 0) : deriv (exLF χ) ρ ≠ 0 := by
  by_cases h : χ = 1
  · subst h
    have hs : ρ ≠ 1 := by
      rintro rfl; exact exLF_one_ne_zero _ hρ
    have hL := (exLF_eq_zero_iff _ hs).1 hρ
    rw [exLF_one_char, DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one M hs]
    simp only [DirichletCharacter.LFunctionTrivChar]
    rw [hL, add_zero]
    exact mul_ne_zero (sub_ne_zero_of_ne hs) hd
  · rw [exLF_of_ne h]; exact hd
end Formalism.HermitianLattices.Ext.PrimesInProgressions
