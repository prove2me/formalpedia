-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.negLD_eq_exLF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:49:52.944873+00:00
-- url     : https://prove2.me/submissions/b24ca1d4-58c9-4799-b390-aec069ec01d0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_of_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_char
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_char_apply
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
theorem _root_.solution (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) (h0 : exLF χ s ≠ 0) :
    negLD χ s = (if χ = 1 then 1 / (s - 1) else 0) - deriv (exLF χ) s / exLF χ s := by
  unfold negLD
  by_cases h : χ = 1
  · subst h
    have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s ≠ 0 :=
      fun hz => h0 ((exLF_eq_zero_iff _ hs).2 hz)
    have hs1 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs
    rw [if_pos rfl, exLF_one_char_apply hs, exLF_one_char,
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one M hs]
    simp only [DirichletCharacter.LFunctionTrivChar]
    field_simp
    ring
  · rw [if_neg h, exLF_of_ne h, zero_sub]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
