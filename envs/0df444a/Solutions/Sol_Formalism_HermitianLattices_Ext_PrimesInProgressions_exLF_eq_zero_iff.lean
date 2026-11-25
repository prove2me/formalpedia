-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:59.210699+00:00
-- url     : https://prove2.me/submissions/51f93798-ad90-4608-bb9a-f768b8ae2b8d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_of_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_char_apply

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
theorem _root_.solution (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) :
    exLF χ s = 0 ↔ DirichletCharacter.LFunction χ s = 0 := by
  by_cases h : χ = 1
  · subst h; rw [exLF_one_char_apply hs, mul_eq_zero]
    exact ⟨fun h => h.resolve_left (sub_ne_zero_of_ne hs), Or.inr⟩
  · rw [exLF_of_ne h]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
