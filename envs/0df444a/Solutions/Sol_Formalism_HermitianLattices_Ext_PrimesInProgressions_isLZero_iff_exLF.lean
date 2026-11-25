-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.isLZero_iff_exLF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:34.801114+00:00
-- url     : https://prove2.me/submissions/3096b64a-5210-4178-b257-db21fbcf9bdf

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
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
theorem _root_.solution (χ : DirichletCharacter ℂ M) (s : ℂ) : IsLZero χ s ↔ exLF χ s = 0 := by
  unfold IsLZero
  by_cases hs : s = 1
  · subst hs
    constructor
    · rintro ⟨h1, h2⟩
      exact absurd h2 (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 (by simp))
    · intro h; exact absurd h (exLF_one_ne_zero χ)
  · rw [exLF_eq_zero_iff χ hs]
    exact ⟨fun h => h.2, fun h => ⟨Or.inr hs, h⟩⟩
end Formalism.HermitianLattices.Ext.PrimesInProgressions
