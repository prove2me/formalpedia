-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_re_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:06.315261+00:00
-- url     : https://prove2.me/submissions/c894cf06-60ea-4e18-affa-31361e929257

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_isLZero_iff_exLF

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
theorem _root_.solution (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : exLF χ s = 0) : s.re < 1 := by
  by_contra hlt
  obtain ⟨h1, h2⟩ := (isLZero_iff_exLF χ s).2 hs
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 (not_lt.1 hlt) h2
end Formalism.HermitianLattices.Ext.PrimesInProgressions
