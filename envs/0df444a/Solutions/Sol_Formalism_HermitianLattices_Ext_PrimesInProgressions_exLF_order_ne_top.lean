-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_order_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:55.401586+00:00
-- url     : https://prove2.me/submissions/d29d0f81-82cb-4dbd-b800-adf4baeaee32

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_analyticAt

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
theorem _root_.solution (χ : DirichletCharacter ℂ M) (ρ : ℂ) : analyticOrderAt (exLF χ) ρ ≠ ⊤ := by
  intro h
  have := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ (exLF_analyticAt χ)).1 h
  exact exLF_one_ne_zero χ (by rw [this]; rfl)
end Formalism.HermitianLattices.Ext.PrimesInProgressions
