-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exOrd_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:14.499745+00:00
-- url     : https://prove2.me/submissions/28736b1d-7b7a-4e1a-b90c-6b09569c349c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
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
theorem _root_.solution (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0) (hd : deriv (exLF χ) ρ ≠ 0) :
    exOrd χ ρ = 1 := by
  unfold exOrd analyticOrderNatAt
  rw [(exLF_analyticAt χ ρ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hd]
  rfl
end Formalism.HermitianLattices.Ext.PrimesInProgressions
