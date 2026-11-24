-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.PsiNatEquivPf.norm_addChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:46.137803+00:00
-- url     : https://prove2.me/submissions/98d951fe-5754-49e3-9f17-10978c9e3d5b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCorePsiNatEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut Formalism.L2.SG.NormCut.PsiNatEquivPf
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace Formalism.L2.SG.NormCut.PsiNatEquivPf
theorem _root_.solution (ψ₀ : AddChar F ℂ) (a : F) : ‖ψ₀ a‖ = 1 := by

  have hpow : ψ₀ a ^ Fintype.card F = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  have hn : Fintype.card F ≠ 0 := Fintype.card_ne_zero
  have h2 : ‖ψ₀ a‖ ^ Fintype.card F = 1 := by
    rw [← norm_pow, hpow, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h2
end Formalism.L2.SG.NormCut.PsiNatEquivPf
