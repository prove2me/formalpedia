-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.isoC_keepC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:57:02.754143+00:00
-- url     : https://prove2.me/submissions/fc3fddf0-201a-41da-8094-7a19147066e9

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_hwc_keepC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_isoC_glStableC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_hwc_le_isoCC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x)) :
    ∀ x ∈ IsoC p LL j Cs la, Q x ∈ IsoC p LL j Cs la := by
  intro x hx
  have hle : IsoC p LL j Cs la ≤ (IsoC p LL j Cs la).comap Q := by
    apply sInf_le
    refine ⟨fun y hy => ?_, fun c hc d hd y hy => ?_⟩
    · exact hwc_le_isoCC LL j Cs la (hwc_keepC LL j Cs la Q hQ y hy)
    · show Q (glAct p LL j c d y) ∈ IsoC p LL j Cs la
      rw [hQ c hc d hd]
      exact isoC_glStableC LL j Cs la c hc d hd _ hy
  exact hle hx
end Formalism.InvariantFactorPaths.L4
