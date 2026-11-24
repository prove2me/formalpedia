-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.hwc_keepC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:49:17.923733+00:00
-- url     : https://prove2.me/submissions/c8e5185d-5c16-46d4-932b-b1bbe9006964

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_comm_wtspC
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x)) :
    ∀ x ∈ HWC p LL j Cs la, Q x ∈ HWC p LL j Cs la := by
  intro x hx
  simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  refine ⟨comm_wtspC LL j Cs Q (fun c hc y => hQ c hc c hc y) la x h1, fun c d hcd => ?_⟩
  rw [← hQ c hcd.1 d hcd.2.1, h2 c d hcd, map_zero]
end Formalism.InvariantFactorPaths.L4
