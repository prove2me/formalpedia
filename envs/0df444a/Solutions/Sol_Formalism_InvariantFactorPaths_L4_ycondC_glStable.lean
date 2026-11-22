-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.ycondC_glStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:23.269856+00:00
-- url     : https://prove2.me/submissions/46acb020-4bc0-4def-9443-290207a66a2f

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport

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
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Mt : WithTop ℤ) :
    GlStableC p LL j Cs (YCondC p LL j Cs Mt) := by
  intro c hc d hd x hx
  have hle : YCondC p LL j Cs Mt ≤ (YCondC p LL j Cs Mt).comap (glAct p LL j c d) := by
    unfold YCondC
    apply sSup_le
    rintro S ⟨h1, hS⟩ y hy
    exact (le_sSup (show S ∈ {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) |
      S ≤ restrictSupport ℚ_[p] {m | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧ GlStableC p LL j Cs S} from ⟨h1, hS⟩))
      (hS c hc d hd y hy)
  exact hle hx
end Formalism.InvariantFactorPaths.L4
