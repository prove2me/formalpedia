-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.isoC_glStableC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:49.733176+00:00
-- url     : https://prove2.me/submissions/47af17a6-62c8-4683-9745-066bac4a613d

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) (c : Fin r) (hc : c ∈ Cs)
    (d : Fin r) (hd : d ∈ Cs) :
    ∀ x ∈ IsoC p LL j Cs la, glAct p LL j c d x ∈ IsoC p LL j Cs la := by
  intro x hx
  rw [IsoC, Submodule.mem_sInf] at hx ⊢
  intro S hS
  exact hS.2 c hc d hd x (hx S hS)
end Formalism.InvariantFactorPaths.L4
