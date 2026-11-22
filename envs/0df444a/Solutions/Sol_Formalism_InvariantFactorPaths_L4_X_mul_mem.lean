-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.X_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:11.191429+00:00
-- url     : https://prove2.me/submissions/d4f42d51-1a26-4b06-939b-b3b4fd0624d4

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {σ : Type} (v : σ) (Q : Set (σ →₀ ℕ)) (g : MvPolynomial σ ℚ_[p]) :
    X v * g ∈ restrictSupport ℚ_[p] Q ↔ g ∈ restrictSupport ℚ_[p] {m | Finsupp.single v 1 + m ∈ Q} := by
  rw [mem_restrictSupport_iff, mem_restrictSupport_iff, support_X_mul, Finset.coe_map,
    Set.image_subset_iff]
  exact Iff.rfl
end Formalism.InvariantFactorPaths.L4
