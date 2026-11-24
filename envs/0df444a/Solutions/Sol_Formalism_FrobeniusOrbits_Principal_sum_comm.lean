-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.sum_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:43:41.900696+00:00
-- url     : https://prove2.me/submissions/3efe0ae3-2051-4f53-a452-2b097ad6427a

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
open Formalism.FrobeniusOrbits.Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Principal
theorem _root_.solution (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b))
    (hc : ∀ (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)), σ (τ x) = τ (σ x)) (w : (hostE ζ a b)) :
    σ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ w) = ∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (σ w) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun τ _ => hc τ w
end Formalism.FrobeniusOrbits.Principal
