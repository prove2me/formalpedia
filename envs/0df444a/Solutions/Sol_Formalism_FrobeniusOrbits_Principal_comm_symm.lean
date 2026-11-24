-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.comm_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:43:40.410518+00:00
-- url     : https://prove2.me/submissions/a7d12e85-97e3-430b-8a3f-bf5090626d27

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
    (hc : ∀ (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)), σ (τ x) = τ (σ x))
    (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)) : σ.symm (τ x) = τ (σ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, hc, AlgEquiv.apply_symm_apply]
end Formalism.FrobeniusOrbits.Principal
