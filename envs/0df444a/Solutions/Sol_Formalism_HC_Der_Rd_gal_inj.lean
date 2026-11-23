-- Prove2me | solution 1 for Formalism.HC.Der.Rd.gal_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:15.402104+00:00
-- url     : https://prove2.me/submissions/80cff84d-4f09-4498-822c-d3c555b41979

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Theorems.Thm_Formalism_HC_Der_Rd_adjoin_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial ArithmeticFunction
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ N) (E : Type*) [Field E] [NumberField E] [Algebra E L]
include hζ
namespace Formalism.HC.Der.Rd
theorem _root_.solution : Function.Injective fun σ : L ≃ₐ[E] L => σ ζ := by
  intro σ τ h
  have := AlgHom.ext_of_adjoin_eq_top (adjoin_top hζ E)
    (φ₁ := (σ : L →ₐ[E] L)) (φ₂ := (τ : L →ₐ[E] L)) (by simpa using h)
  exact AlgEquiv.coe_algHom_injective this
end Formalism.HC.Der.Rd
