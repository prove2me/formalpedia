-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.eichlerTransformProperties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:32.312236+00:00
-- url     : https://prove2.me/submissions/d04f9f5b-646e-4849-8d98-4b03a4f0cd36

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : EichlerFacts := by
  intro R V _ _ _ _ h hh u σ τ huu huσ hτ
  have hσu : h σ u = 0 := by rw [hh u σ, huσ, star_zero]
  have hE : ∀ (σ' : V) (τ' : R) (y : V),
      Formalism.HermitianLatticeCounting.LatticeSumBounds.eichler h u σ' τ' y = y - h y σ' • u + h y u • σ' - (τ' * h y u) • u :=
    fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hxu hxσ
    rw [hE, hxu, hxσ]; simp
  · intro p x' hpu hx'u hx'σ
    rw [hE]
    simp [hpu, hx'u, hx'σ]
  · intro x
    refine ⟨-(h x σ) - τ * h x u, ?_⟩
    rw [hE]; module
  · intro x
    have hyu : h (Formalism.HermitianLatticeCounting.LatticeSumBounds.eichler h u σ τ x) u = h x u := by
      rw [hE]
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, huu, hσu, mul_zero, sub_zero, add_zero]
    have hyσ : h (Formalism.HermitianLatticeCounting.LatticeSumBounds.eichler h u σ τ x) σ = h x σ + h x u * h σ σ := by
      rw [hE]
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, huσ, mul_zero, sub_zero, add_zero]
    rw [hE (-σ) (star τ) (Formalism.HermitianLatticeCounting.LatticeSumBounds.eichler h u σ τ x), map_neg, hyσ, hyu, hE σ τ x, ← hτ]
    module
end Formalism.HermitianLatticeCounting.P
