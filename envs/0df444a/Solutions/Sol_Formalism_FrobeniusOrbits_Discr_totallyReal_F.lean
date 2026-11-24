-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.totallyReal_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:40.717886+00:00
-- url     : https://prove2.me/submissions/ca35d237-8c9c-4626-b57d-b1047d83af4a

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_real_theta
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_real_on_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.Discr
variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}
variable [IsCyclotomicExtension {2 ^ (e + 2)} ℚ K]
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution (hz : IsPrimitiveRoot z (2 ^ (e + 2))) : IsTotallyReal ℚ⟮z + z⁻¹⟯ := by
  have hm : 2 ^ (e + 2) ≠ 0 := by positivity
  refine ⟨fun v => ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  refine RingHom.ext fun y => ?_
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  letI : Algebra ℚ⟮z + z⁻¹⟯ ℂ := v.embedding.toAlgebra
  let Φ : K →ₐ[ℚ⟮z + z⁻¹⟯] ℂ := IsAlgClosed.lift
  have h1 := real_on_adjoin (z + z⁻¹) (Φ : K →+* ℂ) (real_theta hm hz (Φ : K →+* ℂ)) (y : K) y.2
  have h2 : (Φ : K →+* ℂ) (y : K) = v.embedding y := Φ.commutes y
  rw [h2] at h1
  exact h1
end Formalism.FrobeniusOrbits.Discr
