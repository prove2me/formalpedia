-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.quadNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:17:26.556612+00:00
-- url     : https://prove2.me/submissions/3812c016-5e33-4b86-9ee5-b6c1f4c50f3e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (K : IntermediateField ℚ E) (hK : Module.finrank ℚ K = 2) (σ : E ≃ₐ[ℚ] E) (β : K)
    (hβ : σ (β : E) ≠ β) (k : K) : ((Algebra.norm ℚ k : ℚ) : E) = (k : E) * σ (k : E) := by
  classical
  let φ0 : E →+* ℂ := Classical.arbitrary _
  let φ : E →ₐ[ℚ] ℂ := φ0.toRatAlgHom
  let τ1 : K →ₐ[ℚ] ℂ := φ.comp K.val
  let τ2 : K →ₐ[ℚ] ℂ := φ.comp ((σ : E →ₐ[ℚ] E).comp K.val)
  have hne : τ1 ≠ τ2 := by
    intro h
    have := DFunLike.congr_fun h β
    exact hβ (φ.injective this).symm
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {τ1, τ2} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, AlgHom.card, hK])).symm
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ k
  rw [huniv, Finset.prod_pair hne] at h1
  apply φ.injective
  rw [map_mul, map_ratCast]
  rw [eq_ratCast] at h1
  exact h1
end Formalism.HermitianLattices.StabilizerLevels.PfB
