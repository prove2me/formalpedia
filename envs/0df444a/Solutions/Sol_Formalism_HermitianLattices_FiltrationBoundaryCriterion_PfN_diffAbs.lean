-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.diffAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:32:15.379398+00:00
-- url     : https://prove2.me/submissions/f9f30f0d-bb9f-41c5-b604-b633dc626020

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_diffQuad
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_bE_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_bE_mem_KinE
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HF_P_adjoin_top_of_lift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
open NumberField IntermediateField Ideal
open scoped Pointwise
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
theorem _root_.solution : DiffAbs := by
  intro e q d hH L _ _ ζ a b h
  have hsq : bE ζ a b ^ 2 = -(d : hostE ζ a b) := DiscrB.bE_sq h
  let x : KinE ζ a b := ⟨bE ζ a b, Principal.bE_mem_KinE ζ a b⟩
  have hx : x ^ 2 = -(d : KinE ζ a b) := by
    apply Subtype.ext
    simpa [x] using hsq
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx]
    exact (isIntegral_natCast d).neg
  have hadj : IntermediateField.adjoin ℚ {x} = ⊤ := by
    apply Formalism.HF.P.adjoin_top_of_lift
    rw [Set.image_singleton]
    rfl
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 (KinE ζ a b), (β : KinE ζ a b) = x := ⟨⟨x, hint⟩, rfl⟩
  have hK := diffQuad (KinE ζ a b) d hH.2.1 (by have := hH.2.2.2.1; omega) x hx hadj β hβ
  refine ⟨algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) β, ?_, ?_⟩
  · show (((β : KinE ζ a b)) : hostE ζ a b) = bE ζ a b
    rw [hβ]
  · rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)),
      hK, Ideal.map_span, Set.image_singleton]
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
