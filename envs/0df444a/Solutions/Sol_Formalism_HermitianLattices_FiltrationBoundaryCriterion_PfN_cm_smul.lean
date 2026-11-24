-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.cm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:48.383862+00:00
-- url     : https://prove2.me/submissions/51097819-e679-429e-a6fa-f37c3ec5f5c5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_fixK
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
open NumberField IntermediateField Ideal
open scoped Pointwise
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ ∈ Psi e)
    (P : Ideal (𝓞 (hostE ζ a b))) : cm (σ • P) = cm P := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : σ⁻¹ • algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) x =
      algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) x := by
    apply RingOfIntegers.ext
    exact fixK (e := e) σ⁻¹ (by rw [galE_inv hqd h]; exact (Psi e).inv_mem hσ) (x : KinE ζ a b)
  rw [this]
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
