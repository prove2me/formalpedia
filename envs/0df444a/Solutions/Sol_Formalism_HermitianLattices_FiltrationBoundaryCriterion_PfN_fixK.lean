-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.fixK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:12:10.395571+00:00
-- url     : https://prove2.me/submissions/fd1db083-7796-49e8-960f-36886f5a501c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_mem_Psi_iff


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
theorem _root_.solution (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ ∈ Psi e)
    (x : KinE ζ a b) : σ (x : hostE ζ a b) = x := by
  rw [galE_mem_Psi_iff] at hσ
  have : (σ : hostE ζ a b →ₐ[ℚ] hostE ζ a b).comp (KinE ζ a b).val = (KinE ζ a b).val := by
    refine algHom_ext_of_eq_adjoin ℚ (S := KinE ζ a b) (s := {bE ζ a b}) rfl ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hσ
  exact DFunLike.congr_fun this x
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
