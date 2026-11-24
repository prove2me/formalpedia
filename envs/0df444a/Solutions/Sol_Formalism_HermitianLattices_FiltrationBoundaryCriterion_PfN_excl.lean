-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.excl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:32:27.536949+00:00
-- url     : https://prove2.me/submissions/d9caec34-9454-4f89-a742-c4f8c4fde8a9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_int_mem_of_cm

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
theorem _root_.solution (r s : ℕ) (hrs : Nat.Coprime r s) (𝔭 : Ideal (𝓞 (KinE ζ a b)))
    (hs : ((s : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭)
    (P : Ideal (𝓞 (hostE ζ a b))) [hP : P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P) :
    cm P ≠ 𝔭 := by
  intro h1
  have hs' := int_mem_of_cm P 𝔭 h1 s hs
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hrs)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have : (1 : 𝓞 (hostE ζ a b)) = (u : 𝓞 (hostE ζ a b)) * ((r : ℤ) : 𝓞 (hostE ζ a b)) +
      (v : 𝓞 (hostE ζ a b)) * ((s : ℤ) : 𝓞 (hostE ζ a b)) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 (hostE ζ a b)) huv.symm
  rw [this]
  exact P.add_mem (P.mul_mem_left _ hm) (P.mul_mem_left _ hs')
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
