-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:33:06.956386+00:00
-- url     : https://prove2.me/submissions/32fc0484-c375-4716-ac60-2525fe8f98d8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_not_cm_eq_of_conj_smul_prime
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_atLeast

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
theorem _root_.solution (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ) (hr : r = 2 ∨ r = q)
    (𝔭 : Ideal (𝓞 (KinE ζ a b))) [𝔭.IsPrime] (hm𝔭 : ((r : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P) :
    cm (c • P) = 𝔭 ↔ ¬ cm P = 𝔭 := by
  have hrp : r.Prime := by
    rcases hr with rfl | rfl
    · exact Nat.prime_two
    · exact hH.1
  constructor
  · intro h2 h1
    exact not_cm_eq_of_conj_smul_prime hH h c hc r hr 𝔭 P hm h1 h2
  · intro h1
    exact (atLeast hH h c hc r hrp 𝔭 hm𝔭 P hm).resolve_left h1
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
