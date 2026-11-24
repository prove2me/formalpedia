-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.nf_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:53:27.819068+00:00
-- url     : https://prove2.me/submissions/19220022-d296-499b-894b-951531a9240f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions

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
open Ideal UniqueFactorizationMonoid
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
theorem _root_.solution {S : Type*} [CommRing S] [IsDedekindDomain S] (I : Ideal S) (hI : I ≠ ⊥)
    (f : Ideal S ≃* Ideal S) : normalizedFactors (f I) = (normalizedFactors I).map f := by
  have h1 : ∀ P ∈ (normalizedFactors I).map f, Prime P := by
    intro P hP
    obtain ⟨P', hP', rfl⟩ := Multiset.mem_map.mp hP
    exact (MulEquiv.prime_iff f).mpr (prime_of_normalized_factor P' hP')
  have h2 : ((normalizedFactors I).map f).prod = f I := by
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
  have h3 := normalizedFactors_prod_of_prime h1
  rw [h2] at h3
  exact h3
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
