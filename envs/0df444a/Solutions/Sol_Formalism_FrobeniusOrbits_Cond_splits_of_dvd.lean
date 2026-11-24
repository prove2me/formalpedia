-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.splits_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:17.920897+00:00
-- url     : https://prove2.me/submissions/5bccbe5a-66b8-46e0-87ec-316f3469687b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq

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
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {L K : Type*} [Field L] [Field K] [Algebra ℚ L] [Algebra ℚ K] (x : L)
    (f : ℚ[X]) (hf : f ≠ 0) (hx : aeval x f = 0) (hs : (f.map (algebraMap ℚ K)).Splits) :
    IsIntegral ℚ x ∧ ((minpoly ℚ x).map (algebraMap ℚ K)).Splits := by
  have hi : IsIntegral ℚ x := by
    exact IsAlgebraic.isIntegral ⟨f, hf, hx⟩
  refine ⟨hi, ?_⟩
  have hd : (minpoly ℚ x).map (algebraMap ℚ K) ∣ f.map (algebraMap ℚ K) :=
    Polynomial.map_dvd _ (minpoly.dvd ℚ x hx)
  have hf0 : f.map (algebraMap ℚ K) ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ K).injective).mpr hf
  exact hs.of_dvd hf0 hd
end Formalism.FrobeniusOrbits.Cond
