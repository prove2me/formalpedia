-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.lift_of_types
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:06:15.417808+00:00
-- url     : https://prove2.me/submissions/998c3612-00cc-4b63-8a08-bced28ea2b43

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : LiftTypes := by
  unfold LiftTypes
  intro U A _ _ ι n χ m e M M' hχ hm
  have hz : ∀ (f : A →* ℂˣ) (k : ℤ) (x : A), (f ^ k) x = (f x) ^ k := fun _ _ _ => rfl
  refine ⟨fun z => ?_, fun z => ?_, fun lam lam' ν h1 h2 => by omega⟩
  · have h1 : (m * χ ^ (-M')) (ι z) = χ (ι z) ^ (e - M') := by
      rw [MonoidHom.mul_apply, hz, hm]
      group
    refine ⟨h1, ?_⟩
    rw [h1, hχ]
    group
  · have h1 : (m⁻¹ * χ ^ M) (ι z) = χ (ι z) ^ (-(e - M)) := by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hz, hm]
      group
    refine ⟨h1, ?_⟩
    rw [h1, hχ]
    group
end Formalism.HermitianLattices.IntegralLatticeDensity
