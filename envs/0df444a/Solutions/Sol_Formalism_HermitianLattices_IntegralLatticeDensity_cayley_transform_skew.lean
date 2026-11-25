-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.cayley_transform_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:51.168841+00:00
-- url     : https://prove2.me/submissions/5f11ce44-7f26-4ebb-944e-a9c6e70bd17d

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
theorem _root_.solution : CayleySkew := by
  unfold CayleySkew
  intro E V _ _ _ h g θ hadd hherm hg hθ y y'
  have hsub1 : ∀ x x' z, h (x - x') z = h x z - h x' z := fun x x' z => by
    have := hadd (x - x') x' z
    rw [sub_add_cancel] at this
    exact eq_sub_of_add_eq this.symm
  have hsub2 : ∀ z x x', h z (x - x') = h z x - h z x' := fun z x x' => by
    rw [hherm z (x - x'), hsub1, star_sub, ← hherm, ← hherm]
  have h1 : h y (y' - g y') + h (y - g y) y' = h (y - g y) (y' - g y') := by
    simp only [hsub1, hsub2, hg]
    ring
  refine ⟨h1, ?_⟩
  rw [star_sub, star_mul, ← hherm, ← hherm]
  have hθ' : star θ = 1 - θ := by
    rw [← hθ]
    ring
  rw [hθ']
  linear_combination h1
end Formalism.HermitianLattices.IntegralLatticeDensity
