-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.sum_of_two_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:05:07.669446+00:00
-- url     : https://prove2.me/submissions/86d07d8d-8b4a-485d-8962-95a5e466ecd7

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
theorem _root_.solution : SumTwoUnits := by
  unfold SumTwoUnits
  intro R _ _ ⟨x, y, z, hxy, hyz, hxz⟩ a
  have key : ∃ t : IsLocalRing.ResidueField R, t ≠ 0 ∧ t ≠ IsLocalRing.residue R a := by
    by_contra hcon
    push_neg at hcon
    have h : ∀ t, t = 0 ∨ t = IsLocalRing.residue R a := fun t => by
      by_cases ht : t = 0
      · exact Or.inl ht
      · exact Or.inr (hcon t ht)
    rcases h x with hx | hx <;> rcases h y with hy | hy <;> rcases h z with hz | hz <;> simp_all
  obtain ⟨t, ht0, hta⟩ := key
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective t
  have hu : IsUnit u := by rwa [← IsLocalRing.residue_ne_zero_iff_isUnit]
  have hv : IsUnit (a - u) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub]
    exact sub_ne_zero.2 (Ne.symm hta)
  exact ⟨hu.unit, hv.unit, by simp⟩
end Formalism.HermitianLattices.IntegralLatticeDensity
