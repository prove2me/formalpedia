-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:23.218881+00:00
-- url     : https://prove2.me/submissions/b1f775b5-de30-4050-ac69-bdbfb69998da

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_of_hom
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_comp_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace LeadAt
theorem _root_.solution {ι : Type*} {w : σ → M} (T : Finset ι) (v : ι → M) (t : ι → MvPolynomial σ R)
    (ht : ∀ m ∈ T, IsWeightedHomogeneous w (t m) (v m)) (top : ι) (htop : top ∈ T)
    (hlt : ∀ m ∈ T, m ≠ top → v m < v top) : LeadAt w (v top) (∑ m ∈ T, t m) (t top) := by
  classical
  refine ⟨fun e he => ?_, ?_⟩
  · rw [mem_support_iff, coeff_sum] at he
    obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    rw [ht m hm hne]
    by_cases hmt : m = top
    · rw [hmt]
    · exact (hlt m hm hmt).le
  · rw [map_sum, Finset.sum_eq_single top]
    · exact (Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.of_hom (ht top htop)).2
    · intro m hm hmt
      exact (Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.of_hom (ht m hm)).comp_eq_zero (hlt m hm hmt)
    · intro h
      exact absurd htop h
end LeadAt
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
