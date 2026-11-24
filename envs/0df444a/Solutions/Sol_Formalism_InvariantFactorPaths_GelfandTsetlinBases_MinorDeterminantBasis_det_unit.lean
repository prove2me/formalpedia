-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis.det_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:55:26.711129+00:00
-- url     : https://prove2.me/submissions/c2089445-8fc2-4ac7-adcc-7f912b278594

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_MinorDeterminantBasis_rows_indep

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
variable {σ X : Type} [Fintype X] [DecidableEq X]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
theorem _root_.solution (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m)
    (hp : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      LinearIndependent (ZMod p) fun x => MvPolynomial.map (Int.castRingHom (ZMod p)) (F x)) :
    IsUnit (cmat m F).det := by
  rw [Int.isUnit_iff_natAbs_eq]
  by_contra hne
  obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact p.Prime := ⟨hpp⟩
  have hrows := rows_indep m hm F hF (ZMod p) (hp p ⟨hpp⟩)
  have hu : IsUnit ((cmat m F).map (Int.castRingHom (ZMod p))) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp (by simpa [Matrix.row] using hrows)
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
  apply hu
  have hdet : ((cmat m F).map (Int.castRingHom (ZMod p))).det = Int.castRingHom (ZMod p) (cmat m F).det :=
    (RingHom.map_det _ _).symm
  rw [hdet, eq_intCast]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (Int.ofNat_dvd_left.mpr hpd)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
