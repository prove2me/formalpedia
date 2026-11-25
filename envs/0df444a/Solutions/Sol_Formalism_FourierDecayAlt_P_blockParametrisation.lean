-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.blockParametrisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:47:51.839824+00:00
-- url     : https://prove2.me/submissions/844afba6-c40d-4f78-a7a8-8f33cc4031eb

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.Param := by
  intro K _ m t c u' a b hu w hw
  have hdet : IsUnit ((t : K) • u').det := by
    rw [Matrix.det_smul, isUpUni_det _ hu, mul_one]; exact (t.isUnit.pow _)
  constructor
  · rw [fromBlocks_multiply, fromBlocks_multiply]
    have h1 : a * w * ((t : K) • u') * ((t : K) • u')⁻¹ * ((t : K) • b) = a * w * ((t : K) • b) := by
      rw [Matrix.mul_assoc (a * w), Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    rw [h1]
    congr 1 <;> simp [Matrix.mul_assoc, add_comm]
  · intro i hi
    have hi0 : ∀ j : Fin m, j ≠ i → u' j i = 0 := by
      intro j hj
      apply hu.1
      have : i.val < j.val := by
        have : j.val ≠ i.val := fun h => hj (Fin.ext h)
        omega
      exact this
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.smul_apply, hu.2 i, Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
      · subst hw; simp [mul_comm]
      · intro k _ hk; subst hw
        have : i ≠ Fin.rev k := fun h => hk (by rw [h, Fin.rev_rev])
        simp [this]
      · simp
    · intro j _ hj; rw [Matrix.smul_apply, hi0 j hj]; simp
    · simp
end Formalism.FourierDecayAlt.P
