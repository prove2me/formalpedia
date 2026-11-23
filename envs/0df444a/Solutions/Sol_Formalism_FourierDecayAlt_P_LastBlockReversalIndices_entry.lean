-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LastBlockReversalIndices.entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:17.116995+00:00
-- url     : https://prove2.me/submissions/82db4967-7e55-486b-a723-9e9f3ca34c31

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LastBlockReversalIndices
open Formalism.DoubleCosetMeasures MeasureTheory
namespace Formalism.FourierDecayAlt.P.LastBlockReversalIndices
theorem _root_.solution {K : Type} [CommRing K] {n : ℕ} (N : Fin n) (hN : N.val + 1 = n)
    (V W U : Matrix (Fin n) (Fin n) K) (hV : IsLowUni V) (hU : IsUpUni U) :
    (V * W * U)⁻¹ N N = W⁻¹ N N := by
  have hU' := isUpUni_inv K hU
  have hV' := isLowUni_inv K hV
  have hlast : ∀ i : Fin n, i ≤ N := fun i => by
    have := i.2
    rw [Fin.le_def]
    omega
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_apply, Finset.sum_eq_single N]
  · rw [Matrix.mul_apply, Finset.sum_eq_single N]
    · rw [hU'.2 N, hV'.2 N, one_mul, mul_one]
    · intro j _ hj
      rw [hV'.1 (show OrderDual.toDual N < OrderDual.toDual j from (lt_of_le_of_ne (hlast j) hj : j < N)),
        mul_zero]
    · simp
  · intro i _ hi
    rw [hU'.1 (lt_of_le_of_ne (hlast i) hi), zero_mul]
  · simp
end Formalism.FourierDecayAlt.P.LastBlockReversalIndices
