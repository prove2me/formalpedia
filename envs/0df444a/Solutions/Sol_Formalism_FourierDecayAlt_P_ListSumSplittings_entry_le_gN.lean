-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.entry_le_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:24.374943+00:00
-- url     : https://prove2.me/submissions/c9af7d9f-b50b-4699-a8b1-1447a649501d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution (g : Mat k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ gN g := by
  have h : ‖g i j‖ ^ 2 ≤ ∑ i, ∑ j, Complex.normSq (g i j) := by
    rw [Complex.sq_norm]
    exact (Finset.single_le_sum (f := fun j => Complex.normSq (g i j)) (fun _ _ => Complex.normSq_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
  have := Real.abs_le_sqrt h
  rwa [abs_of_nonneg (norm_nonneg _)] at this
end Formalism.FourierDecayAlt.P.ListSumSplittings
