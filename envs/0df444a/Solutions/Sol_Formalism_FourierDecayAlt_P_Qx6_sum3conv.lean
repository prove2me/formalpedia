-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.sum3conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:39:04.355918+00:00
-- url     : https://prove2.me/submissions/3cf4b346-6f52-4dbf-9552-98d4086671ea

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {M : Type*} [AddCommMonoid M] {t : ℕ} (w : Fin (t + 1)) (F : Fin (t + 1) → Fin (t + 1) → Fin (t + 1) → M) :
    (∑ W, ∑ X, ∑ X', if W ≠ w ∧ X ≠ X' then F W X X' else 0) =
      ∑ w', ∑ x', ∑ x, F (w.succAbove w') (x'.succAbove x) x' := by
  rw [Fin.sum_univ_succAbove _ w]
  have h0 : (∑ X, ∑ X', if w ≠ w ∧ X ≠ X' then F w X X' else (0 : M)) = 0 := by
    simp
  rw [h0, zero_add]
  refine Finset.sum_congr rfl (fun w' _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  rw [Fin.sum_univ_succAbove _ x']
  simp [Fin.succAbove_ne]
end Formalism.FourierDecayAlt.P.Qx6
