-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.sum_ne_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:54.978836+00:00
-- url     : https://prove2.me/submissions/d0f7360d-c580-471a-af99-fd973536166b

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] {t : ℕ} (p : Fin (t + 1)) (f : Fin (t + 1) → M) :
    (∑ W, if W ≠ p then f W else 0) = ∑ w, f (p.succAbove w) := by
  rw [Fin.sum_univ_succAbove _ p]
  simp [Fin.succAbove_ne]
end Formalism.FourierDecayAlt.P.Qx6
