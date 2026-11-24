-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.ind_QL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:39:29.807669+00:00
-- url     : https://prove2.me/submissions/9b40374d-ba72-4a7d-899e-d950b9e44897

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {i : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (L : Fin (r + 1)) (Y : ℂ) (a b : Fin 2) {Φ : Fn k r E}
    (h : Ind i Φ) : Ind i (QL k r z z' L Y a b Φ) := by
  intro c hc c' hc' hcc
  show tL k r z z' L Y a b (Φ c) = tL k r z z' L Y a b (Φ c')
  rw [h c hc c' hc' hcc]
end Formalism.FourierDecayAlt.P.Qx6
