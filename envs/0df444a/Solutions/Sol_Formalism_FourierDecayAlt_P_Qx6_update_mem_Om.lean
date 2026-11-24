-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.update_mem_Om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:38:00.51829+00:00
-- url     : https://prove2.me/submissions/6848da1e-5654-4721-952d-d3cff74c73c1

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
theorem _root_.solution {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) {s : ℂ} (hs : s ≠ 0) :
    Function.update c l s ∈ OmX r := by
  show ∀ a, Function.update c l s a ≠ 0
  intro a
  by_cases h : a = l
  · subst h
    simpa using hs
  · simpa [h] using (show ∀ a, c a ≠ 0 from hc) a
end Formalism.FourierDecayAlt.P.Qx6
