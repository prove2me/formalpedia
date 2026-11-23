-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.sum3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:11.753477+00:00
-- url     : https://prove2.me/submissions/fa0a2275-1e90-4acd-9fed-050a7dd56349

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution {K K' : Type} [Fintype K] [Fintype K'] (n : ℕ) (f : K → K' → ℕ → ℂ) :
    ∑ k, ∑ κ, ∑ q ∈ range n, f k κ q = ∑ q ∈ range n, ∑ k, ∑ κ, f k κ q := by
  calc _ = ∑ k, ∑ q ∈ range n, ∑ κ, f k κ q := by
        apply Finset.sum_congr rfl; intro k _; exact Finset.sum_comm
    _ = _ := Finset.sum_comm
end Formalism.FourierDecayAlt.P.LEx2
