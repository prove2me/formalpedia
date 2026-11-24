-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.snocCast_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:59:21.872436+00:00
-- url     : https://prove2.me/submissions/65672c23-62c5-409a-aeaa-d2128961252a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bS_succAbove_castSucc

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
theorem _root_.solution {n : ℕ} : ∀ {m : ℕ} (v : Fin m → Fin n) (es : Fin n) (w : Fin m) (h : m = m - 1 + 1),
    (Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast h : Fin m → Fin n) =
      bS v es ∘ w.castSucc.succAbove
  | 0, _, _, w, _ => w.elim0
  | m + 1, v, es, w, h => by
    rw [bS_succAbove_castSucc]
    rfl
end Formalism.FourierDecayAlt.P.Qx6
