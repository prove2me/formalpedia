-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.skip_two_comp_skip_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:01:58.895837+00:00
-- url     : https://prove2.me/submissions/b1d73f2c-c277-40d7-b920-9a31eba6e2db

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_skip_one_eq_succAbove
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_skip_two_succAbove_comp_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution {n : ℕ} : ∀ {t : ℕ} (v : Fin (t + 1) → Fin n) (w : Fin (t + 1)) (w' : Fin t),
    (v ∘ skip2 (min (w.succAbove w') w) (max (w.succAbove w') w) : Fin (t + 1 - 2) → Fin n) =
      (v ∘ w.succAbove) ∘ skip1 w'
  | 0, _, _, w' => w'.elim0
  | t + 1, v, w, w' => by
    have h1 := skip_two_succAbove_comp_alt w w'
    have h2 := skip_one_eq_succAbove w'
    funext j
    have h3 := congrFun h1 j
    have h4 := congrFun h2 j
    simp only [Function.comp] at h3 ⊢
    rw [h3, h4]
end Formalism.FourierDecayAlt.P.Qx6
