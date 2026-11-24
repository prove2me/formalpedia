-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.qm_dropE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:04:43.631369+00:00
-- url     : https://prove2.me/submissions/f7fefa1e-b687-49bc-8621-41c0060f6fc6

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_succAbove_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_quantum_minor_expand_last_line
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hLR : ExpLastRow) (hSk : QSkewRow) (hE : GlRel E) : ∀ {m : ℕ} (v b : Fin m → Fin n) (s : Fin n)
    (w : Fin m) (u : ℂ),
    qminor E (bE s v ∘ w.succ.succAbove) b u = ∑ x : Fin m, ((-1 : ℤ) ^ (x : ℕ)) •
      (qminor E (v ∘ skip1 w) (b ∘ skip1 x) (u - 1) * Tm E u s (b x))
  | 0, _, _, _, w, _ => w.elim0
  | m + 1, v, b, s, w, u => by
    rw [bE_succAbove_succ, quantum_minor_expand_last_line E hLR hSk hE]
    rfl
end Formalism.FourierDecayAlt.P.Qx6
