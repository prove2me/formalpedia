-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.cd_matmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:59:15.702554+00:00
-- url     : https://prove2.me/submissions/0c53f1ab-3b14-43c1-a16c-05287d27f3e1

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_cd_entries
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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X} {A B : X → Mx k r}
    (hA : ContDiffOn ℝ ∞ A s) (hB : ContDiffOn ℝ ∞ B s) : ContDiffOn ℝ ∞ (fun x => A x * B x) s := by
  rw [cd_entries] at hA hB ⊢
  intro p q
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun j _ => (hA p j).mul (hB j q)
end Formalism.FourierDecayAlt.P.Qx6
