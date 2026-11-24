-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.good_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:39.132776+00:00
-- url     : https://prove2.me/submissions/5fe6bca9-703e-4b27-8f5b-7eea0a41b996

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_opL_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fam_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_RS_op
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_om_stable
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_of

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hFO : FamOps) (hz : inWb k r z) (hz' : inWb k r z') (hS : SData z z' L Dc Dc (OmX r))
    (l : Fin r) (q : Fin 6) : (famData π π' hS).Good (crd (opL l q)) := by
  refine good_of hS (RS_op hFO hz hz' hS l (om_stable l) q) ?_
  intro Φ Ψ hΦ hΨ s c hc g hg hgD
  exact opL_lin l q s (fam_diff hΦ hc hg hgD) (fam_diff hΨ hc hg hgD)
end Formalism.FourierDecayAlt.P.Qx6
