-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.dom_Dcell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:41:22.627807+00:00
-- url     : https://prove2.me/submissions/bd68e298-0ccc-40f9-b762-77ac62b209eb

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Dcell_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Dcell_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_dom_step
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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hR : ResMem) (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)}
    (hD : IsDom k r z z' 0 D) (i : Fin (r + 1)) : ∀ c ∈ OmX r, IsDom k r z z' i (Dcell D i c) := by
  intro c hc
  induction i using Fin.induction with
  | zero =>
    rw [Dcell_zero]
    exact hD
  | succ l ih =>
    rw [Dcell_succ]
    exact dom_step hR hz hz' l ih ((show ∀ a, c a ≠ 0 from hc) l)
end Formalism.FourierDecayAlt.P.Qx6
