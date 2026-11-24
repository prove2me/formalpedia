-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.fam_Res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:21:07.253304+00:00
-- url     : https://prove2.me/submissions/3ae10f37-6c0a-4f16-901b-408f9bbd093e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sf_Res
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
theorem _root_.solution (hW : WeylLevelElementFacts) (hR : ResMem) (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r)
    {Dc : (Fin r → ℂ) → Set (Mx k r)} (hd : ∀ c ∈ OmX r, IsDom k r z z' l.castSucc (Dc c))
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' l.castSucc Dc Φ) :
    FamFF k r z z' π π' l.succ (stepD l Dc) (Res k r l Φ) :=
  ⟨sf_Res hW l h.1, fun c hc => ff_smul _
    ((((hR Wp Wq k r z z' π π' l (Dc c) hz hz' (hd c hc) (Φ c) (h.2 c hc)).1) (c l) (hc l)).2)⟩
end Formalism.FourierDecayAlt.P.Qx6
