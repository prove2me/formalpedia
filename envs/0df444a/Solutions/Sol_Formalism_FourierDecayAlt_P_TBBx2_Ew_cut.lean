-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Ew_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:12:44.717549+00:00
-- url     : https://prove2.me/submissions/4acb09bf-3127-4291-9296-f1138b54337c

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_RR_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.TBBx2
theorem _root_.solution (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hV : TBB.VecCutAt p χ F) (ε : ℝ) (hε : 0 < ε) (γ : C.LPt) (hγ : D.IsLocPt γ (P.r + 1))
    (hG : ε ≤ TBB.Gp p γ) :
    TBB.Ew p nn (D.cutF p.T.base χ F ε) (P.r + 1) [] γ = TBB.Ew p nn F (P.r + 1) [] γ := by
  unfold TBB.Ew TBB.NP
  rw [RR_top p (D.cutF p.T.base χ F ε) γ hγ, RR_top p F γ hγ, hV ε hε γ hγ hG]
end Formalism.FourierDecayAlt.P.TBBx2
