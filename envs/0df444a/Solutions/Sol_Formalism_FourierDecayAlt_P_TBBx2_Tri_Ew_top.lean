-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:53:14.985+00:00
-- url     : https://prove2.me/submissions/610aa3ee-e999-4ab6-b41c-ecbbdf006956

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_RR_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_hsInner_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_RR_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Tri
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par}
namespace Formalism.FourierDecayAlt.P.TBBx2.Tri
theorem _root_.solution (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) :
    Ew p (fun _ => 1) F (P.r + 1) [] γ =
      (Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ)) * ‖B.hsVec (p.V F γ)‖ ^ 2 := by
  unfold Ew NP
  rw [RR_top p F hγ, hsInner_self]
  simp only [normC, List.map_nil, List.prod_nil, div_one]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
end Formalism.FourierDecayAlt.P.TBBx2.Tri
