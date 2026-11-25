-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.gq_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:35.129495+00:00
-- url     : https://prove2.me/submissions/6aa37813-d885-45c4-8b5e-036b791f6673

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_tt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellHermitian_gqDom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.FourierDecayAlt.P.CutMP
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
theorem _root_.solution (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    B.gq Bs q.1 ∈ B.GV P.k P.r ∩ Gauge.OmB Bs := by
  have h := BigCellHermitian.gqDom Bs (q := q.1) ⟨q.2.1, by rw [← tt_eq hpl]; exact q.2.2⟩
  exact ⟨h.1, h.2.2, fun a => h.2.1 _ (by simp)⟩
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
