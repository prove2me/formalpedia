-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.trJB_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:36:41.223391+00:00
-- url     : https://prove2.me/submissions/e3ac19e7-b614-431d-af3e-24e53defc950

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_gq_mem

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
theorem _root_.solution (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    {J J' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV P.k P.r ∩ Gauge.OmB Bs, J g = J' g) :
    Gauge.trJB P Bs e J = Gauge.trJB P Bs e J' := by
  funext ρ
  unfold Gauge.trJB
  congr 1
  funext q
  unfold Gauge.rawJ
  rw [h _ (gq_mem hpl q)]
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
