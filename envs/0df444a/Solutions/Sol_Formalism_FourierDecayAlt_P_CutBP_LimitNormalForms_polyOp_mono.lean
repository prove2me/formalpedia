-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.polyOp_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:03:30.930448+00:00
-- url     : https://prove2.me/submissions/a402e97a-e7c4-4b17-bf38-7e89942433f2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_polyDeg_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ContDiff Topology
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
theorem _root_.solution {o κ o' κ' : ℕ} (ho : o ≤ o') (hκ : κ ≤ κ') {Θ : DiffOp k r Wp Wq} (h : CutMP.PolyOp o κ Θ) :
    CutMP.PolyOp o' κ' Θ := fun T hT => by
  obtain ⟨h1, P, hP, h2⟩ := h T hT
  exact ⟨h1.trans ho, P, polyDeg_mono hκ hP, h2⟩
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
