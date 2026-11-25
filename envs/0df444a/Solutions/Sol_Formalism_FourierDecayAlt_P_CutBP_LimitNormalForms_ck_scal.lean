-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.ck_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:33.942801+00:00
-- url     : https://prove2.me/submissions/35bf306d-157c-4d81-b62d-866ea17f93fe

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_contDiff_poly

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
theorem _root_.solution {κ : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg κ P) (UU : Set (Mat k r)) :
    CkOn ⊤ UU (fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) := fun _ _ =>
  ⟨Set.univ, _, isOpen_univ, Set.mem_univ _, ((contDiff_poly hP).smul contDiff_const).contDiffOn, fun _ _ _ => rfl⟩
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
