-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.polyOp_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:06:56.309098+00:00
-- url     : https://prove2.me/submissions/79cc987e-5811-4bd6-a59e-b2996258592f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_polyDeg_const

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
theorem _root_.solution : ∃ Θ : DiffOp k r Wp Wq, CutMP.PolyOp 0 0 Θ ∧ (∀ F, opApply Θ F = F) ∧
    ∀ (D : RealPlaceData k r Wp Wq) (UU : Set (Mat k r)), Commutes D UU Θ := by
  have e : ∀ F : Mat k r → (Wq →L[ℂ] Wp),
      opApply [scalTerm (Wp := Wp) (Wq := Wq) (fun _ => 1) [] (by simp)] F = F := fun F => by
    funext g; simp [opApply, scalTerm, Rw]
  refine ⟨[scalTerm (fun _ => 1) [] (by simp)], fun T hT => ?_, e, fun D UU p _ f _ g _ => by rw [e, e]⟩
  rw [List.mem_singleton] at hT
  subst hT
  exact ⟨by simp [scalTerm], fun _ => 1, polyDeg_const _ 1, fun _ => rfl, fun _ => rfl⟩
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
