-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.commutes_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:06.59089+00:00
-- url     : https://prove2.me/submissions/e10b1c57-2b26-4aa1-a44d-04d879d4bca6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_ext_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_op_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_sgs_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_sgs_gv

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {UU : Set (Mat k r)} {Θ : DiffOp k r Wp Wq} (hC : Commutes D UU Θ)
    {p : SS k r} (hp : D.inSS p) {VV : Set (Mat k r)} {J : Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : CkOn (opOrder Θ : ℕ∞) VV J) {g : Mat k r} (hg : g ∈ UU) (hgG : g ∈ GV k r) (hgV : sgs p g ∈ VV) :
    opApply Θ (rho D p J) g = rho D p (opApply Θ J) g := by
  obtain ⟨f, U, hf, hU, hgU, he⟩ := ext_loc hJ hgV
  have e1 : opApply Θ (rho D p J) g = opApply Θ (rho D p f) g :=
    op_congr Θ (hU.preimage (sgs_cont p)) (fun x hx hxU => by
      simp only [rho]; rw [he _ hxU (sgs_gv D hp hx)]) hgG hgU
  have e2 : opApply Θ f (sgs p g) = opApply Θ J (sgs p g) :=
    op_congr Θ hU (fun x hx hxU => he x hxU hx) (sgs_gv D hp hgG) hgU
  rw [e1, hC p hp f hf g hg]
  simp only [rho]
  rw [e2]
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
