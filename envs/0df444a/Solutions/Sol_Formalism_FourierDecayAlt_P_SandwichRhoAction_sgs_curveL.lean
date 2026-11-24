-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SandwichRhoAction.sgs_curveL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:45:20.364163+00:00
-- url     : https://prove2.me/submissions/18c11009-fd32-4b28-b4ab-566c018a935c

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SandwichRhoAction_sgs_eq__593e24e4c7f7
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_isUnit_sL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SandwichRhoAction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SandwichRhoAction
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X g : Mat k r) (t : ℝ) :
    sgs p (NormedSpace.exp (-((t : ℂ) • X)) * g) = NormedSpace.exp (-((t : ℂ) • AdL p X)) * sgs p g := by
  have hu : IsUnit (sL p) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_sL D hp)
  rw [sgs_eq', sgs_eq']
  unfold AdL
  have hc : -((t : ℂ) • ((sL p)⁻¹ * X * sL p)) = (sL p)⁻¹ * (-((t : ℂ) • X)) * sL p := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hc]
  first
    | rw [Matrix.exp_conj' _ _ hu]
    | rw [Matrix.exp_conj' ℂ _ _ hu]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_sL D hp)]
end Formalism.FourierDecayAlt.P.SandwichRhoAction
