-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SandwichRhoAction.sgs_curveR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:46:38.466702+00:00
-- url     : https://prove2.me/submissions/13fae1aa-d45b-4254-9594-5e2651afbd9b

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SandwichRhoAction_sgs_eq__593e24e4c7f7
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_isUnit_sR

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
    sgs p (g * NormedSpace.exp ((t : ℂ) • X)) = sgs p g * NormedSpace.exp ((t : ℂ) • AdR p X) := by
  have hu : IsUnit (sR p) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_sR D hp)
  rw [sgs_eq', sgs_eq']
  unfold AdR
  have hc : ((t : ℂ) • ((sR p)⁻¹ * X * sR p)) = (sR p)⁻¹ * ((t : ℂ) • X) * sR p := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hc]
  first
    | rw [Matrix.exp_conj' _ _ hu]
    | rw [Matrix.exp_conj' ℂ _ _ hu]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_sR D hp)]
end Formalism.FourierDecayAlt.P.SandwichRhoAction
