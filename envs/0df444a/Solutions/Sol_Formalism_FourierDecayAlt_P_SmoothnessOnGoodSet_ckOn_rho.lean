-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.ckOn_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:09:41.119646+00:00
-- url     : https://prove2.me/submissions/ae56cb22-8af9-46d3-a4d1-14ae0ea16519

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_translate
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ∞} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn m (GV k r) F) : CkOn m (GV k r) (rho D p F) := by
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r :=
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hp.1.1) (WeylGroupFacts.uh_inv hp.2.1.1)
  have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1
  have e : rho D p F = fun x => ((ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹)))
      (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))) := by
    funext x
    simp only [rho, sgs, Matrix.mul_assoc]
    rfl
  rw [e]
  exact Formalism.FourierDecayAlt.P.B5.ckOn_clm (Formalism.FourierDecayAlt.P.B5.ckOn_translate hF ha hb) _
end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
