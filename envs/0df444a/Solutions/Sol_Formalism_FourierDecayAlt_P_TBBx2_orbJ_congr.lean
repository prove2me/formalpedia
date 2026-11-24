-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.orbJ_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:12.89146+00:00
-- url     : https://prove2.me/submissions/bc9ddf5d-b511-4899-881b-7793d6ca8938

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_choose_dite_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.TBBx2
theorem _root_.solution {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (μR : Measure (Mt k r)) (F G : B.Mat k r → (Wq →L[ℂ] Wp))
    (hae : ∀ᵐ q ∂Ds.μSS, D.orbIntegrand Ds γ F q = D.orbIntegrand Ds γ G q) :
    D.orbJ Ds γ μR F = D.orbJ Ds γ μR G := by
  unfold D.orbJ
  exact choose_dite_congr
    (fun θ => D.IsNormCut Ds γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Ds γ F q) Ds.μSS)
    (fun θ => D.IsNormCut Ds γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Ds γ G q) Ds.μSS)
    (funext fun θ => propext (and_congr_right fun _ =>
      integrable_congr (hae.mono fun q hq => by simp only [hq])))
    (fun θ => ∫ q, θ q • D.orbIntegrand Ds γ F q ∂Ds.μSS)
    (fun θ => ∫ q, θ q • D.orbIntegrand Ds γ G q ∂Ds.μSS)
    (fun θ _ => integral_congr_ae (hae.mono fun q hq => by simp only [hq]))
end Formalism.FourierDecayAlt.P.TBBx2
