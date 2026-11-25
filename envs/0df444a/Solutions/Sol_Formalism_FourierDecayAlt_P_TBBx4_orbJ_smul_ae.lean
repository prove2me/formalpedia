-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx4.orbJ_smul_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:24.497555+00:00
-- url     : https://prove2.me/submissions/656e2c5c-2f1d-4fef-9cf4-859537b114e5

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_choose_dite_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx4
open MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal ComplexConjugate
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
namespace Formalism.FourierDecayAlt.P.TBBx4
theorem _root_.solution {k r : ℕ} (Ds : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (F G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ) (hc : c ≠ 0)
    (hae : ∀ᵐ q ∂Ds.μSS, D.orbIntegrand Ds γ G q = c • D.orbIntegrand Ds γ F q) :
    D.orbJ Ds γ μR G = c • D.orbJ Ds γ μR F := by
  classical
  have hP : (fun θ => D.IsNormCut Ds γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Ds γ G q) Ds.μSS) =
      (fun θ => D.IsNormCut Ds γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Ds γ F q) Ds.μSS) := by
    funext θ
    apply propext
    refine and_congr_right fun _ => ?_
    rw [integrable_congr (hae.mono fun q hq => by
      show θ q • D.orbIntegrand Ds γ G q = c • (θ q • D.orbIntegrand Ds γ F q)
      rw [hq, smul_comm])]
    exact integrable_fun_smul_iff hc _
  unfold D.orbJ
  simp only [smul_dite, smul_zero]
  refine TBBx2.choose_dite_congr (E := Wq →L[ℂ] Wp) _ _ hP
    (fun θ => ∫ q, θ q • D.orbIntegrand Ds γ G q ∂Ds.μSS)
    (fun θ => c • ∫ q, θ q • D.orbIntegrand Ds γ F q ∂Ds.μSS) fun θ _ => ?_
  rw [← integral_smul]
  exact integral_congr_ae (hae.mono fun q hq => by
    show θ q • D.orbIntegrand Ds γ G q = c • (θ q • D.orbIntegrand Ds γ F q)
    rw [hq, smul_comm])
end Formalism.FourierDecayAlt.P.TBBx4
