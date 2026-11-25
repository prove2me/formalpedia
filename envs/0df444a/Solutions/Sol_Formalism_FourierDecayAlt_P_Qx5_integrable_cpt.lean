-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.integrable_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:15:15.955922+00:00
-- url     : https://prove2.me/submissions/c6749103-f123-49de-ac9d-52b1f3fc84ff

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_Glev_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_ae


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution {i : Fin (r + 1)} {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r i) μ) {D K : Set (Mx k r)}
    {p : Mx k r → ℂ} (hK : IsCompact K) (hKD : K ⊆ D) (hp : ContinuousOn p (Glev k r i ∩ D))
    (h0 : ∀ g ∈ Glev k r i, g ∉ K → p g = 0) : Integrable (fun x : Mt k r => p (Matrix.of x)) μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ.finite_compact K hK⟩
  have hS : IsCompact (Glev k r i ∩ K) := hK.inter_left (Glev_closed i)
  have hS' : IsCompact ({x : Mt k r | (Matrix.of x : Mx k r) ∈ Glev k r i ∩ K}) := hS
  have hc : ContinuousOn (fun x : Mt k r => p (Matrix.of x)) {x : Mt k r | (Matrix.of x : Mx k r) ∈ Glev k r i ∩ K} :=
    hp.mono fun x hx => ⟨hx.1, hKD hx.2⟩
  have hi := hc.integrableOn_compact (μ := μ) hS'
  refine hi.integrable_of_ae_notMem_eq_zero ?_
  filter_upwards [B5.haar_ae hμ] with x hx hxS
  exact h0 _ hx fun hxK => hxS ⟨hx, hxK⟩
end Formalism.FourierDecayAlt.P.Qx5
