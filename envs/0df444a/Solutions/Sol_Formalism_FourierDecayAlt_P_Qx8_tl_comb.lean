-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.tl_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:38:55.564537+00:00
-- url     : https://prove2.me/submissions/e8b10767-583b-4e3b-a606-3c673d2044e7

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulIntegralStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Topology Formalism.YangianSpanCharacter.T
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {i : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution (hT : TLinLoc) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}
    (hD : IsOpen D) (Y : ℂ) (a b : Fin 2) (s s₂ : ℂ) {f f₂ : Mx k r → E} (hf : SmoothLev k r i D f)
    (hf₂ : SmoothLev k r i D f₂) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    tL k r z z' i Y a b (fun x => s • (f x + s₂ • f₂ x)) g =
      s • (tL k r z z' i Y a b f g + s₂ • tL k r z z' i Y a b f₂ g) := by
  have h1 := tl_smul (z := z) (z' := z') hT hD Y a b s (smooth_add hf (smooth_smul hf₂ s₂)) hg
  have h2 := tl_add (z := z) (z' := z') hT hD Y a b hf (smooth_smul hf₂ s₂) hg
  have h3 := tl_smul (z := z) (z' := z') hT hD Y a b s₂ hf₂ hg
  rw [h2, h3] at h1
  exact h1
end Formalism.FourierDecayAlt.P.Qx8
