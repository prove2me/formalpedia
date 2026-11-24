-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.hsVec_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:57:12.725223+00:00
-- url     : https://prove2.me/submissions/e02fac04-c6b9-4c4c-93fa-a4e13842b620

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_hsVec_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_hsVec_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution : Continuous (hsVec : (Wq →L[ℂ] Wp) → _) := by
  let φ : (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
    { toFun := hsVec, map_add' := hsVec_add, map_smul' := fun a A => hsVec_smul a A }
  exact φ.continuous_of_finiteDimensional
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
