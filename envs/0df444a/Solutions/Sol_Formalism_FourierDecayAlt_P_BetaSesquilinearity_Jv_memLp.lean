-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Jv_memLp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:12.810843+00:00
-- url     : https://prove2.me/submissions/9141e2ef-da3b-4b79-ae36-ca1c2cbbf260

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_normSqTau_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Jv_aesm

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
variable {D : RealPlaceData k r Wp Wq} {A : ℝ}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (hJ : JCont D A) (hDD : DiagDom D A) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F)
    {τ : ℝ × ℝ} (hτ : τ ∈ Quad) : MemLp (Jv D τ F) 2 (μQ D) := by
  rw [memLp_two_iff_integrable_sq_norm (Jv_aesm hJ hF hτ)]
  refine ⟨(Jv_aesm hJ hF hτ).norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h := (hDD F hF τ hτ).2
  rw [normSqTau_eq] at h
  refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  congr 1
  funext q
  rw [enorm_pow, enorm_norm]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
