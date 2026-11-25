-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.normSqTau_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:46:24.917109+00:00
-- url     : https://prove2.me/submissions/6f6a0224-b97b-49e8-8828-ea940dec26a1

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_wt_nonneg
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lint__Q_b562b7426d78

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) :
    normSqTau D τ F = ∫⁻ q, ‖Jv D τ F q‖ₑ ^ 2 ∂μQ D := by
  rw [lint_μQ]
  unfold normSqTau jNormSq
  refine lintegral_congr fun q => ?_
  rw [ENNReal.ofReal_mul (show 0 ≤ bcWeight k r (Tz k r D.z) (Tz k r D.z') q from wt_nonneg D q),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rfl
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
