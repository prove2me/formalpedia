-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:22:18.909133+00:00
-- url     : https://prove2.me/submissions/416194d2-a7e8-4870-8dec-8e614f883681

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_shear_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq Q]
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (B : Matrix P Q ℂ) (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀)
    (h0 : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0) :
    ∫⁻ X : Q → Q → ℂ, G₀ ((cm X)ᴴ * cm X - Bᴴ * B) = ∫⁻ X : Q → Q → ℂ, G₀ ((cm X)ᴴ * cm X) := by
  have hB : Bᴴ * B = ∑ i, Matrix.vecMulVec (star (B i)) (B i) := by
    ext j l
    rw [Matrix.mul_apply, Matrix.sum_apply]
    rfl
  rw [hB]
  exact shear_finset B Finset.univ G₀ hG h0
end Formalism.FourierDecayAlt.P.HermitianFormFactor
