-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.cutoff_gamma_product_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:46:36.748156+00:00
-- url     : https://prove2.me/submissions/4e08abd9-b7d2-4339-9451-fae4ccb12a46

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gam_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Wd_tsupport

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (m l : ℕ) {t : ℝ × ℝ}
    (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2) :
    gam (rr r) (Wd D) m t.1 * gam (rr r) (Wd D) l t.2 = 0 := by
  by_cases h1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
  · have h2 : t.2 ∉ Set.Ioo (1 / 2 : ℝ) 2 := fun h2 => ht ⟨h1, h2⟩
    rw [gam_zero (Wd_tsupport D) _ _ h2, mul_zero]
  · rw [gam_zero (Wd_tsupport D) _ _ h1, zero_mul]
end Formalism.FourierDecayAlt.P.B6
