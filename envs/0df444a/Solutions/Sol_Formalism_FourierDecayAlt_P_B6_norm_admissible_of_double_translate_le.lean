-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.norm_admissible_of_double_translate_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:29:28.094589+00:00
-- url     : https://prove2.me/submissions/8c186d13-4af5-481e-96e1-2420030b8261

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_two_sided_translate
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_norm_bound

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
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {α c : ℝ} (hα : 0 ≤ α) {f : Mat k r → (Wq →L[ℂ] Wp)} (hf : admitted α c f)
    {u v g : Mat k r} (hu : u ∈ GV k r) (hv : v ∈ GV k r) (hg : g ∈ GV k r) {K : ℝ}
    (h1 : gN u⁻¹ ≤ K) (h2 : gN v⁻¹ ≤ K) :
    ‖f (u * g * v)‖ ≤ c * (K * K) ^ α * gN g ^ (-α) := by
  have h := admissible_norm_bound (admissible_two_sided_translate hα hf hu hv) hg
  have hc := admissible_constant_nonneg hf
  have hm : 0 ≤ gN g ^ (-α) := Real.rpow_nonneg (gN_nonneg g) _
  have hP : (gN u⁻¹ * gN v⁻¹) ^ α ≤ (K * K) ^ α :=
    Real.rpow_le_rpow (mul_nonneg (gN_nonneg _) (gN_nonneg _))
      (mul_le_mul h1 h2 (gN_nonneg _) (le_trans (gN_nonneg _) h1)) hα
  refine le_trans h ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hc) hm
end Formalism.FourierDecayAlt.P.B6
