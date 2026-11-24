-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.admissible_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:01:29.728841+00:00
-- url     : https://prove2.me/submissions/c12b9aea-3713-44c0-9fcc-2b4941be17df

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_pos

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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α c : ℝ} {f : Mat k r → E}
    (hf : admitted α c f) {g : Mat k r} (hg : g ∈ GV k r) : ‖f g‖ ≤ c * gN g ^ (-α) := by
  have hp : 0 < gN g ^ α := Real.rpow_pos_of_pos (gN_pos hg) _
  rw [Real.rpow_neg (gN_nonneg g), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
  exact hf.2 g hg
end Formalism.FourierDecayAlt.P.B6
