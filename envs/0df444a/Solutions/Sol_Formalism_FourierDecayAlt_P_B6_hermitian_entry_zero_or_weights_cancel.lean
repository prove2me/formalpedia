-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.hermitian_entry_zero_or_weights_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:06:05.225783+00:00
-- url     : https://prove2.me/submissions/5a801ecf-deb3-43aa-843d-af80b03a82c1

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

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
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = 0 ∨ dilationGeneratorDiagonal k r i + dilationGeneratorDiagonal k r j = 0 := by
  by_cases c1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · right
    have h1 : ¬ j.val < r := by omega
    have h2 : ¬ j.val ≤ r + k := by omega
    have h3 : j.val - (r + k) = r - i.val := by omega
    simp only [dilationGeneratorDiagonal, c1.1, h1, h2, if_true, if_false, h3]
    push_cast; ring
  · by_cases c2 : j.val < r ∧ i.val + j.val = 2 * r + k
    · right
      have h1 : ¬ i.val < r := by omega
      have h2 : ¬ i.val ≤ r + k := by omega
      have h3 : i.val - (r + k) = r - j.val := by omega
      simp only [dilationGeneratorDiagonal, c2.1, h1, h2, if_true, if_false, h3]
      push_cast; ring
    · by_cases c3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
      · right
        obtain ⟨a, b, rfl⟩ := c3
        have h1 : ¬ i.val < r := by omega
        simp [dilationGeneratorDiagonal, h1, b]
      · left
        simp [Hpk, c1, c2, c3]
end Formalism.FourierDecayAlt.P.B6
