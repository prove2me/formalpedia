-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FixedPointsGramVector.eq_zero_of_sum_normSq_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:19.335448+00:00
-- url     : https://prove2.me/submissions/71f7e726-19f9-43f5-9782-6a02f297f24d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FixedPointsGramVector
theorem _root_.solution {n : ℕ} (y : Fin n → ℂ) (h : ∑ i, Complex.normSq (y i) ≤ 0) : y = 0 := by
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ Complex.normSq (y j) := fun j _ => Complex.normSq_nonneg _
  have h0 : ∑ i, Complex.normSq (y i) = 0 := le_antisymm h (Finset.sum_nonneg hnn)
  funext i
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ _)
  simpa using Complex.normSq_eq_zero.1 h1
end Formalism.FourierDecayAlt.P.FixedPointsGramVector
