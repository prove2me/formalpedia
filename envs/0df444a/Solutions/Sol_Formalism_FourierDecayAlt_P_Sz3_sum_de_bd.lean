-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.sum_de_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:14.490412+00:00
-- url     : https://prove2.me/submissions/a63c2c5e-a686-4d5e-87f6-ac167ee19104

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (s : Finset ℕ) :
    0 ≤ ∑ i ∈ s, de i ∧ ∑ i ∈ s, de i ≤ (s.card : ℝ) := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    rcases hde i with h | h <;> linarith
  · have : ∑ i ∈ s, de i ≤ ∑ _i ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rcases hde i with h | h <;> linarith
    simpa using this
end Formalism.FourierDecayAlt.P.Sz3
