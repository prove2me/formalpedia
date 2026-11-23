-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormDomination.prob_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:51.519676+00:00
-- url     : https://prove2.me/submissions/2a8d283c-d02e-48f1-b518-51de5de34334

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FormDomination
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.FormDomination
theorem _root_.solution {α : Type} (S : Finset α) (θ g : α → ℝ) (hθ : IsProb S θ) (M : ℝ)
    (hg : ∀ a ∈ S, g a ≤ M) : ∑ a ∈ S, θ a * g a ≤ M := by
  calc ∑ a ∈ S, θ a * g a ≤ ∑ a ∈ S, θ a * M :=
        Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hg a ha) (hθ.1 a)
    _ = M := by rw [← Finset.sum_mul, hθ.2.2, one_mul]
end Formalism.FourierDecayAlt.P.FormDomination
