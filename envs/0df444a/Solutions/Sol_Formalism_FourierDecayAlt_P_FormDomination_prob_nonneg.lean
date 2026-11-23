-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormDomination.prob_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:51.59281+00:00
-- url     : https://prove2.me/submissions/19b27ef4-4312-429a-8835-13d68e678e75

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
theorem _root_.solution {α : Type} (S : Finset α) (θ g : α → ℝ) (hθ : IsProb S θ)
    (hg : ∀ a ∈ S, 0 ≤ g a) : 0 ≤ ∑ a ∈ S, θ a * g a :=
  Finset.sum_nonneg fun a ha => mul_nonneg (hθ.1 a) (hg a ha)
end Formalism.FourierDecayAlt.P.FormDomination
