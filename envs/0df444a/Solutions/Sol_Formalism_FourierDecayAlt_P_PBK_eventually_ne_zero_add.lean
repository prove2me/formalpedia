-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:12:27.836747+00:00
-- url     : https://prove2.me/submissions/11cb97b2-7bbe-4eba-8f4f-52fb7b5993dc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (σ : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ 0 ∧ x + σ ≠ 0 := by
  have h1 : ∀ᶠ x in cocompact ℂ, x ≠ 0 := (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have h2 : ∀ᶠ x in cocompact ℂ, x ≠ -σ := (isCompact_singleton (x := -σ)).compl_mem_cocompact
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, fun h => hx2 (eq_neg_of_add_eq_zero_left h)⟩
end Formalism.FourierDecayAlt.P.PBK
