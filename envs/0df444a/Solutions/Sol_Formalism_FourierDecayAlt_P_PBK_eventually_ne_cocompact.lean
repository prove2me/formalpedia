-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.eventually_ne_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:16:45.666417+00:00
-- url     : https://prove2.me/submissions/47d135da-5355-4f7a-a614-5c5712664f1c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (c : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ c := by
  filter_upwards [(isCompact_singleton : IsCompact ({c} : Set ℂ)).compl_mem_cocompact] with x hx
  simpa using hx
end Formalism.FourierDecayAlt.P.PBK
