-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.lw_conjPl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:46.000879+00:00
-- url     : https://prove2.me/submissions/da73632c-ef4b-4033-b8f7-e2f2c27c242a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_absNorm_map_ringEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ValuationRepresentative
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ValuationRepresentative
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : lw (conjPl w) = lw w := by
  unfold lw
  rw [show (conjPl w).asIdeal = w.asIdeal.map (cO K) from rfl, absNorm_map_ringEquiv]
end Formalism.DivisionValues.ValuationRepresentative
