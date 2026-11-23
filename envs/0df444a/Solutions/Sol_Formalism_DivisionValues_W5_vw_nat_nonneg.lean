-- Prove2me | solution 1 for Formalism.DivisionValues.W5.vw_nat_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:30.485562+00:00
-- url     : https://prove2.me/submissions/450e3f8e-6dcb-46ff-9786-e2377f71fd8a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Theorems.Thm_Formalism_DivisionValues_W5_vw_int
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.W5
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues.W5
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : 0 ≤ vw w (n : K) := by
  have h : ((n : 𝓞 K) : K) = (n : K) := map_natCast _ n
  rw [← h, vw_int]
  exact FractionalIdeal.count_coe_nonneg K w _
end Formalism.DivisionValues.W5
