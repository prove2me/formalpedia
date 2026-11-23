-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.map_cO_map_cO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:03.206329+00:00
-- url     : https://prove2.me/submissions/dfd7f36f-84c7-48e1-a898-ec2caeaa87f7

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_cO_cO

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
theorem _root_.solution (I : Ideal (𝓞 K)) : (I.map (cO K)).map (cO K) = I := by
  ext y
  simp only [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    rwa [cO_cO]
  · intro hy
    exact ⟨cO K y, ⟨y, hy, rfl⟩, cO_cO y⟩
end Formalism.DivisionValues.ValuationRepresentative
