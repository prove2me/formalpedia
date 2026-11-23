-- Prove2me | solution 1 for Formalism.DivisionValues.sum_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:16.020001+00:00
-- url     : https://prove2.me/submissions/fa8fac5a-05af-4c40-b884-c07f5d8ef454

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution {Pl : Type} [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (f : Pl → ℝ) :
    ∑ t ∈ TT, f t = ∑ ρ, if ρ ∈ TT then f ρ else 0 := by
  symm
  rw [← Finset.sum_filter]
  congr 1
  ext ρ
  simp
end Formalism.DivisionValues
