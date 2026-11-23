-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement_degree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:43.888986+00:00
-- url     : https://prove2.me/submissions/432bd2b1-0df4-43fd-ab62-66e9ee763509

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_sum_top

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
theorem _root_.solution : Complement2Degree := by
  unfold Complement2Degree
  intro Pl _ TT _ aT w nν δν δpm k Dpi Dp Dm hDpi hnν hD
  have h1 : Dpi - Dp - Dm = ∑ ρ, (nν ρ - ((k - 1) * w ρ + δpm ρ)) := by
    rw [Finset.sum_sub_distrib, ← hDpi, ← hD]; ring
  rw [h1, sum_top TT aT, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  simp only [hnν ρ]
  split_ifs <;> ring
end Formalism.DivisionValues
