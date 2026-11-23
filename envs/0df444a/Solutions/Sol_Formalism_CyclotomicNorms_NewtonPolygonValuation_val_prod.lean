-- Prove2me | solution 1 for Formalism.CyclotomicNorms.NewtonPolygonValuation.val_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:38.323803+00:00
-- url     : https://prove2.me/submissions/d6d756c2-e13f-4b37-834a-4454e2e50d29

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.NewtonPolygonValuation
variable {L : Type} [Field L] (v : AddValuation L (WithTop ℝ))
namespace Formalism.CyclotomicNorms.NewtonPolygonValuation
theorem _root_.solution {ι : Type*} (s : Finset ι) (g : ι → L) :
    v (∏ i ∈ s, g i) = ∑ i ∈ s, v (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, AddValuation.map_mul, ih]
end Formalism.CyclotomicNorms.NewtonPolygonValuation
