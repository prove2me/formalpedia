-- Prove2me | solution 1 for Formalism.CyclotomicNorms.NewtonPolygonValuation.val_sum_eq_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:38.858014+00:00
-- url     : https://prove2.me/submissions/e4894ba3-1c97-45ce-9b00-ce310d3b280d

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
theorem _root_.solution {ι : Type*} [DecidableEq ι] {s : Finset ι} {g : ι → L} {i₀ : ι}
    (hi : i₀ ∈ s) (h0 : v (g i₀) ≠ ⊤) (hlt : ∀ i ∈ s.erase i₀, v (g i₀) < v (g i)) :
    v (∑ i ∈ s, g i) = v (g i₀) := by
  rw [← add_sum_erase s g hi]
  exact AddValuation.map_add_eq_of_lt_left v (AddValuation.map_lt_sum v h0 hlt)
end Formalism.CyclotomicNorms.NewtonPolygonValuation
