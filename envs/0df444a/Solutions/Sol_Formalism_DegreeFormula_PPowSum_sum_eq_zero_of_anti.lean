-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.sum_eq_zero_of_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:45.187275+00:00
-- url     : https://prove2.me/submissions/d60bc85c-d975-4ed1-938a-71fb04702d17

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PPowSum
theorem _root_.solution {G : Type*} [Group G] [Fintype G] (ρ : G) (F : G → ℝ)
    (h : ∀ g, F (ρ * g) = -F g) : ∑ g, F g = 0 := by
  have h1 : ∑ g, F (ρ * g) = ∑ g, F g := Fintype.sum_equiv (Equiv.mulLeft ρ) _ _ (fun _ => rfl)
  simp only [h, Finset.sum_neg_distrib] at h1
  linarith
end Formalism.DegreeFormula.PPowSum
