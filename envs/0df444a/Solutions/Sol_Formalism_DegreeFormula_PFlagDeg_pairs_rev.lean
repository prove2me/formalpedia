-- Prove2me | solution 1 for Formalism.DegreeFormula.PFlagDeg.pairs_rev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:26.883095+00:00
-- url     : https://prove2.me/submissions/55f55184-3f13-4668-b06b-d3d12c3d6512

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg
namespace Formalism.DegreeFormula.PFlagDeg
theorem _root_.solution {N : ℕ} (v : Fin N → ℝ) :
    ∏ i : Fin N, ∏ k : Fin N, (if i < k then v i - v k else 1) =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev j) - v (Fin.rev i)) := by
  calc ∏ i : Fin N, ∏ k : Fin N, (if i < k then v i - v k else 1)
      = ∏ i : Fin N, ∏ k : Fin N,
          (if Fin.rev i < Fin.rev k then v (Fin.rev i) - v (Fin.rev k) else 1) := by
        rw [← Equiv.prod_comp Fin.revPerm]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Equiv.prod_comp Fin.revPerm]
        rfl
    _ = ∏ k : Fin N, ∏ i : Fin N, (if k < i then v (Fin.rev i) - v (Fin.rev k) else 1) := by
        rw [Finset.prod_comm]
        simp only [Fin.rev_lt_rev]
    _ = _ := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← Finset.filter_lt_eq_Ioi, Finset.prod_filter]
end Formalism.DegreeFormula.PFlagDeg
