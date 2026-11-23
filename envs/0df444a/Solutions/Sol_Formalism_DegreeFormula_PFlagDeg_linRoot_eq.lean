-- Prove2me | solution 1 for Formalism.DegreeFormula.PFlagDeg.linRoot_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:09.400924+00:00
-- url     : https://prove2.me/submissions/37209a72-e743-447f-af1f-203020ab1f62

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
theorem _root_.solution {ι : Type} [Fintype ι] {N : ℕ} (lam : ι → Fin N → ℝ) :
    linRoot lam = ∑ x : ι × Fin N, (-lam x.1 x.2) • (X x : MvPolynomial (ι × Fin N) ℝ) := by
  unfold linRoot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_eq_C_mul, C_neg, neg_mul]
end Formalism.DegreeFormula.PFlagDeg
