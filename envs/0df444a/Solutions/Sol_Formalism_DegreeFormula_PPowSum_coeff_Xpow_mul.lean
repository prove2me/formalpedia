-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.coeff_Xpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:48.269788+00:00
-- url     : https://prove2.me/submissions/5aa60e0f-e30a-4203-a7ce-5664235f0ccd

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
theorem _root_.solution {ι : Type} [Fintype ι] {N : ℕ} (x : ι × Fin N) (k : ℕ)
    (m : (ι × Fin N) →₀ ℕ) (P : MvPolynomial (ι × Fin N) ℝ) :
    (X x ^ k * P).coeff m = if k ≤ m x then P.coeff (m - Finsupp.single x k) else 0 := by
  rw [X_pow_eq_monomial, coeff_monomial_mul', one_mul]
  by_cases h : k ≤ m x
  · rw [if_pos (Finsupp.single_le_iff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (Finsupp.single_le_iff.mp h')), if_neg h]
end Formalism.DegreeFormula.PPowSum
