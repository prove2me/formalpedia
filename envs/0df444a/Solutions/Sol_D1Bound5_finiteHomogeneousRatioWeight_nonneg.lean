-- Prove2me | solution 1 for D1Bound5.finiteHomogeneousRatioWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:32.725136+00:00
-- url     : https://prove2.me/submissions/1e15e69c-de79-415b-80d0-2f48aaa3a1cd

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions

section
noncomputable section

namespace D1Bound5



theorem _root_.solution (n : ℕ) (v : Fin (n+1) → ℤ)
    (r : ℝ) (hr : 0 ≤ r) : 0 ≤ finiteHomogeneousRatioWeight n v r := by
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (pow_nonneg hr _))









end D1Bound5
end
