-- Prove2me | solution 1 for D1Bound5.fiveRegionAnchorRatio_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:54:51.572652+00:00
-- url     : https://prove2.me/submissions/bc26d565-2c95-4352-b324-8e87e329982f

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









theorem _root_.solution (r : Fin 5) : 0 ≤ fiveRegionAnchorRatio r := by
  fin_cases r <;> norm_num [fiveRegionAnchorRatio]



end D1Bound5
end
