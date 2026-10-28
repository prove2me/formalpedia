-- Prove2me | solution 1 for D1Bound5.finite_norm_quadratic_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:38.246613+00:00
-- url     : https://prove2.me/submissions/bcb1775f-56df-4d9d-b6c5-6e455776bc31

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

section
namespace D1Bound5





theorem _root_.solution (u v w c : ℂ) :
    ‖u+v*c+w*c^2‖ ≤ ‖u‖+‖v‖*‖c‖+‖w‖*‖c‖^2 := by
  calc
    _ ≤ ‖u+v*c‖+‖w*c^2‖ := norm_add_le _ _
    _ ≤ (‖u‖+‖v*c‖)+‖w*c^2‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by rw [norm_mul, norm_mul, norm_pow]

end D1Bound5
end
