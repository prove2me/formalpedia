-- Prove2me | solution 1 for D1Bound5.finiteQResidual_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:44:42.154108+00:00
-- url     : https://prove2.me/submissions/054cf55b-b487-4b3e-80b0-98d3958717f2

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQResidualBound_Definitions
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions
import Theorems.Thm_D1Bound5_finiteQResidual_eq_remainders
import Theorems.Thm_D1Bound5_finiteQTailSide_norm_le

section
namespace D1Bound5







/-- The actual finite-Q pair residual has the manuscript's strict bound.
It follows from convergent Taylor estimates, explicit cancellations, and
the actual anchor moduli. -/
theorem _root_.solution
    (u v c : ℂ) (A T : ℝ) (hA : 0 < A)
    (hAu : A ≤ ‖u‖) (hAv : A ≤ ‖v‖)
    (huT : ‖u‖ ≤ T) (hvT : ‖v‖ ≤ T) (hAC : 1000 ≤ A*‖c‖) :
    ‖finiteQResidual u v c‖ < 3*T/(2*A^2*‖c‖^4) := by
  have hu : u ≠ 0 := norm_pos_iff.mp (hA.trans_le hAu)
  have hv : v ≠ 0 := norm_pos_iff.mp (hA.trans_le hAv)
  have hc : c ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero, mul_zero] at hAC
    norm_num at hAC
  have hT : 0 < T := (hA.trans_le hAu).trans_le huT
  have hC : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have heq : finiteQResidual u v c = finiteQTailSide u v c-finiteQTailSide v u c := by
    rw [finiteQResidual_eq_remainders u v c hu hv hc]
    unfold finiteQTailSide
    ring
  have hside1 := finiteQTailSide_norm_le u v c A T hA hAu huT hvT hAC
  have hside2 := finiteQTailSide_norm_le v u c A T hA hAv hvT huT hAC
  calc
    _ ≤ ‖finiteQTailSide u v c‖+‖finiteQTailSide v u c‖ := by rw [heq]; exact norm_sub_le _ _
    _ ≤ (625/888 : ℝ)*T/(A^2*‖c‖^4)+(625/888 : ℝ)*T/(A^2*‖c‖^4) :=
      add_le_add hside1 hside2
    _ = (625/444 : ℝ)*T/(A^2*‖c‖^4) := by ring
    _ < 3*T/(2*A^2*‖c‖^4) := by
      apply (div_lt_div_iff₀ (by positivity : 0 < A^2*‖c‖^4)
        (by positivity : 0 < 2*A^2*‖c‖^4)).2
      nlinarith only [mul_pos hT (by positivity : 0 < A^2*‖c‖^4)]

end D1Bound5
end
