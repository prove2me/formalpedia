-- Prove2me | solution 1 for D1Bound5.coupled_phase_row_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:59:32.808895+00:00
-- url     : https://prove2.me/submissions/f0b19405-5855-42a9-b6b7-0ddea442c096

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_CoupledPhaseBounds_Definitions
import Definitions.Def_D1Bound5_CoupledPhaseGeometry_Definitions
import Theorems.Thm_D1Bound5_coupled_phase_polynomial_bound

section
namespace D1Bound5












/-- All five printed phase constants follow from exact rational critical
brackets. Decimal approximations are not used in the proof. -/
theorem _root_.solution (q F : ℝ) (hrow : CoupledPhaseRow q F)
    (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) : coupledPhasePolynomial q x < F := by
  rcases hrow with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact coupled_phase_polynomial_bound 8 (64870519/536870912) (8108815/67108864) 269
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [phaseCritical]) (by norm_num [phaseCritical]) (by norm_num) x hx hx2
  · exact coupled_phase_polynomial_bound (8/3) (157513737/536870912) (78756869/268435456) 368
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [phaseCritical]) (by norm_num [phaseCritical]) (by norm_num) x hx hx2
  · exact coupled_phase_polynomial_bound (12/7) (195093997/536870912) (97546999/268435456) 540
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [phaseCritical]) (by norm_num [phaseCritical]) (by norm_num) x hx hx2
  · exact coupled_phase_polynomial_bound (3/2) (203350297/536870912) (101675149/268435456) 637
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [phaseCritical]) (by norm_num [phaseCritical]) (by norm_num) x hx hx2
  · exact coupled_phase_polynomial_bound (18/17) (107257323/268435456) (214514647/536870912) 1121
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [phaseCritical]) (by norm_num [phaseCritical]) (by norm_num) x hx hx2



end D1Bound5
end
