-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.cpow_half_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:35.335147+00:00
-- url     : https://prove2.me/submissions/820f3578-3418-4d16-8801-0316dce511ed

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution (u : ℂ) (hu : 0 < u.re) (R : ℝ) (hR : 0 < R) :
    ((Real.pi : ℂ) / u) ^ (1 / 2 : ℂ) * ((Real.pi : ℂ) / ((R : ℂ) / u)) ^ (1 / 2 : ℂ) =
      ((Real.pi / Real.sqrt R : ℝ) : ℂ) := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have harg : u.arg ≠ Real.pi := by
    intro h; have := (Complex.arg_eq_pi_iff.1 h).1; linarith
  have hπ := Real.pi_pos
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hπc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
  have e1 : (Real.pi : ℂ) / u = ((Real.pi : ℝ) : ℂ) * u⁻¹ := div_eq_mul_inv _ _
  have e2 : (Real.pi : ℂ) / ((R : ℂ) / u) = ((Real.pi / R : ℝ) : ℂ) * u := by
    push_cast; field_simp
  have hpR : 0 < Real.pi / R := by positivity
  rw [e1, e2, Complex.cpow_def_of_ne_zero (mul_ne_zero hπc (inv_ne_zero hu0)),
    Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hpR.ne') hu0), ← Complex.exp_add,
    Complex.log_ofReal_mul hπ (inv_ne_zero hu0), Complex.log_ofReal_mul hpR hu0, Complex.log_inv _ harg]
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have e3 : Real.pi / Real.sqrt R = Real.exp (Real.log Real.pi - Real.log R / 2) := by
    rw [← Real.log_sqrt hR.le, ← Real.log_div hπ.ne' hs.ne', Real.exp_log (by positivity)]
  rw [e3, Real.log_div hπ.ne' hR.ne']
  push_cast
  congr 1
  ring
end Formalism.FourierDecayAlt.P.G8
