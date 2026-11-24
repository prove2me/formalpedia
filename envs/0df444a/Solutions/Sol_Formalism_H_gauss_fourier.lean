-- Prove2me | solution 1 for Formalism.H.gauss_fourier
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:25.154695+00:00
-- url     : https://prove2.me/submissions/830cc83c-ef93-471b-a292-065b9e0b01f1

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
import Theorems.Thm_Formalism_H_gauss_fun_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
open Formalism Formalism.H
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution (t : ℝ) (ht : 0 < t) (w : V) :
    (𝓕 (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) : V → ℂ) w =
      ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) * (Real.exp (-Real.pi * ‖w‖ ^ 2 / t) : ℂ) := by
  have hb : 0 < (((Real.pi * t : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; exact mul_pos Real.pi_pos ht
  rw [gauss_fun_eq, fourier_gaussian_innerProductSpace hb w]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have e1 : (Real.pi : ℂ) / ((Real.pi * t : ℝ) : ℂ) = ((t⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  have e2 : ((t⁻¹ : ℝ) : ℂ) ^ ((Module.finrank ℝ V : ℂ) / 2) =
      ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((Module.finrank ℝ V : ℂ) / 2) = (((Module.finrank ℝ V : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_div]
  rw [e1, e2, Complex.ofReal_exp]
  congr 2
  push_cast
  field_simp
end Formalism.H
