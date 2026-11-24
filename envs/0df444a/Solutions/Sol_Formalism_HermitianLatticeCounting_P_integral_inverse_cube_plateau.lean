-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integral_inverse_cube_plateau
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:46.838826+00:00
-- url     : https://prove2.me/submissions/a1dd2df8-323c-4ccc-b805-490dec6c7d50

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integral_radial_inverse_cube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
open MeasureTheory
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (H : ℝ) (hH : 0 < H) :
    Integrable (fun z : ℂ => ((max 1 (‖z‖ / H)) ^ 3)⁻¹) ∧
      ∫ z : ℂ, ((max 1 (‖z‖ / H)) ^ 3)⁻¹ = 3 * Real.pi * H ^ 2 := by
  obtain ⟨hi, hv⟩ := integral_radial_inverse_cube H hH
  have hdim : finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  constructor
  · have := (integrable_fun_norm_addHaar (volume : Measure ℂ)
      (f := fun y : ℝ => ((max 1 (y / H)) ^ 3)⁻¹)).2 (by
        simpa only [hdim, Nat.add_one_sub_one, pow_one, smul_eq_mul] using hi)
    exact this
  · have := integral_fun_norm_addHaar (volume : Measure ℂ) (fun y : ℝ => ((max 1 (y / H)) ^ 3)⁻¹)
    rw [this, hdim]
    simp only [Nat.add_one_sub_one, pow_one, smul_eq_mul]
    rw [hv]
    have hb : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
      rw [measureReal_def, Complex.volume_ball]; simp
    rw [hb]; simp; ring
end Formalism.HermitianLatticeCounting.P
