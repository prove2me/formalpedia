-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.integral_cube_ee
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:32.507674+00:00
-- url     : https://prove2.me/submissions/47eaa28e-9d87-4fd3-b6e8-5b2f86849ca0

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integral_one_dim
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_ee_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution (τ : Fin d → ℤ) :
    ∫ z, (((cube d).indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ) * ee z τ = if τ = 0 then 1 else 0 := by
  have h1 : ∀ z : Fin d → ℝ, (((cube d).indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ) * ee z τ =
      ∏ j, (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator
        (fun t : ℝ => Complex.exp (2 * π * Complex.I * (((τ j : ℝ) : ℂ) * (t : ℂ)))) (z j) := by
    intro z
    by_cases hz : z ∈ cube d
    · rw [Set.indicator_of_mem hz, Complex.ofReal_one, one_mul, ee_eq_prod]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Set.indicator_of_mem]
      exact ⟨hz.1 j, hz.2 j⟩
    · rw [Set.indicator_of_notMem hz, Complex.ofReal_zero, zero_mul]
      have : ∃ j, z j ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
        by_contra hcon
        push Not at hcon
        exact hz ⟨fun j => (hcon j).1, fun j => (hcon j).2⟩
      obtain ⟨j, hj⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)).symm
  simp_rw [h1]
  rw [integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_indicator measurableSet_Icc, integral_one_dim]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]
end Formalism.FourierDecayAlt.P.HLsc
