-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.parseval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:20.573847+00:00
-- url     : https://prove2.me/submissions/0da98222-a339-47bc-9ce6-8af3a1a409da

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integral_mul_normSq_tp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integral_cube_ee
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_measurableSet_cube
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integrable_indicator_cube

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
theorem _root_.solution (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ∫ z in cube d, ‖tp B c z‖ ^ 2 = ∑ σ ∈ B, ‖c σ‖ ^ 2 := by
  have h := integral_mul_normSq_tp (integrable_indicator_cube (d := d)) B c
  simp_rw [integral_cube_ee, sub_eq_zero] at h
  have h2 : (∫ z, (cube d).indicator (fun _ => (1 : ℝ)) z * ‖tp B c z‖ ^ 2) =
      ∫ z in cube d, ‖tp B c z‖ ^ 2 := by
    rw [← integral_indicator measurableSet_cube]
    congr 1
    funext z
    by_cases hz : z ∈ cube d
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
  rw [h2] at h
  have h3 : (∑ σ ∈ B, ∑ σ' ∈ B, (if σ = σ' then (1 : ℂ) else 0) * c σ * starRingEnd ℂ (c σ')) =
      ((∑ σ ∈ B, ‖c σ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun σ hσ => ?_)
    simp_rw [ite_mul, zero_mul, one_mul]
    rw [Finset.sum_ite_eq, if_pos hσ, Complex.mul_conj']
  rw [h3] at h
  exact_mod_cast h
end Formalism.FourierDecayAlt.P.HLsc
