-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.pk_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:53.381136+00:00
-- url     : https://prove2.me/submissions/6bb1fc41-e4d5-46eb-bb0e-be4b60cebb96

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_fac_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_pk_zero

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
theorem _root_.solution (y : Fin d → ℝ) (hy : y ∈ cube d) (hy0 : y ≠ 0) : pk y < pk (0 : Fin d → ℝ) := by
  rw [pk_zero]
  by_cases hz : ∃ j, ‖1 + Complex.exp (2 * π * Complex.I * (y j : ℂ))‖ ^ 2 = 0
  · obtain ⟨j, hj⟩ := hz
    unfold pk
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hj]
    positivity
  · push Not at hz
    have h4 : (4 : ℝ) ^ d = ∏ _j : Fin d, (4 : ℝ) := by simp
    rw [h4]
    unfold pk
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hy0 (funext hcon)
    refine Finset.prod_lt_prod (fun i _ => lt_of_le_of_ne (by positivity) (hz i).symm)
      (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · rw [fac_eq]; linarith [Real.cos_le_one (2 * π * y i)]
    · rw [fac_eq]
      have h1 := hy.1 j
      have h2 := hy.2 j
      have hne : Real.cos (2 * π * y j) ≠ 1 := by
        intro h
        rw [Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])] at h
        have : (2 * π) ≠ 0 := by positivity
        exact hj ((mul_eq_zero.1 h).resolve_left this)
      have := lt_of_le_of_ne (Real.cos_le_one (2 * π * y j)) hne
      linarith
end Formalism.FourierDecayAlt.P.HLsc
