-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cutoff_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:33.493278+00:00
-- url     : https://prove2.me/submissions/53d51a5b-be9e-4319-99a4-97c5b8f89927

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integrable_radial_iff
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integral_complex_radial_eq_two_pi_mul_integral_Ioi
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_mul_cutoff_of_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_mul_cutoff_of_gt
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integrable_cutoff_below
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integrable_cutoff_beyond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.CutoffIntegralFormula := by
  intro K L hK hL
  have hK0 : 0 ≤ K := by linarith
  have hU : Set.Ioi (0 : ℝ) = Set.Ioc 0 L ∪ Set.Ioi L := (Set.Ioc_union_Ioi_eq_Ioi hL.le).symm
  constructor
  · rw [integrable_radial_iff (fun y => TruncationCutoff K L y), hU]
    exact (integrable_cutoff_below hK0).union (integrable_cutoff_beyond hK hL)
  · rw [integral_complex_radial_eq_two_pi_mul_integral_Ioi (fun y => TruncationCutoff K L y), hU,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (integrable_cutoff_below hK0)
        (integrable_cutoff_beyond hK hL),
      setIntegral_congr_fun measurableSet_Ioc (fun y hy => mul_cutoff_of_le hK0 hy.1 hy.2),
      setIntegral_congr_fun measurableSet_Ioi (fun y hy => mul_cutoff_of_gt hK0 hL hy),
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : 1 - K < -1) hL,
      ← intervalIntegral.integral_of_le hL.le, integral_id]
    have e : L ^ K * L ^ (1 - K + 1) = L ^ 2 := by
      rw [← Real.rpow_add hL, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hK2 : K - 2 ≠ 0 := by linarith [hK]
    have hK3 : 1 - K + 1 ≠ 0 := by
      intro h
      apply hK2
      linarith
    have e2 : L ^ K * (-L ^ (1 - K + 1) / (1 - K + 1)) = L ^ 2 / (K - 2) := by
      rw [← e]
      field_simp
      ring
    rw [e2]
    field_simp
    ring
end Formalism.HermitianLatticeCounting.P
