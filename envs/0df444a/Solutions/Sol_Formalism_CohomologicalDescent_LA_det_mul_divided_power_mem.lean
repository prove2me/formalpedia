-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.det_mul_divided_power_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:45.359802+00:00
-- url     : https://prove2.me/submissions/9a4f2245-1c69-4369-988b-391e0ca18839

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_divided_power_det_mul_of_ne
import Theorems.Thm_Formalism_CohomologicalDescent_LA_divided_power_zero_det_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_divided_power_succ_det_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {r : ℕ}
    (W : Submodule R (MvPolynomial (Fin r × Fin r) R))
    (hW : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R), f ∈ W →
      rowDiv R a b k f ∈ W) (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : genericDet R r * f ∈ W) : genericDet R r * rowDiv R a b k f ∈ W := by
  by_cases hab : a = b
  · subst hab
    induction k with
    | zero =>
      rw [← divided_power_zero_det_mul]
      exact hW a a 0 _ hf
    | succ k ih =>
      have h1 := hW a a (k + 1) _ hf
      rw [divided_power_succ_det_mul, mul_add] at h1
      have h2 := W.sub_mem h1 ih
      simpa using h2
  · rw [← divided_power_det_mul_of_ne R a b hab]
    exact hW a b k _ hf
end Formalism.CohomologicalDescent.LA
