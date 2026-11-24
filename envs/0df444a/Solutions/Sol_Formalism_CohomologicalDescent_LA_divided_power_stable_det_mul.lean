-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.divided_power_stable_det_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:46.996795+00:00
-- url     : https://prove2.me/submissions/843c4cc9-b024-4240-8e90-7de895d5b813

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
    (L : Submodule R (MvPolynomial (Fin r × Fin r) R))
    (hs : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R), f ∈ L →
      rowDiv R a b k f ∈ L) (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : f ∈ L.map (LinearMap.mulLeft R (genericDet R r))) :
    rowDiv R a b k f ∈ L.map (LinearMap.mulLeft R (genericDet R r)) := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  rw [LinearMap.mulLeft_apply]
  by_cases hab : a = b
  · subst hab
    cases k with
    | zero =>
      rw [divided_power_zero_det_mul]
      exact Submodule.mem_map.mpr ⟨_, hs a a 0 g hg, by simp⟩
    | succ k =>
      rw [divided_power_succ_det_mul]
      exact Submodule.mem_map.mpr ⟨_, L.add_mem (hs a a (k + 1) g hg) (hs a a k g hg), by simp⟩
  · rw [divided_power_det_mul_of_ne R a b hab]
    exact Submodule.mem_map.mpr ⟨_, hs a b k g hg, by simp⟩
end Formalism.CohomologicalDescent.LA
