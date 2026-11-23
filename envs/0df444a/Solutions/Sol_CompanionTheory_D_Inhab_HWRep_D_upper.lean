-- Prove2me | solution 1 for CompanionTheory.D.Inhab.HWRep.D_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:56.655154+00:00
-- url     : https://prove2.me/submissions/8ea17448-f7e4-431e-8b5f-b6983d6173c7

import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_HWRepD
import Theorems.Thm_CompanionTheory_D_Inhab_HWRep_hasDerivAt_curve
import Theorems.Thm_CompanionTheory_D_Inhab_HWRep_curve_deriv
import Theorems.Thm_CompanionTheory_D_Inhab_HWRep_curve_tri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab CompanionTheory.D.Inhab.HWRep
variable {k : ℕ} {ν : Fin k → ℤ} (R : HWRep k ν)
namespace CompanionTheory.D.Inhab.HWRep
theorem _root_.solution {a b : Fin k} (hab : a < b) : R.D (Matrix.single a b 1) *ᵥ R.v0 = 0 := by
  have h := R.hasDerivAt_curve (fun t : ℝ => 1 + (t : ℂ) • Matrix.single a b (1 : ℂ)) _ (by simp)
    (curve_deriv a b) R.v0
  have hdiag : ∀ (t : ℂ) c, (1 + t • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c c = 1 := by
    intro t c
    have : ¬(a = c ∧ b = c) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
    simp [Matrix.single_apply, this]
  have e : (fun t : ℝ => R.ρ (1 + (t : ℂ) • Matrix.single a b (1 : ℂ)) *ᵥ R.v0) = fun _ => R.v0 := by
    funext t
    rw [R.hw _ (curve_tri hab.le _)]
    · simp only [hdiag]; simp
    · rw [Matrix.det_of_upperTriangular (curve_tri hab.le _)]
      simp only [hdiag]; simp
  rw [e] at h
  exact h.unique (hasDerivAt_const _ _)
end CompanionTheory.D.Inhab.HWRep
