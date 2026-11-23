-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:49.434803+00:00
-- url     : https://prove2.me/submissions/e3043a3d-5c2b-4e2e-8a9d-628e084650bf

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_P2M_CompanionTheory_D_gk_admitted_FinOfPIAux_word_range__04080a514807
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_word_cases
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_ofFn_val
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply


attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply

set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (E : H →L[ℂ] H) (M : ℕ) (φ : ℕ → H →L[ℂ] ℂ) (x : ℕ → H)
omit [CompleteSpace H]
namespace CompanionTheory.D.gk.admitted.FinOfPIAux
theorem _root_.solution (hφ : ∀ i ≤ M, ∀ j ≤ M, φ i (E (x j)) = if i = j then 1 else 0) :
    stdPoly E (fun a : Fin M => (φ (a + 1)).smulRight (x a)) (x M) = E (x 0) := by
  have hm : ∀ π : Equiv.Perm (Fin M), (List.ofFn fun i => (φ (π i + 1)).smulRight (x (π i))) =
      (List.ofFn fun i => (π i : ℕ)).map fun a => (φ (a + 1)).smulRight (x a) := by
    intro π
    rw [List.map_ofFn]; rfl
  rw [stdPoly, sum_apply, Finset.sum_eq_single 1]
  · rw [hm]
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one, id]
    rw [ofFn_val, word_range' E M φ x hφ M 0 (by omega)]
  · intro π _ hπ
    rw [hm, mul_apply_eq_comp]
    rcases word_cases E M φ x hφ (List.ofFn fun i => (π i : ℕ)) (by simp [List.mem_ofFn]) with h | ⟨k, hk, h⟩
    · rw [h, map_zero]
    · exfalso
      apply hπ
      rw [List.length_ofFn] at hk h
      obtain rfl : k = 0 := by omega
      rw [← ofFn_val] at h
      ext i
      exact congrFun (List.ofFn_injective h) i
  · intro h; exact absurd (Finset.mem_univ _) h
end CompanionTheory.D.gk.admitted.FinOfPIAux
