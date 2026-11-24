-- Prove2me | solution 1 for Formalism.G0.DetDividesP.coprime_det_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:50.434913+00:00
-- url     : https://prove2.me/submissions/bb938e4c-6585-41e5-a2e1-a3e8934d540c

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_degreeOf_eq_zero_of_dvd
import Theorems.Thm_Formalism_G0_DetDividesP_degreeOf_det_eq_zero
import Theorems.Thm_Formalism_G0_DetDividesP_isUnit_of_degreeOf_eq_zero
import Theorems.Thm_Formalism_G0_DetDividesP_det_Tm_ne_zero
import Theorems.Thm_Formalism_G0_DetDividesP_adj_Tm_ne_zero
import Theorems.Thm_Formalism_G0_DetDividesP_rho_cc
import Theorems.Thm_Formalism_G0_DetDividesP_rho_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (A : Fin r → ι) (hA : Function.Injective A) (lst : Fin r) :
    IsRelPrime (Tm K A).det (((Tm K A).adjugate.mulVec (Wv K A)) lst) := by
  intro p hpD hpc
  have hD := det_Tm_ne_zero (K := K) A hA
  have hp0 : p ≠ 0 := by rintro rfl; exact hD (zero_dvd_iff.mp hpD)
  have hinr : ∀ i, degreeOf (Sum.inr i) p = 0 := fun i =>
    degreeOf_eq_zero_of_dvd _ hpD hD (degreeOf_det_eq_zero _ _ fun a b => by
      simp [Tm, degreeOf_X_of_ne])
  have hrow : ∀ l b, degreeOf (Sum.inl (A l, b)) p = 0 := by
    intro l b
    have h1 : p ∣ (Tm K A).adjugate lst l := by
      have := map_dvd (rho K A l) hpc
      rwa [rho_fix A l hinr, rho_cc A hA] at this
    refine degreeOf_eq_zero_of_dvd _ h1 (adj_Tm_ne_zero A hA lst l) ?_
    rw [Matrix.adjugate_apply]
    refine degreeOf_det_eq_zero _ _ fun i j => ?_
    by_cases hi : i = l
    · subst hi
      rw [Matrix.updateRow_self, Pi.single_apply]
      split_ifs
      · exact degreeOf_one _
      · exact degreeOf_zero _
    · rw [Matrix.updateRow_ne hi]
      simp only [Tm, Matrix.of_apply]
      apply degreeOf_X_of_ne
      intro h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      exact hi (hA h.1).symm
  apply isUnit_of_degreeOf_eq_zero hp0
  intro x
  rcases x with ⟨i, b⟩ | i
  · by_cases hi : i ∈ Set.range A
    · obtain ⟨l, rfl⟩ := hi; exact hrow l b
    · refine degreeOf_eq_zero_of_dvd _ hpD hD (degreeOf_det_eq_zero _ _ fun a c => ?_)
      simp only [Tm, Matrix.of_apply]
      apply degreeOf_X_of_ne
      intro h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      exact hi ⟨a, h.1.symm⟩
  · exact hinr i
end Formalism.G0.DetDividesP
