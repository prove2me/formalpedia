-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.normMinorMonomialLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:12.343944+00:00
-- url     : https://prove2.me/submissions/54e9b023-6c8d-42f3-8650-f63da9b171a1

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_finset_prod_le_prod_of_subset_of_one_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_finset_prod_real_of_forall_one_le


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
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : MonomialMinor := by
  intro N σ c t I J
  classical
  set W : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => if j = σ i then c i else 0 with hW
  set P := ∏ i, max 1 ‖c i‖ with hP
  have hP1 : 1 ≤ P := one_le_finset_prod_real_of_forall_one_le _ _ fun i _ => le_max_left _ _
  by_cases hI : Function.Injective I
  · set g : Equiv.Perm (Fin t) → ℝ := fun π => ∏ i, ‖(W.submatrix I J) (π i) i‖ with hg
    have hdet : ‖(W.submatrix I J).det‖ ≤ ∑ π, g π := by
      rw [Matrix.det_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => ?_)
      rw [hg]
      simp only [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
      have h2 : ‖(((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
      rw [h2, one_mul]
    have hgle : ∀ π, g π ≤ P := by
      intro π
      calc g π ≤ ∏ i, max 1 ‖c (I (π i))‖ := by
            refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
            simp only [hW, Matrix.submatrix_apply, Matrix.of_apply]
            split_ifs
            · exact le_max_right _ _
            · simp
        _ = ∏ i, max 1 ‖c (I i)‖ := Equiv.prod_comp π (fun i => max 1 ‖c (I i)‖)
        _ = ∏ k ∈ Finset.univ.image I, max 1 ‖c k‖ := by
            rw [Finset.prod_image (fun a _ b _ h => hI h)]
        _ ≤ P := finset_prod_le_prod_of_subset_of_one_le _ _ (Finset.subset_univ _) _ fun k _ => le_max_left _ _
    have huniq : ∀ π π', g π ≠ 0 → g π' ≠ 0 → π = π' := by
      intro π π' h h'
      have key : ∀ ρ : Equiv.Perm (Fin t), g ρ ≠ 0 → ∀ i, J i = σ (I (ρ i)) := by
        intro ρ hρ i
        by_contra hne
        apply hρ
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hW, hne]
      ext i
      have := (key π h i).symm.trans (key π' h' i)
      exact congrArg _ (hI (σ.injective this))
    refine hdet.trans ?_
    by_cases hex : ∃ π₀, g π₀ ≠ 0
    · obtain ⟨π₀, h₀⟩ := hex
      rw [Finset.sum_eq_single π₀]
      · exact hgle π₀
      · intro π _ hne
        by_contra hπ
        exact hne (huniq π π₀ hπ h₀)
      · simp
    · push_neg at hex
      rw [Finset.sum_eq_zero fun π _ => hex π]; linarith
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, I a = I b ∧ a ≠ b := by
      simpa [Function.Injective] using hI
    rw [Matrix.det_zero_of_row_eq hne (by ext j; simp [hab])]
    simp; linarith
end Formalism.HermitianLatticeCounting.P
