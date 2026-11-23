-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.dec_of_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:12.208841+00:00
-- url     : https://prove2.me/submissions/53014b0b-788f-4d96-9cf8-7fd772a33447

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_pr_pr
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_adapted
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_pr_eq_iff
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_dec
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Dec_of_conj
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_congr
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_conjTranspose
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_diagonal
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_mul_dp
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open Matrix PI.UpqRep
open CompanionTheory.D.gk.admitted.CholeskyDecomposition
variable {n : ℕ}
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
theorem _root_.solution {ε : Fin n → Bool} (hε : Monotone ε) : Dec (Jm ε) := by
  classical
  have hA := adapted hε
  have hp : ∀ i, pr ε (pr ε i) = i := pr_pr ε
  have hqq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hqs : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hsg2 : ∀ i, sg ε i * sg ε i = 1 := fun i => by unfold sg; split_ifs <;> norm_num
  have hsgs : ∀ i, star (sg ε i) = sg ε i := fun i => by unfold sg; split_ifs <;> simp
  have hnf : ∀ i, ¬ε i.rev = ε i →
      pr ε i = i.rev ∧ ¬ε (pr ε i).rev = ε (pr ε i) ∧ sg ε (pr ε i) = -sg ε i := by
    intro i h
    have hpi : pr ε i = i.rev := by unfold pr; rw [if_neg h]
    refine ⟨hpi, ?_, ?_⟩
    · rw [hpi, Fin.rev_rev]
      exact fun e => h e.symm
    · rw [hpi]
      unfold sg
      cases hx : ε i <;> cases hy : ε i.rev <;> simp_all
  generalize hq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = q at hqq hqs
  let α : Fin n → ℂ := fun i => if ε i.rev = ε i then 1 else q
  let β : Fin n → ℂ := fun i => if ε i.rev = ε i then 0 else sg ε i * q
  have hαs : ∀ i, star (α i) = α i := fun i => by simp only [α]; split_ifs <;> simp [hqs]
  have hβs : ∀ i, star (β i) = β i := fun i => by simp only [β]; split_ifs <;> simp [hqs, hsgs]
  have hVt : (dp (pr ε) α β).conjTranspose = dp (pr ε) α (fun i => β (pr ε i)) := by
    rw [dp_conjTranspose hp]
    simp only [hαs, hβs]
  have hJ : Jm ε = dp (pr ε) (sg ε) 0 := by
    rw [dp_diagonal]
    rfl
  apply Dec.of_conj (V := dp (pr ε) α β)
  · rw [hVt, dp_mul_dp hp, ← Matrix.diagonal_one, ← dp_diagonal (pr ε)]
    apply dp_congr
    · intro i hi
      have h := pr_eq_iff.mp hi
      simp [α, β, h, hi]
    · intro i hi
      have h : ¬ε i.rev = ε i := fun e => hi (pr_eq_iff.mpr e)
      obtain ⟨hpi, hpp, hs⟩ := hnf i h
      simp only [α, β, h, hpp, ↓reduceIte, hs, Pi.zero_apply]
      constructor
      · linear_combination (1 + sg ε i * sg ε i) * hqq + (1 / 2 : ℂ) * hsg2 i
      · ring
  · have key : (dp (pr ε) α β).conjTranspose * Jm ε * dp (pr ε) α β = dp (pr ε) 0 (wt ε) := by
      rw [hVt, hJ, dp_mul_dp hp, dp_mul_dp hp]
      apply dp_congr
      · intro i hi
        have h := pr_eq_iff.mp hi
        simp [α, β, h, hi, wt]
      · intro i hi
        have h : ¬ε i.rev = ε i := fun e => hi (pr_eq_iff.mpr e)
        obtain ⟨hpi, hpp, hs⟩ := hnf i h
        simp only [α, β, wt, h, hpp, ↓reduceIte, hs, Pi.zero_apply]
        constructor
        · linear_combination (-(sg ε i) * q * q) * hsg2 i
        · linear_combination (2 * sg ε i * sg ε i) * hqq + hsg2 i
    rw [key]
    exact hA.dec
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
