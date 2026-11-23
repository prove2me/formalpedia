-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_part1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:41.874803+00:00
-- url     : https://prove2.me/submissions/61d8c904-5933-4ce9-b412-d11e93e33d61

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_pderiv_supported
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_minor_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_lap
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_cof_last
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_cof_supported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (ι : κ → Fin r) (hι : Function.Injective ι) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ)
    (b : κ) :
    pderiv (ι b, (⟨p, hp⟩ : Fin n)) (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp) =
      if b ∈ Finset.univ.image a then 0 else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) := by
  split_ifs with hb
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hb
    have hni : ¬ Function.Injective (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) := by
      intro hinj
      have h2 := @hinj (Fin.castSucc i) (Fin.last p) (by simp [hi])
      exact (Fin.castSucc_lt_last i).ne h2
    rw [xn_minor_zero _ hp hni, map_zero]
  · have hns : ((ι b, (⟨p, hp⟩ : Fin n)) : Fin r × Fin n) ∉
        {v : Fin r × Fin n | ∃ i, v.1 = ι (a i)} := by
      rintro ⟨i, hi⟩
      exact hb (Finset.mem_image.2 ⟨i, Finset.mem_univ _, (hι hi).symm⟩)
    rw [xn_lap ι hp a b, map_sum, Finset.sum_eq_single (Fin.last p), ← xn_cof_last ι hp a]
    · rw [Derivation.leibniz, xn_pderiv_supported _ _ hns _ (xn_cof_supported ι hp a _), smul_zero,
        zero_add, MvPolynomial.pderiv_X, smul_eq_mul]
      simp [Pi.single_apply, Fin.ext_iff]
    · intro j _ hj
      have hjv : (j : ℕ) ≠ p := fun h => hj (Fin.ext (by simpa using h))
      rw [Derivation.leibniz, xn_pderiv_supported _ _ hns _ (xn_cof_supported ι hp a _), smul_zero,
        zero_add, MvPolynomial.pderiv_X, smul_eq_mul]
      simp [Pi.single_apply, Fin.ext_iff, hjv]
    · simp
end Formalism.BranchingDeterminantCap
