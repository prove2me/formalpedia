-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:49.758651+00:00
-- url     : https://prove2.me/submissions/de554eae-e728-48d1-be7c-3a7cc97dcab1

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_minor_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_SR
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_sum_perm

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
theorem _root_.solution {p : ℕ} (ι : Fin p → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : Fin p, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : Fin p, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (hp : p ≤ n) :
    xnN (initMinor ℂ ι hp * f) = xnC p m p * xnN f := by
  have h1 := xn_SR ι hι m f hR hW p hp
  rw [Fintype.card_fin] at h1
  have h2 := xn_sum_perm ι f p hp id Function.injective_id
  have h3 : ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => id ∘ π),
      xnN (initMinor ℂ (ι ∘ a) hp * f) = ∑ a : Fin p → Fin p, xnN (initMinor ℂ (ι ∘ a) hp * f) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
    have hna : ¬ Function.Injective (ι ∘ a) := by
      intro hinj
      apply ha
      refine Finset.mem_image.2 ⟨Equiv.ofBijective a (Finite.injective_iff_bijective.1 hinj.of_comp),
        Finset.mem_univ _, ?_⟩
      rfl
    rw [xn_minor_zero _ hp hna, zero_mul]
    simp [xnN, fockF]
  rw [← h3, h2] at h1
  have hpos : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  exact mul_left_cancel₀ hpos.ne' h1
end Formalism.BranchingDeterminantCap
