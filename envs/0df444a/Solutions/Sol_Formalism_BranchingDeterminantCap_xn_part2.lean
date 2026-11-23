-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_part2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:02.031669+00:00
-- url     : https://prove2.me/submissions/d1b378b1-3914-4ff7-9be8-8171cb516345

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_lap
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_cof_last

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
theorem _root_.solution (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (m : ℂ)
    (h0 : ∀ t : Fin n, t.val < p → ∑ b : κ, X (ι b, t) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = 0)
    (h1 : ∑ b : κ, X (ι b, (⟨p, hp⟩ : Fin n)) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = C m * f) :
    ∑ b : κ, initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp *
        pderiv (ι b, (⟨p, hp⟩ : Fin n)) f =
      C m * (initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) * f) := by
  have hl : Fin.castLE hp (Fin.last p) = (⟨p, hp⟩ : Fin n) := Fin.ext (by simp)
  simp only [xn_lap ι hp a, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_eq_single (Fin.last p)]
  · simp only [hl]
    simp_rw [mul_right_comm _ (xnCof ι hp a (Fin.last p)) _]
    rw [← Finset.sum_mul, h1, xn_cof_last]
    ring
  · intro j _ hj
    have hjv : (Fin.castLE hp j).val < p := by
      have h3 : (j : ℕ) ≠ p := fun h => hj (Fin.ext (by simpa using h))
      have h4 := j.isLt
      simp only [Fin.coe_castLE]
      omega
    simp_rw [mul_right_comm _ (xnCof ι hp a j) _]
    rw [← Finset.sum_mul, h0 (Fin.castLE hp j) hjv, zero_mul]
  · simp
end Formalism.BranchingDeterminantCap
