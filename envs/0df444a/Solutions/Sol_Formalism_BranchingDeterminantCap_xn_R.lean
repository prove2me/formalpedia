-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:46.20488+00:00
-- url     : https://prove2.me/submissions/44699a4b-0ae1-4a87-ad8d-5d2dac542754

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm

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
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (μ : ℕ → ℕ) (p i : ℕ) (hi : i < p) (h0 : ∀ j, p ≤ j → μ j = 0) (m : ℕ) (hm : p ≤ m) :
    (∏ j ∈ Finset.range m, xnT (xnAdd μ p) i j) * ((p : ℝ) - i + μ i) =
      (∏ j ∈ Finset.range m, xnT μ i j) * ((m : ℝ) - i + μ i) := by
  have hlt : ∀ j, j < p → xnT (xnAdd μ p) i j = xnT μ i j := by
    intro j hj
    simp only [xnT, xnAdd, if_pos hi, if_pos hj]
    split_ifs <;> push_cast <;> ring
  obtain ⟨d, rfl⟩ : ∃ d, m = p + d := ⟨m - p, by omega⟩
  clear hm
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    rw [Finset.prod_congr rfl fun j hj => hlt j (Finset.mem_range.1 hj)]
  | succ d ih =>
    have hμ : μ (p + d) = 0 := h0 _ (by omega)
    have h1 : i < p + d := by omega
    have h2 : ¬ (p + d < p) := by omega
    have e1 : xnT (xnAdd μ p) i (p + d) =
        ((μ i : ℝ) + 1 + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i) := by
      simp only [xnT, xnAdd, if_pos h1, if_pos hi, if_neg h2, hμ]
      push_cast
      ring
    have e2 : xnT μ i (p + d) = ((μ i : ℝ) + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i) := by
      simp only [xnT, if_pos h1, hμ]
      push_cast
      ring
    rw [← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_range_succ, e1, e2]
    push_cast at ih ⊢
    linear_combination (((μ i : ℝ) + 1 + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i)) * ih
end Formalism.BranchingDeterminantCap
