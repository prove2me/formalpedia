-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_sum_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:27.135817+00:00
-- url     : https://prove2.me/submissions/448acb85-1f79-4c5a-aa94-a78dcad08868

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_minor_perm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnN_sg

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
theorem _root_.solution (ι : κ → Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ) (p : ℕ) (hp : p ≤ n)
    (J : Fin p → κ) (hJ : Function.Injective J) :
    ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => J ∘ π),
      xnN (initMinor ℂ (ι ∘ a) hp * f) = (p.factorial : ℝ) * xnN (initMinor ℂ (ι ∘ J) hp * f) := by
  rw [Finset.sum_image (by intro x _ y _ hxy; exact Equiv.ext fun i => hJ (congrFun hxy i))]
  have e : ∀ π : Equiv.Perm (Fin p), xnN (initMinor ℂ (ι ∘ (J ∘ π)) hp * f) =
      xnN (initMinor ℂ (ι ∘ J) hp * f) := by
    intro π
    rw [xn_minor_perm ι hp J π, mul_assoc, xnN_sg]
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
end Formalism.BranchingDeterminantCap
