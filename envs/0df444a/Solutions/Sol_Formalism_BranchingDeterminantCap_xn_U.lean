-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_U
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:50.148664+00:00
-- url     : https://prove2.me/submissions/d660bdbe-68ca-4fcc-a7a2-7b3a7cf348f9

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnN_nonneg
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
theorem _root_.solution (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) (J : Fin p → κ) (hJ : Function.Injective J) :
    xnN (initMinor ℂ (ι ∘ J) hp * f) ≤ xnC (Fintype.card κ) m p * xnN f := by
  have h1 := xn_SR ι hι m f hR hW p hp
  have h2 := xn_sum_perm ι f p hp J hJ
  have h3 : ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => J ∘ π),
      xnN (initMinor ℂ (ι ∘ a) hp * f) ≤ ∑ a : Fin p → κ, xnN (initMinor ℂ (ι ∘ a) hp * f) :=
    Finset.sum_le_univ_sum_of_nonneg fun a => xnN_nonneg _
  rw [h1, h2] at h3
  exact le_of_mul_le_mul_left h3 (by exact_mod_cast p.factorial_pos)
end Formalism.BranchingDeterminantCap
