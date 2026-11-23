-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xnN_sg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:29.998664+00:00
-- url     : https://prove2.me/submissions/d9cf5df5-e62f-4ca4-9019-01800ebb55af

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnSg_mul_self
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnSg_star

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
theorem _root_.solution {σ : Type*} {p : ℕ} (π : Equiv.Perm (Fin p)) (f : MvPolynomial σ ℂ) :
    xnN (C (xnSg π) * f) = xnN f := by
  unfold xnN fockF
  have hc : xnSg π ≠ 0 := fun h0 => by simpa [h0] using xnSg_mul_self π
  rw [MvPolynomial.C_mul']
  first
  | rw [MvPolynomial.support_smul_eq hc]
  | rw [Finsupp.support_smul_eq hc]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul', xnSg_star]
  rw [show ∀ a x y N : ℂ, a * x * (a * y) * N = (a * a) * (x * y * N) from fun _ _ _ _ => by ring,
    xnSg_mul_self, one_mul]
end Formalism.BranchingDeterminantCap
