-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xi_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:15:24.533797+00:00
-- url     : https://prove2.me/submissions/0d7b055b-1ed9-4c79-8ceb-0e26d1d0966a

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnW_weylProd
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_stage

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
theorem _root_.solution : XiNorm := by
  unfold XiNorm
  intro n lam sg hI
  have H := xn_stage n lam sg hI n le_rfl
  have hμ : (fun q => xnLam lam q - xnLam lam n) = xnLam lam := by
    funext q
    have h0 : xnLam lam n = 0 := by simp [xnLam]
    rw [h0, Nat.sub_zero]
  have hx : (∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < n),
      (initMinor ℂ (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
        initMinor ℂ (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i))) = xiB ℂ lam sg := by
    unfold xiB
    rw [Finset.filter_true_of_mem fun i _ => i.isLt]
  have hh : (∏ s ∈ Finset.univ.filter (fun s : Fin n => s.val < n),
      (lpMinor ℂ (r := n + 1) (n := n) (s.val + 1) (by omega) (by omega)) ^ (lam s - nuNext lam s)) =
      hw ℂ (Nat.le_succ n) lam := by
    unfold hw
    rw [Finset.filter_true_of_mem fun i _ => i.isLt]
  have hW : weylProd (lamZ lam) = xnW (n + 1) (xnLam lam) := by
    rw [← xnW_weylProd]
    congr 1
    funext a
    simp only [lamZ, xnLam]
    split_ifs <;> simp
  have H2 := H.le
  rw [hμ, hx, hh] at H2
  unfold xnN at H2
  rw [hW]
  exact H2
end Formalism.BranchingDeterminantCap
