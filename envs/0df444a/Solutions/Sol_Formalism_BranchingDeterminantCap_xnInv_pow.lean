-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xnInv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:28.404401+00:00
-- url     : https://prove2.me/submissions/42124611-0377-459a-a43f-8198f094c707

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnInv_congr
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnInv_step

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
variable {r n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h)
    (hk : k ≤ n) (hkr : k ≤ r) (J : Fin k → Fin r) (hJ : Function.Injective J) (e : ℕ) :
    xnInv k (fun q => μ q + if q < k then e else 0) (initMinor ℂ J hk ^ e * x)
      (lpMinor ℂ k hkr hk ^ e * h) := by
  induction e with
  | zero =>
    refine xnInv_congr H ?_ ?_ ?_
    · funext q
      split_ifs <;> simp
    · simp
    · simp
  | succ e ih =>
    have H2 := xnInv_step ih hk hkr J hJ
    refine xnInv_congr H2 ?_ ?_ ?_
    · funext q
      simp only [xnAdd]
      split_ifs <;> omega
    · ring
    · ring
end Formalism.BranchingDeterminantCap
