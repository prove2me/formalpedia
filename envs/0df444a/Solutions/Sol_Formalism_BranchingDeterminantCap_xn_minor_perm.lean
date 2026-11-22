-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_minor_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:11.83453+00:00
-- url     : https://prove2.me/submissions/cc9ed1fc-56c1-42eb-9bc7-fc6715deb342

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
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (ι : κ → Fin r) {p : ℕ} (hp : p ≤ n) (a : Fin p → κ) (π : Equiv.Perm (Fin p)) :
    initMinor ℂ (ι ∘ (a ∘ π)) hp = C (xnSg π) * initMinor ℂ (ι ∘ a) hp := by
  unfold initMinor xnSg
  first
  | (rw [map_intCast, ← Matrix.det_permute]; rfl)
  | (rw [map_intCast]
     exact Matrix.det_permute π (Matrix.of fun x y : Fin p =>
       (X ((ι ∘ a) x, Fin.castLE hp y) : MvPolynomial (Fin r × Fin n) ℂ)))
end Formalism.BranchingDeterminantCap
