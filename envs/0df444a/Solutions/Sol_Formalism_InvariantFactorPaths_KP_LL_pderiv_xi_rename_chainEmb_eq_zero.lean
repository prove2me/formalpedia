-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.pderiv_xi_rename_chainEmb_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:04.768+00:00
-- url     : https://prove2.me/submissions/03544af1-2f57-4860-8bfe-608c74b5ce7f

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_xi_notin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]
variable {N r : ℕ} [NeZero r] {D : BlockData N}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (c : Fin r) :
    pderiv (xiVar N r D.T.t c) (rename (chainEmb N r D.T.t) y) = 0 := by
  classical
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (vars_rename _ _ h)
  exact xi_notin (D := D) c ⟨a, ha⟩
end Formalism.InvariantFactorPaths.KP.LL
