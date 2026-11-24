-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.sp_midGen_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:41.553705+00:00
-- url     : https://prove2.me/submissions/713830b9-8b69-419f-8ae8-1dfc396bc46d

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepPlus

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D 0 j jp x = (∏ i, D.Ehat p (r := r) i ^ j i) *
      (ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) ^ jp *
        (X (zP D r) ^ D.zPlus * PL p D (List.finRange D.T.t) j jp x)) := by
  have h1 : D.Eplus p (r := r) = ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) := rfl
  unfold midGen
  rw [h1]
  simp only [Nat.not_lt_zero, Finset.filter_false, Finset.prod_empty, List.drop_zero, mul_one]
  ring
end Formalism.InvariantFactorPaths.KP.LL
