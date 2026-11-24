-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.sp_gen_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:41.498292+00:00
-- url     : https://prove2.me/submissions/c54e5528-09a6-41b8-9157-0fdf974a4846

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
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp * Pplus p D jp y =
      (∏ i, D.Ehat p (r := r) i ^ j i) *
      (ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) ^ jp *
        tieP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus y) := by
  rw [mul_assoc]
  rfl
end Formalism.InvariantFactorPaths.KP.LL
