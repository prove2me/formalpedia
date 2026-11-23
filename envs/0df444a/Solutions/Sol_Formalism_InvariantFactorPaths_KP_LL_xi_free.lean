-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.xi_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:56.36742+00:00
-- url     : https://prove2.me/submissions/18fe0ace-db80-41f8-a1af-fd1f05d3d8e1

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Theorems.Thm_Formalism_GM_ProjS_pderiv_of_free
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_xi_supp


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
theorem _root_.solution {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {v : BVar N r D.T.t} (hv : ∀ c, v ≠ xiVar N r D.T.t c) : pderiv v g = 0 :=
  ProjS.pderiv_of_free v g (fun m hm => (xi_supp hg hm).1 v hv)
end Formalism.InvariantFactorPaths.KP.LL
