-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.chainEmb_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:47.148373+00:00
-- url     : https://prove2.me/submissions/af2eb41b-172a-4bdd-aa49-2e2454a4e236

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj

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
open scoped Pointwise
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
variable {p D}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : Function.Injective (chainEmb N r D.T.t) := by
  intro x y h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
  exact Prod.ext h.1 h.2
end Formalism.InvariantFactorPaths.KP.LL
