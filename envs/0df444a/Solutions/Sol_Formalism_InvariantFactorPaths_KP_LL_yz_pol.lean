-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.yz_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:57.671641+00:00
-- url     : https://prove2.me/submissions/1b2080a7-5534-4fbe-93b3-a9de4d174309

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_BiHomPlus

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
theorem _root_.solution {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ Pol p r LL :=
  (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).1).1
end Formalism.InvariantFactorPaths.KP.LL
