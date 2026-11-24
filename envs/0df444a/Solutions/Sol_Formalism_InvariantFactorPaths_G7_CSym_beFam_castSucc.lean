-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.beFam_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:48.495713+00:00
-- url     : https://prove2.me/submissions/7d4f0c0b-b4a2-47b9-ac0e-56e0f5b9ca37

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.CSym
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CSym
theorem _root_.solution (Q : K) (hQ : Q ≠ 0) (g : ℕ) (i : Fin g) :
    beFam Q (g + 1) i.castSucc = Q * beFam Q g i := by
  unfold beFam
  rw [show ((g + 1 : ℕ) : ℤ) - 1 - 2 * ((i.castSucc : Fin (g + 1)).val : ℤ) =
      ((g : ℤ) - 1 - 2 * (i.val : ℤ)) + 1 by simp; ring, zpow_add_one₀ hQ, mul_comm]
end Formalism.InvariantFactorPaths.G7.CSym
