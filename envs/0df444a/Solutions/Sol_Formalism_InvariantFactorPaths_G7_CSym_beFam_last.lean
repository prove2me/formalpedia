-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.beFam_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:48.50931+00:00
-- url     : https://prove2.me/submissions/9d265269-593d-467d-a0be-6779b982eff7

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
theorem _root_.solution (Q : K) (g : ℕ) : beFam Q (g + 1) (Fin.last g) = Q ^ (-(g : ℤ)) := by
  unfold beFam
  congr 1
  simp
  ring
end Formalism.InvariantFactorPaths.G7.CSym
