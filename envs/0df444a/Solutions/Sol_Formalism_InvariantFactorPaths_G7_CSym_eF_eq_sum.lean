-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.eF_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:22.300234+00:00
-- url     : https://prove2.me/submissions/41d535e3-99e2-4431-805a-555dea249d26

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
variable {K σ : Type} [CommRing K] [Fintype σ]
namespace Formalism.InvariantFactorPaths.G7.CSym
theorem _root_.solution (x : σ → K) (l : ℕ) :
    eF x l = ∑ s ∈ powersetCard l univ, ∏ i ∈ s, x i := by
  unfold eF
  simp [MvPolynomial.esymm, map_sum, map_prod]
end Formalism.InvariantFactorPaths.G7.CSym
