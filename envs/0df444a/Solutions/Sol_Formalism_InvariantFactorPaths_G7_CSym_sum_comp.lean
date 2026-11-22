-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.sum_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:06.608743+00:00
-- url     : https://prove2.me/submissions/207247d1-53d8-4905-82dd-a1c154f58e60

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
namespace Formalism.InvariantFactorPaths.G7.CSym
theorem _root_.solution {K A B C ι : Type} [CommRing K] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C] (s : Finset ι) (f : ι → B →ₗ[K] C) (g : A →ₗ[K] B) :
    (∑ i ∈ s, f i).comp g = ∑ i ∈ s, (f i).comp g := by
  ext a
  simp [LinearMap.sum_apply]
end Formalism.InvariantFactorPaths.G7.CSym
