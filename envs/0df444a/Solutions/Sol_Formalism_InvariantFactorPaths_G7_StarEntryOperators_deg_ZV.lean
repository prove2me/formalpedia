-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.deg_ZV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:11.188845+00:00
-- url     : https://prove2.me/submissions/005ed04d-4101-489f-bd9a-1dbeccbc0e5b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd

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
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)
open Formalism.InvariantFactorPaths.G7.StarEntryOperators
namespace Formalism.InvariantFactorPaths.G7.StarEntryOperators
theorem _root_.solution {ν r0 r1 : ℕ} [NeZero ν] (n : ZV ν r0 r1 →₀ ℕ) :
    n.degree = ∑ s, ∑ x : Fin r0 × Fin r1, n (s, x) := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
