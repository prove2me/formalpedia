-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.zSub_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:36.734719+00:00
-- url     : https://prove2.me/submissions/bec82156-de67-4ccd-9394-ac7245f164a3

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
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.StarEntryOperators
theorem _root_.solution [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K)
    (x : ZV ν r0 r1) :
    zSub TT ξ x = ∑ i, MvPowerSeries.C (Amat TT ξ i x) * MvPowerSeries.X i := by
  rw [Fintype.sum_sum_type, Finset.sum_eq_single (x.1, x.2.2), Finset.sum_eq_single x]
  · simp only [Amat, if_true, map_one, one_mul, zSub]
    rw [add_comm]
    split_ifs <;> simp
  · intro y _ hy
    simp [Amat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro y _ hy
    simp [Amat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
