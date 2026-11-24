-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.cc_hhS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:33.515839+00:00
-- url     : https://prove2.me/submissions/599c8528-344a-471b-9dab-5f0331e034ec

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
theorem _root_.solution [NeZero ν] {p : ℕ} (hp : p ≠ 0) (u : ZMod (2 * ν) → K) :
    MvPowerSeries.constantCoeff (hhS (r0 := r0) (r1 := r1) p u) = 0 := by
  have h : ∀ (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1),
      MvPowerSeries.constantCoeff (sPos (K := K) p s ab) = 0 := by
    intro s ab
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    change (∑ l ∈ range ((0 : ZV ν r0 r1 →₀ ℕ).degree + 1),
      if (0 : ZV ν r0 r1 →₀ ℕ) = Finsupp.single (s - 2 * (l : ZMod (2 * ν)), ab) ((p ^ 2) ^ l)
        then (-1 : K) ^ l else 0) = 0
    refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
    have := Finsupp.single_eq_zero.1 h.symm
    exact (pow_ne_zero l (pow_ne_zero 2 hp)) this
  simp [hhS, map_sum, h]
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
