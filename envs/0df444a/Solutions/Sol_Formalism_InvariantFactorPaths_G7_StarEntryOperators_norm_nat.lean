-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.norm_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:46.176504+00:00
-- url     : https://prove2.me/submissions/de5205a7-819f-4be5-b142-36516cd34fa2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_pow_padicValNat


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
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {m : ℕ} (hm : m ≠ 0) :
    ‖(m : K)‖ = (p : ℝ) ^ (-(padicValNat p m : ℝ)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlt : ‖(p : K)‖ < 1 := by
    rw [hnp]; exact inv_lt_one_of_one_lt₀ hp1
  rw [Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp hlt hm, hnp,
    Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
