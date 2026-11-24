-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.int_zSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:38.819316+00:00
-- url     : https://prove2.me/submissions/3dfbe00e-7eb4-4140-8145-9d2603a182ec

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
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}
    (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (hξ : ∀ s a, ‖ξ s a‖ ≤ 1)
    (x : ZV ν r0 r1) : Integral (zSub (r1 := r1) TT ξ x) := by
  intro n
  classical
  unfold zSub
  rw [map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp
  · split_ifs
    · rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, norm_mul]
      refine mul_le_one₀ (hξ _ _) (norm_nonneg _) ?_
      split_ifs <;> simp
    · simp
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
