-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.norm_lift_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:37.256964+00:00
-- url     : https://prove2.me/submissions/cbb59d55-ba02-4a28-a47e-25de2903e1af

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {σ : K →+* K}
    (hU : UnrOK K p σ) {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  obtain ⟨hp, -, -, -, hσ⟩ := hU
  have h1 : ‖a ^ p‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg a) ha
  have h2 : ‖σ a - a ^ p‖ ≤ 1 :=
    (hσ a ha).trans (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_lt.le))
  calc ‖σ a‖ = ‖(σ a - a ^ p) + a ^ p‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ p‖ ‖a ^ p‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le h2 h1
end Formalism.InvariantFactorPaths.G7
