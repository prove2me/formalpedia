-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_g0F_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:20.82268+00:00
-- url     : https://prove2.me/submissions/28752036-8e64-41ae-b68c-f74f3331f3d5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ppowq_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lt_ppowq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_sum_range_ite_unique

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
theorem _root_.solution (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    PowerSeries.coeff (p * (p ^ 2) ^ j) (g0F K p) = ((p : K) ^ (j + 1))⁻¹ := by
  unfold g0F
  rw [PowerSeries.coeff_mk]
  exact sum_range_ite_unique _ (fun i => p * (p ^ 2) ^ j = p * (p ^ 2) ^ i)
    (fun i => ((p : K) ^ (i + 1))⁻¹) j (lt_ppowq hp j) rfl (fun i h => ppowq_inj hp h.symm)
end Formalism.InvariantFactorPaths.G7
