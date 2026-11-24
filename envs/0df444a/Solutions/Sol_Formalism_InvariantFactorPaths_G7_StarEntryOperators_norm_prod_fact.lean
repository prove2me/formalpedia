-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.norm_prod_fact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:38.822024+00:00
-- url     : https://prove2.me/submissions/8ef7b859-73c5-4e02-8b88-39cff0026c64

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_norm_nat

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
    (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {α : Type} (s : Finset α) (f : α → ℕ) :
    ‖((∏ x ∈ s, (f x).factorial : ℕ) : K)‖ =
      (p : ℝ) ^ (-(∑ x ∈ s, (padicValNat p (f x).factorial : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Nat.cast_prod, norm_prod, ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hp0]
  exact Finset.prod_congr rfl fun x _ => norm_nat hp hnp (Nat.factorial_ne_zero _)
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
