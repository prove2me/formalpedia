-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.sum_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:59.815351+00:00
-- url     : https://prove2.me/submissions/2977b9f6-df29-4251-be33-10b27b07870e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open Formalism.InvariantFactorPaths.G7.TwoS
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {K ι : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν] (a b : Fin ν → ZMod (2 * ν) → K)
    (par : ZMod (2 * ν) → Prop) [DecidablePred par]
    (h : ∀ s s', ∑ r, a r s * b r s' = if par s' ∧ s = s' + 1 then 1 else 0)
    (P Q : ZMod (2 * ν) → Fin r0 × Fin r1 → MvPowerSeries ι K) :
    ∑ e : EV ν r0 r1, (∑ s, MvPowerSeries.C (a e.1 s) * P s e.2) *
        (∑ s', MvPowerSeries.C (b e.1 s') * Q s' e.2) =
      ∑ s', if par s' then ∑ ab, Q s' ab * P (s' + 1) ab else 0 := by
  classical
  have key : ∀ ab : Fin r0 × Fin r1,
      ∑ r, (∑ s, MvPowerSeries.C (a r s) * P s ab) * (∑ s', MvPowerSeries.C (b r s') * Q s' ab) =
        ∑ s', if par s' then Q s' ab * P (s' + 1) ab else 0 := by
    intro ab
    simp only [Finset.sum_mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    have e : ∀ s, ∑ r, MvPowerSeries.C (a r s) * P s ab * (MvPowerSeries.C (b r s') * Q s' ab) =
        if par s' ∧ s = s' + 1 then Q s' ab * P s ab else 0 := by
      intro s
      have : ∑ r, MvPowerSeries.C (a r s) * P s ab * (MvPowerSeries.C (b r s') * Q s' ab) =
          MvPowerSeries.C (∑ r, a r s * b r s') * (Q s' ab * P s ab) := by
        rw [map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => by rw [map_mul]; ring
      rw [this, h]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun s _ => e s]
    by_cases hp : par s'
    · simp [hp]
    · simp [hp]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_congr rfl fun ab _ => key ab,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.G7.TwoS
