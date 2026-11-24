-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.subst_g_series_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:24.50748+00:00
-- url     : https://prove2.me/submissions/63620135-90d2-45bc-aff5-cfab4c47d735

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_subst_leadT
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Aser_eq
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_Aser__eq_f9daf344d726


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low WtGe MonoWtGe dot dot_const substitution_weight_bound)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {K τ : Type} [Field K] (p : ℕ) (c c' : K) {a : Fin 2 → MvPowerSeries τ K}
    (hs : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (Gser p c c') = MvPowerSeries.subst a (G1 p c c') +
      MvPowerSeries.C ((p : K)⁻¹) * (MvPowerSeries.C c * (a 0 * a 1 ^ p) -
        MvPowerSeries.C c' * (a 1 * a 0 ^ p)) := by
  have e : Gser p c c' = G1 p c c' +
      (MvPowerSeries.C c * leadT K p 0 1 - MvPowerSeries.C c' * leadT K p 1 0) := by
    rw [Gser, G1, Aser_eq, Aser'_eq]
    ring
  have hC : ∀ r : K, MvPowerSeries.substAlgHom hs (MvPowerSeries.C r) = MvPowerSeries.C r :=
    fun r => (MvPowerSeries.substAlgHom hs).commutes r
  have h1 := subst_leadT p 0 1 hs
  have h2 := subst_leadT p 1 0 hs
  rw [← MvPowerSeries.coe_substAlgHom hs] at h1 h2 ⊢
  rw [e, map_add, map_sub, map_mul, map_mul, hC, hC, h1, h2]
  ring
end Formalism.InvariantFactorPaths.G7
