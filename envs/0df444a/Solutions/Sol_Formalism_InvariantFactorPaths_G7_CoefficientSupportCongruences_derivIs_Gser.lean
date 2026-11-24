-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.derivIs_Gser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:31.193806+00:00
-- url     : https://prove2.me/submissions/2a228350-48de-443a-8fd8-207ea051076d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_derivA


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
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
open FrobeniusSubstitution
namespace Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {p : ℕ}
    (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {c c' : K} (hc : ‖c‖ ≤ 1) (hc' : ‖c'‖ ≤ 1) :
    DerivIs p (Gser p c c') c := by
  obtain ⟨h1, h2⟩ := Formalism.InvariantFactorPaths.G7.Top.derivA K p hp hnp
  have e : MvPowerSeries.pderiv (R := K) 0 (Gser p c c') -
      MvPowerSeries.C c * (at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p)) =
      c • (MvPowerSeries.pderiv (R := K) 0 (Aser K p) -
        at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p)) -
      c' • MvPowerSeries.pderiv (R := K) 0 (Aser' K p) := by
    unfold Gser
    rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul,
      map_sub, Derivation.map_smul, Derivation.map_smul, smul_sub]
    abel
  unfold DerivIs
  rw [e]
  intro n
  rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_one₀ hc (norm_nonneg _) (h1 n)
  · rw [norm_neg, norm_mul]
    exact mul_le_one₀ hc' (norm_nonneg _) (h2 n)
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
