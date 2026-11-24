-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.DeS_Gser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:28:35.776377+00:00
-- url     : https://prove2.me/submissions/30e64519-d1c6-4966-91f5-7e828fa5eadc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_map_Gser
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_frobExprG


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
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) (σ : K →+* K) {c : K}
    (hσσ : σ (σ c) = c) :
    DeS p σ (Gser p c (σ c)) =
      MvPowerSeries.C (σ c) * (at1 0 (g0F K p) * at1 1 (lgF K p)) -
        MvPowerSeries.C c * (at1 0 (lgF K p) * at1 1 (g0F K p)) := by
  unfold DeS
  rw [Formalism.InvariantFactorPaths.G7.CoboundarySeries.map_Gser σ p c (σ c), hσσ, Formalism.InvariantFactorPaths.G7.Top.frobExprG K p c (σ c) hp hpK,
    ← mul_assoc, ← map_mul, inv_mul_cancel₀ hpK, map_one, one_mul]
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
