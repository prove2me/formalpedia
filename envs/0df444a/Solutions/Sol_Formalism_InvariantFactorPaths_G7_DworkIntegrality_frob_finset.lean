-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.frob_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:45:14.316882+00:00
-- url     : https://prove2.me/submissions/7fd047c1-b631-419c-b487-3c844bdd37dd

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_monomial
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero


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
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
open Formalism.InvariantFactorPaths.G7.DworkIntegrality
variable {K ι : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {σ : K →+* K}
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) (c : (ι →₀ ℕ) → K) (hc : ∀ m, ‖c m‖ ≤ 1)
    (s : Finset (ι →₀ ℕ)) :
    Bd 1 (∑ m ∈ s, MvPowerSeries.monomial m (c m)) ∧
    Bd (p : ℝ)⁻¹ ((∑ m ∈ s, MvPowerSeries.monomial m (c m)) ^ p -
      PhiH hp.ne_zero σ (∑ m ∈ s, MvPowerSeries.monomial m (c m))) := by
  classical
  have hmon : ∀ a, Bd 1 (MvPowerSeries.monomial a (c a) : MvPowerSeries ι K) := by
    intro a n
    rw [MvPowerSeries.coeff_monomial]
    split_ifs
    · exact hc a
    · simp
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun n => by simp, fun n => ?_⟩
    simp [zero_pow hp.ne_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ⟨bd_add (hmon a) ih.1,
      frob_add hp hnp (hmon a) ih.1 (frob_monomial hp.ne_zero hσ a (hc a)) ih.2⟩
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
