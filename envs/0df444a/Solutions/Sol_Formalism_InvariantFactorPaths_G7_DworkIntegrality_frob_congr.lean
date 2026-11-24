-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.frob_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:52:43.077741+00:00
-- url     : https://prove2.me/submissions/e56a590d-0400-498a-b9ab-7f42466ff0ff

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_low_sub_truncD
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_low_PhiH
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_finset
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
theorem _root_.solution [Finite ι] (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) {f : MvPowerSeries ι K} (hf : Bd 1 f) :
    Bd (p : ℝ)⁻¹ (f ^ p - PhiH hp.ne_zero σ f) := by
  intro n
  have hg : Bd (p : ℝ)⁻¹ ((truncD (n.degree + 1) f) ^ p -
      PhiH hp.ne_zero σ (truncD (n.degree + 1) f)) :=
    (frob_finset hp hnp hσ (fun m => MvPowerSeries.coeff m f) hf _).2
  have hl := low_sub_truncD (n.degree + 1) f
  have h1 : Low (n.degree + 1) (f ^ p - (truncD (n.degree + 1) f) ^ p) := by
    obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow f (truncD (n.degree + 1) f) p
    rw [hr]
    simpa using low_mul hl (low_zero r)
  have h2 : Low (n.degree + 1) (PhiH hp.ne_zero σ (f - truncD (n.degree + 1) f)) :=
    low_mono (Nat.le_mul_of_pos_left _ hp.pos) (low_PhiH hp.ne_zero σ hl)
  have e : f ^ p - PhiH hp.ne_zero σ f =
      ((truncD (n.degree + 1) f) ^ p - PhiH hp.ne_zero σ (truncD (n.degree + 1) f)) +
        (f ^ p - (truncD (n.degree + 1) f) ^ p) -
        PhiH hp.ne_zero σ (f - truncD (n.degree + 1) f) := by
    rw [map_sub]; ring
  rw [e, map_sub, map_add, h1 n (by omega), h2 n (by omega), add_zero, sub_zero]
  exact hg n
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
