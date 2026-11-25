-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.law_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:53.653188+00:00
-- url     : https://prove2.me/submissions/744bef3d-e12f-4d59-867c-2cb556854eaf

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_one_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_cob_eq_zero_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_law_exists
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_law_unique
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_law
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_not_dvd_den
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_norm_ratCast_le_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_funEqType_lgF
import Theorems.Thm_Formalism_FG_frobenius_lift_padic_square
import Theorems.Thm_Formalism_LT_funEqGroup


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
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLaws
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (F : MvPowerSeries (Fin 2) K)
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hF : cob F (lgF K p) = 0) : Integral F := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  obtain ⟨FQ, hFQ0, hFQ⟩ := law_exists (K := ℚ) p hp2
  obtain ⟨G, hG0, hGint, hGlog⟩ := Formalism.LT.funEqGroup ℚ_[p] p (p ^ 2) (RingHom.id ℚ_[p])
    (Formalism.FG.frobenius_lift_padic_square p) (lgF ℚ_[p] p) (constantCoeff_lgF p hp2)
    (coeff_one_lgF p hp2) (funEqType_lgF p)
  have hGcob : cob G (lgF ℚ_[p] p) = 0 := (cob_eq_zero_iff G _).mpr hGlog
  obtain ⟨h0p, hcp⟩ := map_law (Rat.castHom ℚ_[p]) p FQ hFQ0 hFQ
  have hEq := law_unique p hp2 _ G h0p hG0 hcp hGcob
  have hQp : ∀ n, ‖((MvPowerSeries.coeff n FQ : ℚ) : ℚ_[p])‖ ≤ 1 := by
    intro n
    have h1 := hGint n
    rw [← hEq, MvPowerSeries.coeff_map] at h1
    simpa using h1
  obtain ⟨h0K, hcK⟩ := map_law (Rat.castHom K) p FQ hFQ0 hFQ
  have hEqK := law_unique p hp2 _ F h0K hF0 hcK hF
  have hnp' : ‖(p : K)‖ < 1 := by
    rw [hnp]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  intro n
  rw [← hEqK, MvPowerSeries.coeff_map]
  have h2 := norm_ratCast_le_one hp hnp' (MvPowerSeries.coeff n FQ) (not_dvd_den _ (hQp n))
  simpa using h2
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
