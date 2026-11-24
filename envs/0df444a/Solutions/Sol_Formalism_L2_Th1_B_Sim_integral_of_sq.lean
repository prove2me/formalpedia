-- Prove2me | solution 1 for Formalism.L2.Th1.B.Sim.integral_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:16.983195+00:00
-- url     : https://prove2.me/submissions/0d5d5254-72d3-4f87-b38c-ec272dd676f3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_SimeqPadicIntegers
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_add
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_neg
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_nsmul
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_zero
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_integral_of_mul_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Sim
open Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.HermitianLattices.ExpSeriesBivariate (InLam)
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_zero inLam_add inLam_neg inLam_nsmul integral_of_mul_eq_one)
variable {K ι : Type} [NormedField K] [CharZero K]
namespace Formalism.L2.Th1.B.Sim
theorem _root_.solution [IsUltrametricDist K] {y : MvPowerSeries ι K} (h2 : ‖(2 : K)‖ = 1)
    (hy0 : MvPowerSeries.constantCoeff y = 1) (hy : Integral (y * y)) : Integral y := by
  classical
  have main : ∀ (m : ℕ) (d : ι →₀ ℕ), d.degree = m → ‖MvPowerSeries.coeff d y‖ ≤ 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro d hd
      by_cases hd0 : d = 0
      · subst hd0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0, norm_one]
      have hmem : ((d, 0) : (ι →₀ ℕ) × (ι →₀ ℕ)) ∈ (antidiagonal d).erase ((0 : ι →₀ ℕ), d) := by
        refine Finset.mem_erase.mpr ⟨fun h => hd0 (congrArg Prod.fst h), by simp⟩
      have h1 : MvPowerSeries.coeff d (y * y) = _ := MvPowerSeries.coeff_mul d y y
      rw [← Finset.add_sum_erase _ _ (show ((0 : ι →₀ ℕ), d) ∈ antidiagonal d by simp),
        ← Finset.add_sum_erase _ _ hmem] at h1
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0, one_mul, mul_one] at h1
      have h3 : 2 * MvPowerSeries.coeff d y = MvPowerSeries.coeff d (y * y) +
          - ∑ p ∈ ((antidiagonal d).erase ((0 : ι →₀ ℕ), d)).erase (d, 0),
            MvPowerSeries.coeff p.1 y * MvPowerSeries.coeff p.2 y := by
        rw [h1]; ring
      have h4 : ‖MvPowerSeries.coeff d y‖ = ‖2 * MvPowerSeries.coeff d y‖ := by
        rw [norm_mul, h2, one_mul]
      rw [h4, h3]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy d) ?_)
      rw [norm_neg]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p hp => ?_
      rw [norm_mul]
      have hpa := Finset.mem_erase.mp hp
      have hpb := Finset.mem_erase.mp hpa.2
      have hp1 : p.1 + p.2 = d := by simpa using hpb.2
      have hdeg : p.1.degree + p.2.degree = d.degree := by rw [← map_add, hp1]
      have hne1 : p.1 ≠ 0 := by
        intro h0
        apply hpb.1
        ext1
        · exact h0
        · simpa [h0] using hp1
      have hne2 : p.2 ≠ 0 := by
        intro h0
        apply hpa.1
        ext1
        · simpa [h0] using hp1
        · exact h0
      have hpos1 : p.1.degree ≠ 0 := fun h => hne1 ((Finsupp.degree_eq_zero_iff _).mp h)
      have hpos2 : p.2.degree ≠ 0 := fun h => hne2 ((Finsupp.degree_eq_zero_iff _).mp h)
      exact mul_le_one₀ (ih p.1.degree (by omega) p.1 rfl) (norm_nonneg _)
        (ih p.2.degree (by omega) p.2 rfl)
  exact fun d => main _ d rfl
end Formalism.L2.Th1.B.Sim
