-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.integral_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:29.598055+00:00
-- url     : https://prove2.me/submissions/5024e5b7-aec9-414d-9b15-be022d31c2ff

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExpSeriesBivariate Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
open Finset Formalism.G Formalism.HermitianLattices.ExpSeriesBivariate
variable {σ K : Type} [NormedField K]
namespace Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
theorem _root_.solution [IsUltrametricDist K] {u v : MvPowerSeries σ K} (huv : u * v = 1)
    (hu0 : MvPowerSeries.constantCoeff u = 1) (hu : IntegralMv u) : IntegralMv v := by
  classical
  have key : ∀ n, ∀ d : σ →₀ ℕ, d.degree = n → ‖MvPowerSeries.coeff d v‖ ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro d hd
      have hmul := congrArg (MvPowerSeries.coeff d) huv
      rw [MvPowerSeries.coeff_mul] at hmul
      have hmem : ((0 : σ →₀ ℕ), d) ∈ Finset.HasAntidiagonal.antidiagonal d :=
        Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add d)
      rw [← Finset.add_sum_erase _ _ hmem] at hmul
      have hc : MvPowerSeries.coeff (0 : σ →₀ ℕ) u = 1 := by
        first
        | rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hu0
        | simpa using hu0
      simp only [hc, one_mul] at hmul
      rw [eq_sub_of_add_eq hmul]
      have hsub : ∀ a b : K, ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
        intro a b
        first
        | (rw [sub_eq_add_neg]
           have h1 := IsUltrametricDist.norm_add_le_max a (-b)
           rwa [norm_neg] at h1)
        | (have h1 := IsUltrametricDist.dist_triangle_max a 0 b
           simpa [dist_eq_norm] using h1)
      refine (hsub _ _).trans (max_le ?_ ?_)
      · rw [MvPowerSeries.coeff_one]
        split_ifs <;> simp
      · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
        intro p hp
        rw [Finset.mem_erase] at hp
        have hp2 : p.1 + p.2 = d := by
          first
          | exact _root_.Finset.mem_antidiagonal.1 hp.2
          | exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp.2
        have hp1 : p.1 ≠ 0 := by
          intro h0
          apply hp.1
          rw [h0, zero_add] at hp2
          exact Prod.ext h0 hp2
        have hdeg : p.1.degree + p.2.degree = d.degree := by
          rw [← hp2]
          first
          | exact (map_add Finsupp.degree p.1 p.2).symm
          | exact (Finsupp.degree_add p.1 p.2).symm
        have hpos : 0 < p.1.degree := by
          rcases Nat.eq_zero_or_pos p.1.degree with h | h
          · exfalso
            apply hp1
            first
            | exact (Finsupp.degree_eq_zero_iff p.1).mp h
            | exact Finsupp.degree_eq_zero_iff.mp h
          · exact h
        rw [norm_mul]
        exact (mul_le_mul (hu p.1) (ih p.2.degree (by omega) p.2 rfl) (norm_nonneg _)
          zero_le_one).trans (by norm_num)
  intro d
  exact key _ d rfl
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
