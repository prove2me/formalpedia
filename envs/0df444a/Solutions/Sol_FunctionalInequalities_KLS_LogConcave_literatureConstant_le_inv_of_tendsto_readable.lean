-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.literatureConstant_le_inv_of_tendsto_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:29:10.471811+00:00
-- url     : https://prove2.me/submissions/673b6623-9499-4d16-8f1e-1e3915c4141e

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_literatureConstant_le_of_gap_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_center_sq_sub_le_readable

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU in
/-- Bakry–Gentil–Ledoux (2014), Corollary 4.8.2, **under an ergodicity hypothesis**: if
`∇∇U ≥ ρ > 0` and `Var(P_t u) → 0` as `t → ∞` for every `u ∈ D(T̄)`, then the literature Poincaré
constant satisfies `C_P(ν) ≤ 1/ρ`. -/
theorem solution {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (herg : ∀ u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      Tendsto (fun t : ℝ => ‖FunctionalInequalities.L2.center ν (FunctionalInequalities.Analysis.Semigroup.Generated.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi)
        (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) t u)‖)
        atTop (𝓝 0)) :
    FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹ := by
  let C : NNReal := ⟨ρ⁻¹, (inv_pos.mpr hρ).le⟩
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

  have hgap :
      ∀ u : T.domain,
        ‖FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
          (C : ℝ) * ‖T u‖ ^ 2 := by
    intro u

    let a : ℝ := ‖FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2
    let b : ℕ → ℝ := fun n =>
      ‖FunctionalInequalities.L2.center ν (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (n : ℝ) u)‖ ^ 2
    let d : ℝ := ‖T u‖ ^ 2

    have hpointwise : ∀ n : ℕ, a ≤ b n + ρ⁻¹ * d := by
      intro n
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hmain :=
        FunctionalInequalities.KLS.LogConcave.norm_center_sq_sub_le_readable m hν hi hνU hU hρ hH u hn
      change
        ‖FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
            ‖FunctionalInequalities.L2.center ν (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (n : ℝ) u)‖ ^ 2 ≤
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ * ‖T u‖ ^ 2 at hmain

      have hnum :
          1 - Real.exp (-2 * ρ * (n : ℝ)) ≤ (1 : ℝ) := by
        linarith [Real.exp_nonneg (-2 * ρ * (n : ℝ))]

      have hcoef :
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ ≤ ρ⁻¹ := by
        calc
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ ≤ 1 / ρ :=
            div_le_div_of_nonneg_right hnum hρ.le
          _ = ρ⁻¹ := by rw [one_div]

      have hmul :
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ * ‖T u‖ ^ 2 ≤
            ρ⁻¹ * ‖T u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

      dsimp [a, b, d]
      linarith

    have hb :
        Tendsto (fun n : ℕ => b n) atTop (𝓝 0) := by
      have hnat :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      have h := (herg u).comp hnat
      have h' :
          Tendsto
            (fun n : ℕ =>
              ‖FunctionalInequalities.L2.center ν (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (n : ℝ) u)‖ ^ 2)
            atTop (𝓝 (0 : ℝ)) := by
        simpa [T, hT, hd] using h.pow 2
      simpa [b] using h'

    have hsum :
        Tendsto (fun n : ℕ => b n + ρ⁻¹ * d)
          atTop (𝓝 (ρ⁻¹ * d)) := by
      simpa using hb.add tendsto_const_nhds

    have ha : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) :=
      tendsto_const_nhds

    have hlim : a ≤ ρ⁻¹ * d :=
      le_of_tendsto_of_tendsto' ha hsum hpointwise

    have hC : (C : ℝ) = ρ⁻¹ := by
      rfl

    dsimp [a, d] at hlim ⊢
    rw [hC]
    exact hlim

  have hconst :
      FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) :=
    FunctionalInequalities.KLS.LogConcave.literatureConstant_le_of_gap_readable m hν hi C hgap

  calc
    FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) := hconst
    _ = ENNReal.ofReal ρ⁻¹ := by
      rw [ENNReal.ofReal_eq_coe_nnreal]
      rfl
