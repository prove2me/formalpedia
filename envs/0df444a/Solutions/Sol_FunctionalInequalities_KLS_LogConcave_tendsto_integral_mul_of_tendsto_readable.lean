-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_of_tendsto_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:38:19.447049+00:00
-- url     : https://prove2.me/submissions/21bed376-8ffa-4fb7-8042-c6d0faeb2bd2

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_eq_integral_mul_exp_readable

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
/-- `L²(ν)` convergence gives convergence of Haar integrals against a continuous compactly
supported weight. -/
theorem solution (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) {g : ℕ → V → ℝ} (hg : ∀ n, MemLp (g n) 2 (ν : Measure V))
    {f : Lp ℝ 2 (ν : Measure V)} (hlim : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 f))
    {ψ : V → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ x, g n x * ψ x ∂m) atTop (𝓝 (∫ x, f x * ψ x ∂m)) := by
  let Z : ℝ := ∫ y, Real.exp (-U y) ∂m
  let Ψ : V → ℝ := fun x => (Z * Real.exp (U x)) * ψ x

  have hInt : Integrable (fun x => Real.exp (-U x)) m :=
    FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable hνU

  have hΨcont : Continuous Ψ := by
    dsimp [Ψ]
    exact (continuous_const.mul (Real.continuous_exp.comp hU)).mul hψ

  have hsupport : Function.support Ψ ⊆ Function.support ψ := by
    intro x hx
    by_contra h
    have hψx : ψ x = 0 := by
      simpa [Function.mem_support] using h
    have hΨx : Ψ x = 0 := by
      simp [Ψ, hψx]
    exact hx hΨx

  have hΨc : HasCompactSupport Ψ := by
    exact hψc.mono hsupport

  have hΨ : MemLp Ψ 2 (ν : Measure V) :=
    hΨcont.memLp_of_hasCompactSupport hΨc

  have hpair :
      ∀ a : Lp ℝ 2 (ν : Measure V),
        (∫ x, (a : V → ℝ) x * Ψ x ∂(ν : Measure V)) =
          ⟪a, hΨ.toLp Ψ⟫ := by
    intro a
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hΨ] with x hx
    rw [hx]
    exact mul_comm _ _

  have hseq :
      ∀ n, (∫ x, g n x * ψ x ∂m) =
        ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫ := by
    intro n
    calc
      ∫ x, g n x * ψ x ∂m =
          ∫ x, (Z * Real.exp (U x)) * (g n x * ψ x) ∂(ν : Measure V) := by
            simpa [Z] using
              (FunctionalInequalities.KLS.LogConcave.integral_eq_integral_mul_exp_readable m hνU (fun x => g n x * ψ x))
      _ = ∫ x, ((hg n).toLp (g n) : V → ℝ) x * Ψ x ∂(ν : Measure V) := by
            apply integral_congr_ae
            filter_upwards [MemLp.coeFn_toLp (hg n)] with x hx
            dsimp [Ψ]
            rw [hx]
            ring
      _ = ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫ := hpair ((hg n).toLp (g n))

  have htarget :
      (∫ x, f x * ψ x ∂m) = ⟪f, hΨ.toLp Ψ⟫ := by
    calc
      ∫ x, f x * ψ x ∂m =
          ∫ x, (Z * Real.exp (U x)) * ((f : V → ℝ) x * ψ x) ∂(ν : Measure V) := by
            simpa [Z] using
              (FunctionalInequalities.KLS.LogConcave.integral_eq_integral_mul_exp_readable m hνU
                (fun x => (f : V → ℝ) x * ψ x))
      _ = ∫ x, (f : V → ℝ) x * Ψ x ∂(ν : Measure V) := by
            apply integral_congr_ae
            filter_upwards [] with x
            dsimp [Ψ]
            ring
      _ = ⟪f, hΨ.toLp Ψ⟫ := hpair f

  have hinner :
      Tendsto
        (fun n => ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫)
        atTop (𝓝 ⟪f, hΨ.toLp Ψ⟫) :=
    hlim.inner tendsto_const_nhds

  rw [show (fun n => ∫ x, g n x * ψ x ∂m) =
      (fun n => ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫) from funext hseq]
  rw [show (∫ x, f x * ψ x ∂m) = ⟪f, hΨ.toLp Ψ⟫ from htarget]
  exact hinner
