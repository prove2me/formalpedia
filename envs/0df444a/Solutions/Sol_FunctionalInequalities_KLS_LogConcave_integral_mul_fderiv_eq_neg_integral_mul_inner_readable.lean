-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:05.948716+00:00
-- url     : https://prove2.me/submissions/a2a1c913-253c-4a17-a587-8e59c0ebaa3a

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_graph_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_tendsto_integral_mul_inner_of_tendsto_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_tendsto_integral_mul_of_tendsto_readable

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
omit [SecondCountableTopology V] in
/-- Smooth integration by parts against a test: `∫ g ∂_w φ dm = -∫ φ ⟪∇g, w⟫ dm` for smooth `g`
and smooth compactly supported `φ`. -/
theorem FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner_gradient {g φ : V → ℝ}
    (hg : ContDiff ℝ ∞ g) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
    ∫ x, g x * fderiv ℝ φ x w ∂m = -∫ x, φ x * ⟪gradient g x, w⟫ ∂m := by
  have hIBP :=
    Energy.Euclidean.integral_mul_fderiv_apply m hφ hφc hg w
  have hgrad :
      (∫ x, φ x * ⟪gradient g x, w⟫ ∂m) =
        ∫ x, φ x * fderiv ℝ g x w ∂m := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Energy.Euclidean.inner_gradient_eq_fderiv_apply]
  linarith
/-- **Weak gradient of an element of the closed domain**: for `h ∈ D(T̄)`, smooth compactly
supported `φ` and every direction `w`, `∫ h ∂_w φ dm = -∫ φ ⟪T̄ h, w⟫ dm`. -/
theorem solution (hν : FunctionalInequalities.KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
    ∫ x, (h : Lp ℝ 2 (ν : Measure V)) x * fderiv ℝ φ x w ∂m =
      -∫ x, φ x * ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
        Lp V 2 (ν : Measure V)) x, w⟫ ∂m := by
  obtain ⟨g, hg, hgc, h1, h2⟩ :=
    hν.exists_seq_smooth_tendsto_graph_readable m
      (ContinuousLinearMap.id ℝ V) hi h

  have hψ : Continuous (fun x => fderiv ℝ φ x w) := by
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

  have hψc : HasCompactSupport (fun x => fderiv ℝ φ x w) := by
    exact hφc.fderiv_apply ℝ w

  have hL :
      Tendsto
        (fun n => ∫ x, g n x * fderiv ℝ φ x w ∂m)
        atTop
        (𝓝 (∫ x, (h : Lp ℝ 2 (ν : Measure V)) x *
          fderiv ℝ φ x w ∂m)) :=
    FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_of_tendsto_readable m hνU hU
      (fun n => FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n))
      h1 hψ hψc

  let G : ℕ → V → V :=
    fun n => FunctionalInequalities.Energy.WeightedGradient.apply (ContinuousLinearMap.id ℝ V) (g n)

  have hG : ∀ n, MemLp (G n) 2 (ν : Measure V) := by
    intro n
    dsimp [G]
    exact
      (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν
        (ContinuousLinearMap.id ℝ V) (hg n) (hgc n)).memLp_apply

  have h2' :
      Tendsto
        (fun n => (hG n).toLp (G n))
        atTop
        (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h)) := by
    simpa [G] using h2

  have hR :
      Tendsto
        (fun n => ∫ x, φ x * ⟪G n x, w⟫ ∂m)
        atTop
        (𝓝 (∫ x, φ x *
          ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
            Lp V 2 (ν : Measure V)) x, w⟫ ∂m)) :=
    FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_inner_of_tendsto_readable m hνU hU hG h2'
      hφ.continuous hφc w

  have hneg :
      Tendsto
        (fun n => -(∫ x, φ x * ⟪G n x, w⟫ ∂m))
        atTop
        (𝓝 (-∫ x, φ x *
          ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
            Lp V 2 (ν : Measure V)) x, w⟫ ∂m)) :=
    hR.neg

  have heq :
      ∀ n, -(∫ x, φ x * ⟪G n x, w⟫ ∂m) =
        ∫ x, g n x * fderiv ℝ φ x w ∂m := by
    intro n
    simpa [G, FunctionalInequalities.Energy.WeightedGradient.apply_id] using
      (FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner_gradient
        m (hg n) hφ hφc w).symm

  have hL' :
      Tendsto
        (fun n => ∫ x, g n x * fderiv ℝ φ x w ∂m)
        atTop
        (𝓝 (-∫ x, φ x *
          ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
            Lp V 2 (ν : Measure V)) x, w⟫ ∂m)) := by
    exact hneg.congr heq

  exact tendsto_nhds_unique hL hL'
