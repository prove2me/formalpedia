-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.eq_zero_of_localRegularity_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:43:02.465001+00:00
-- url     : https://prove2.me/submissions/f6aaadaf-4b40-4cc7-85bd-acef74aed18d

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_toLp_mul_cutoff_le_readable

noncomputable section
open MeasureTheory Filter Topology Metric Set InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
section Cutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
private theorem FunctionalInequalities.KLS.LogConcave.cutoff_nonneg (r : ℝ) (y : V) : 0 ≤ FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y :=
  (FunctionalInequalities.KLS.LogConcave.profile (V := V)).nonneg
private theorem FunctionalInequalities.KLS.LogConcave.cutoff_le_one (r : ℝ) (y : V) : FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y ≤ 1 :=
  (FunctionalInequalities.KLS.LogConcave.profile (V := V)).le_one
private theorem FunctionalInequalities.KLS.LogConcave.cutoff_eq_one {r : ℝ} (hr : 0 < r) {y : V} (hy : ‖y‖ ≤ 5 * r) :
    FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y = 1 := by
  apply (FunctionalInequalities.KLS.LogConcave.profile (V := V)).one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr),
    ← div_eq_inv_mul, div_le_iff₀ hr]
  exact hy
/-- A single bound for the gradients of the whole scaled family. -/
private theorem FunctionalInequalities.KLS.LogConcave.exists_norm_gradient_cutoff_le :
    ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r → ∀ y : V, ‖gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y‖ ≤ M / r := by
  have hb : ContDiff ℝ 1 ((FunctionalInequalities.KLS.LogConcave.profile (V := V)) : V → ℝ) := (FunctionalInequalities.KLS.LogConcave.profile (V := V)).contDiff
  obtain ⟨M, hM⟩ := ((FunctionalInequalities.KLS.LogConcave.profile (V := V)).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv one_ne_zero)
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun r hr y => ?_⟩
  have hlin : HasFDerivAt (fun y : V => r⁻¹ • y) (r⁻¹ • ContinuousLinearMap.id ℝ V) y :=
    (hasFDerivAt_id y).const_smul _
  have hd := (hb.differentiable one_ne_zero _).hasFDerivAt.comp y hlin
  have hnorm : ‖gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y‖ = ‖fderiv ℝ (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y‖ := by
    rw [gradient, (toDual ℝ V).symm.norm_map]
  rw [hnorm]
  have hfd : fderiv ℝ (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y
      = fderiv ℝ (((FunctionalInequalities.KLS.LogConcave.profile (V := V)) : V → ℝ) ∘ fun y : V => r⁻¹ • y) y := rfl
  rw [hfd, hd.fderiv]
  have hop : ‖r⁻¹ • ContinuousLinearMap.id ℝ V‖ ≤ r⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.2 hr.le)).trans_eq
      (mul_one _)
  calc
    _ ≤ ‖fderiv ℝ ((FunctionalInequalities.KLS.LogConcave.profile (V := V)) : V → ℝ) (r⁻¹ • y)‖ *
        ‖r⁻¹ • ContinuousLinearMap.id ℝ V‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ max M 1 * r⁻¹ := mul_le_mul ((hM _).trans (le_max_left _ _)) hop
      (norm_nonneg _) (le_trans zero_le_one (le_max_right _ _))
    _ = max M 1 / r := (div_eq_mul_inv _ _).symm
end Cutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Criterion
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
/-- **A deficiency element of the minimal generator that is locally in the form domain
vanishes.**

Let `u ∈ L²(ν)` be orthogonal to `(A + 1) C_c^∞(V)`, that is, `⟪A [f], u⟫ + ⟪[f], u⟫ = 0` for
every smooth compactly supported `f`. If every localization `[χ u]`, `χ ∈ C_c^∞(V)`, lies in the
form domain `D(T̄)`, then `u = 0`.

Only *local* membership is assumed: no global gradient of `u`, no smoothness of `u` and no
classical representative are used. The passage from local to global is the cutoff estimate
`‖χ_r u‖ ≤ (M / r) ‖u‖`, which is where completeness of the ambient Euclidean space enters. The
potential is only `C¹` and no convexity is used. -/
theorem solution
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : (Lp ℝ 2 (ν : Measure V)))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
        ⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2 (ν : Measure V))), u⟫ = 0)
    (hloc : ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
      (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    u = 0 := by
  classical
  obtain ⟨M, hM0, hM⟩ := FunctionalInequalities.KLS.LogConcave.exists_norm_gradient_cutoff_le (V := V)
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hbound : ∀ n : ℕ, ‖(FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
      (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖
      ≤ M / ((n : ℝ) + 1) * ‖u‖ := fun n =>
    FunctionalInequalities.KLS.LogConcave.norm_toLp_mul_cutoff_le_readable m hν hi hνU hU u horth hloc (hpos n) hM0.le (hM _ (hpos n))
  -- the localizations converge to `u` in `L²`, by dominated convergence
  have hsq : ∀ n : ℕ, ‖u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
      (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖ ^ 2
      = ∫ y, ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2 ∂(ν : Measure V) := by
    intro n
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub u ((FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _),
      (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).coeFn_toLp] with
      y e1 e2
    rw [Real.inner_apply, e1, Pi.sub_apply, e2]
    ring
  have hdom : Tendsto
    (fun n : ℕ => ∫ y, ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2 ∂(ν : Measure V))
      atTop (𝓝 0) := by
    have hint : Integrable (fun y => (u y) ^ 2) (ν : Measure V) := (Lp.memLp u).integrable_sq
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun y => ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2) (ν : Measure V) := by
      intro n
      exact ((((continuous_const.sub
        (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)).continuous)).aestronglyMeasurable).mul
          (Lp.aestronglyMeasurable u)).pow 2
    have hbd : ∀ n : ℕ, ∀ᵐ y ∂(ν : Measure V),
        ‖((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2‖ ≤ (u y) ^ 2 := by
      intro n
      refine Filter.Eventually.of_forall fun y => ?_
      have h1 : |1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y| ≤ 1 :=
        abs_le.mpr ⟨by linarith [FunctionalInequalities.KLS.LogConcave.cutoff_le_one ((n : ℝ) + 1) y], by
          linarith [FunctionalInequalities.KLS.LogConcave.cutoff_nonneg ((n : ℝ) + 1) y]⟩
      have h2 : ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2 ≤ (u y) ^ 2 := by
        have := mul_le_mul_of_nonneg_right h1 (abs_nonneg (u y))
        calc ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2
            = (|1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y| * |u y|) ^ 2 := by
              rw [← abs_mul, sq_abs]
          _ ≤ (1 * |u y|) ^ 2 := by
              apply pow_le_pow_left₀ (by positivity) this
          _ = (u y) ^ 2 := by rw [one_mul, sq_abs]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h2
    have hlim : ∀ᵐ y ∂(ν : Measure V), Tendsto
        (fun n : ℕ => ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2) atTop (𝓝 0) := by
      refine Filter.Eventually.of_forall fun y => ?_
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      refine (Filter.eventually_atTop.2 ⟨⌈‖y‖⌉₊, fun n hn => ?_⟩)
      have hy : ‖y‖ ≤ 5 * ((n : ℝ) + 1) := by
        have h1 : ‖y‖ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
        linarith
      simp [FunctionalInequalities.KLS.LogConcave.cutoff_eq_one (hpos n) hy]
    have := tendsto_integral_of_dominated_convergence (μ := (ν : Measure V))
      (F := fun (n : ℕ) y => ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2)
      (f := fun _ : V => (0 : ℝ)) (fun y => (u y) ^ 2) hmeas hint hbd hlim
    simpa using this
  have hten : Tendsto (fun n : ℕ => ‖u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
      (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ‖u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [hsq] using hdom
    have h2 := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h2
    exact h2
  -- the two bounds force `‖u‖ = 0`
  have hzero : ‖u‖ ≤ 0 := by
    have hsum : Tendsto (fun n : ℕ => ‖u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖
        + M / ((n : ℝ) + 1) * ‖u‖) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n : ℕ => M / ((n : ℝ) + 1) * ‖u‖) atTop (𝓝 0) := by
        have := (tendsto_const_div_atTop_nhds_zero_nat M).mul_const ‖u‖
        simpa using (tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).mul_const ‖u‖
      simpa using hten.add h3
    refine ge_of_tendsto hsum (Filter.Eventually.of_forall fun n => ?_)
    calc ‖u‖ = ‖(u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _)
          + (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖
          + ‖(FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖ :=
            norm_add_le _ _
      _ ≤ _ := by linarith [hbound n]
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg u))
