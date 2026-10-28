-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.fderiv_logLaplace_jointLaw_none_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:26:44.633703+00:00
-- url     : https://prove2.me/submissions/2e54d09c-4cb0-4dc3-bafd-cdb6415f6164

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Density
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiffOn_logLaplace_ball_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_readable
import Theorems.Thm_FunctionalInequalities_KLS_BorelLogConcave_exists_integrable_exp_norm_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_f_abs_exponential_moment_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_graph_norm_moment_of_local_moments_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_jointLaw_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_logConcave_jointLaw_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_joint_first_derivative_of_radii_readable

section
noncomputable section
open MeasureTheory Set Topology Filter
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
open scoped ContDiff in
/-- **A log-concave law has a smooth logarithmic Laplace transform near `0`**: for some `r > 0`,
`∫ e^{r‖x‖} dν < ∞` and `Λ_ν` is `C^∞` on the ball of radius `r` (BKL p. 29, through the Borell
exponential moment and `contDiffOn_logLaplace_ball`). -/
theorem FunctionalInequalities.KLS.LogConcave.exists_integrable_exp_norm_contDiffOn_logLaplace {ν : ProbabilityMeasure E} (hν : KLS.LogConcave ν) :
    ∃ r : ℝ, 0 < r ∧ Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure E) ∧
      ContDiffOn ℝ ∞ (Analysis.BakryEmery.logLaplace (ν : Measure E)) (Metric.ball 0 r) := by
  obtain ⟨r, hr, hi⟩ := ((KLS.LogConcave.borel_iff ν).1 hν).exists_integrable_exp_norm_readable
  exact ⟨r, hr, hi, Analysis.BakryEmery.contDiffOn_logLaplace_ball_readable (ν : Measure E) hr hi⟩
end FiniteDimensional
end
end

section
noncomputable section
open MeasureTheory Set
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted_readable hνW hW hconv)
end
end
end

section
open MeasureTheory FunctionalInequalities.Probability.Line
section
open FunctionalInequalities.Analysis.BakryEmery in
/-- **The joint law is log-concave** under (110) (BKL p. 28, "Then `W_N` is convex"): (109) from
`jointLaw_eq_tilted` and convexity of `W_N` from `logConcave_jointLaw_of_eq_tilted`. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_jointLaw {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ}
    (hβ : 0 < β) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (hint : Integrable (fun x => Real.exp (-V x)))
    (h : IsProbabilityMeasure (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)) :
    KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (JointSpace N n)) :=
  logConcave_jointLaw_of_eq_tilted_readable V f hβ hV hf hVa hfM hN
    (jointLaw_eq_tilted_readable V f hβ hV.continuous.measurable hf.continuous.measurable hint) h
open scoped ContDiff in
/-- **Local exponential moments and smoothness of `Λ_ν` under (110)** (BKL p. 29, "the logarithmic
Laplace transform is finite and smooth in a neighborhood of the origin"): for `μ = e^{-V}dx/Z` with
`∇²V ≥ a`, `f ∈ C²` with `‖∇²f‖ ≤ M` and `β M/√N ≤ a`, the joint law has an exponential moment
`e^{r‖p‖}` for some `r > 0` and `Λ_ν` is `C^∞` on the ball of radius `r`. The density (109) is
proved, not assumed. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw {n N : ℕ}
    (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ} (hβ : 0 < β) (hV : ContDiff ℝ 2 V)
    (hf : ContDiff ℝ 2 f) (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (hint : Integrable (fun x => Real.exp (-V x))) :
    ∃ r : ℝ, 0 < r ∧
      Integrable (fun p => Real.exp (r * ‖p‖))
        (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N) ∧
      ContDiffOn ℝ ∞ (Analysis.BakryEmery.logLaplace
        (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)) (Metric.ball 0 r) := by
  have : IsProbabilityMeasure (volume.tilted fun x => -V x) := isProbabilityMeasure_tilted hint
  have hp := isProbabilityMeasure_jointLaw_of_pos (volume.tilted fun x => -V x)
    hf.continuous.measurable hβ (sigma β) N
  exact (logConcave_jointLaw V f hβ hV hf hVa hfM hN hint hp).exists_integrable_exp_norm_contDiffOn_logLaplace
end
end

section
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
section
open scoped RealInnerProductSpace
/-- The graph law has an exponential moment when the joint law and `μ` do; no moment of `f` is
assumed. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_graph_norm_moment_from_joint {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r s : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) (hs : 0 < s)
    (hexp : Integrable (fun p : JointSpace N n => Real.exp (r * ‖p‖))
      (jointLaw μ f β (sigma β) N))
    (hxs : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
    ∃ t : ℝ, 0 < t ∧
      Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))
        (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
            EuclideanSpace ℝ (Option (Fin n))))) := by
  obtain ⟨a, ha, hfa⟩ := exists_f_abs_exponential_moment_readable μ hf hβ hN hr hexp
  exact exists_graph_norm_moment_of_local_moments_readable μ hf ha hs hfa hxs
end
end
end

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped Topology ContDiff
open FunctionalInequalities.Analysis.BakryEmery
open scoped Topology
/-- Source-path entry: graph moments are derived internally from the actual joint and mu radii. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_joint_first_derivative_neighborhood {n N : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r s : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) (hs : 0 < s)
    (hjoint : Integrable (fun p : JointSpace N n => Real.exp (r * ‖p‖))
      (jointLaw μ f β (sigma β) N))
    (hμ : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : JointSpace N n, z none = 0 → ‖z‖ < δ →
      HasDerivAt (fun w : ℝ => logLaplace (jointLaw μ f β (sigma β) N)
          (w • EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none + z))
        ((∑ i : Fin N, tiltAverage μ f
          (WithLp.toLp 2 fun j => z (some (i, j)))) / (sigma β * Real.sqrt N)) 0 := by
  obtain ⟨rG, hrG, hgraph⟩ := exists_graph_norm_moment_from_joint μ hf hβ hN hr hs hjoint hμ
  refine ⟨min r rG, lt_min hr hrG, ?_⟩
  intro z hz0 hz
  exact joint_first_derivative_of_radii_readable μ hf hβ hN hr hrG hjoint hgraph z hz0 hz
open FunctionalInequalities
open scoped ContDiff
/-- The actual source construction supplies both radii: no joint, graph or f moment premise.
This is the chosen-positive-N local germ (111), retaining the source condition (110). -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.source_joint_first_derivative {n N : ℕ}
    (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hNpos : 0 < N) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hint : Integrable (fun x => Real.exp (-V x)))
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (hN : β / Real.sqrt N * M ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : JointSpace N n, z none = 0 → ‖z‖ < δ →
      HasDerivAt (fun w : ℝ => logLaplace
          (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)
          (w • EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none + z))
        ((∑ i : Fin N, tiltAverage (volume.tilted fun x => -V x) f
          (WithLp.toLp 2 fun j => z (some (i, j)))) / (sigma β * Real.sqrt N)) 0 := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted fun x => -V x
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hint
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := ⟨μ, inferInstance⟩
  have hμlc : KLS.LogConcave ν :=
    KLS.LogConcave.logConcave_of_eq_tilted (ν := ν) rfl hV.continuous
      (convexOn_of_hessian_ge_readable hV ha.le hVa)
  obtain ⟨s, hs, hμ, _⟩ := hμlc.exists_integrable_exp_norm_contDiffOn_logLaplace
  obtain ⟨r, hr, hjoint, _⟩ := exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw
    V f hβ hV hf hVa hfM hN hint
  exact exists_joint_first_derivative_neighborhood μ
    hf.continuous.measurable hβ hNpos hr hs hjoint hμ
/-- **BKL (111)** for the source's chosen `N`. -/
theorem solution {n N : ℕ} (hN : 0 < N) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    {a b' : ℝ} (hV : FunctionalInequalities.KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ}
    (hβ : 0 < β) (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (h110 : β / Real.sqrt N * M ≤ a) :
    ∃ r > 0, ∀ z : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n, ‖z‖ < r → z none = 0 →
      fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (hV.law : Measure _) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) z
          (EuclideanSpace.single none 1) =
        (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)⁻¹ *
          ∑ i, FunctionalInequalities.Analysis.BakryEmery.tiltAverage (hV.law : Measure _) f (WithLp.toLp 2 fun j => z (some (i, j))) := by
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hint : Integrable (fun x => Real.exp (-V x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hV.integrable_exp_neg
  obtain ⟨δ, hδ, h111⟩ := FunctionalInequalities.KLS.LogConcave.Suspension.source_joint_first_derivative
    V f hV.pos hβ hN hV2 hf hint hV.lower hfM h110
  obtain ⟨r, hr, _, hcd⟩ := FunctionalInequalities.KLS.LogConcave.Suspension.exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw
    V f hβ hV2 hf hV.lower hfM h110 hint
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro z hz hz0
  have hzδ : ‖z‖ < δ := hz.trans_le (min_le_left δ r)
  have hzr : ‖z‖ < r := hz.trans_le (min_le_right δ r)
  have hdiff : DifferentiableAt ℝ
      (FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (hV.law : Measure _) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) z := by
    apply (hcd.contDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hzr))).differentiableAt
    simp
  let e0 : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n := EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none
  have hline : HasDerivAt (fun w : ℝ => w • e0 + z) e0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e0).add_const z
  have hF : HasFDerivAt (FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (hV.law : Measure _) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N))
      (fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (hV.law : Measure _) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) z)
      ((fun w : ℝ => w • e0 + z) 0) := by simpa using hdiff.hasFDerivAt
  have hd := hF.comp_hasDerivAt 0 hline
  have heq := hd.unique (h111 z hz0 hzδ)
  have hμeq : (hV.law : Measure _) = volume.tilted (fun x => -V x) := rfl
  simpa only [hμeq, e0, EuclideanSpace.basisFun_apply, div_eq_mul_inv, mul_comm] using heq
