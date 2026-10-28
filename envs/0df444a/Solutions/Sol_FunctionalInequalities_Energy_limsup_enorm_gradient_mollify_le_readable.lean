-- Prove2me | solution 1 for FunctionalInequalities.Energy.limsup_enorm_gradient_mollify_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:33.77267+00:00
-- url     : https://prove2.me/submissions/8008c9a2-b5be-4e2e-b2e2-b309b4f1d413

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Theorems.Thm_FunctionalInequalities_Energy_lipschitzOnWith_mollify_ball_readable

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
universe u
section Metric
variable {X : Type*} [MetricSpace X]
theorem FunctionalInequalities.Energy.AsymptoticLipschitz.apply_eq_iInf_secant (f : X → ℝ) (x : X) :
    apply f x = ⨅ (r : ℝ) (_ : 0 < r), secant f r x :=
  rfl
/-- Below any strict upper bound for the asymptotic Lipschitz constant there is a radius whose
secant supremum already respects it. -/
theorem FunctionalInequalities.Energy.AsymptoticLipschitz.exists_secant_le {f : X → ℝ} {x : X} {c : ℝ≥0∞} (h : apply f x < c) :
    ∃ r : ℝ, 0 < r ∧ secant f r x ≤ c := by
  rw [apply_eq_iInf_secant, iInf_lt_iff] at h
  obtain ⟨r, hr⟩ := h
  rw [iInf_lt_iff] at hr
  obtain ⟨hr0, hlt⟩ := hr
  exact ⟨r, hr0, hlt.le⟩
/-- A bound on the secant supremum is a Lipschitz-type bound on the ball. -/
theorem FunctionalInequalities.Energy.AsymptoticLipschitz.dist_le_of_secant_le {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : secant f r x ≤ ENNReal.ofReal c) {y z : X} (hy : dist y x < r) (hz : dist z x < r) :
    dist (f y) (f z) ≤ c * dist y z := by
  rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := z)) with h0 | h0
  · have : y = z := by simpa [eq_comm] using h0.symm
    simp [this]
  · have hle : ENNReal.ofReal (dist (f y) (f z) / dist y z) ≤ secant f r x := by
      simp only [secant]
      refine le_iSup₂_of_le y hy ?_
      exact le_iSup₂_of_le z hz le_rfl
    have hq : ENNReal.ofReal (dist (f y) (f z) / dist y z) ≤ ENNReal.ofReal c := hle.trans h
    rw [ENNReal.ofReal_le_ofReal_iff hc, div_le_iff₀ h0] at hq
    exact hq
end Metric
section Mollification
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [CompleteSpace V] [SecondCountableTopology V] in
/-- The mollification's derivative at `x` respects every Lipschitz constant of `g` on a slightly
larger ball. -/
theorem FunctionalInequalities.Energy.norm_fderiv_mollify_le_of_lipschitzOnWith (m : Measure V) [m.IsAddHaarMeasure]
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {c : ℝ≥0} {g : V → ℝ} (hg : Continuous g) (x : V)
    (h : LipschitzOnWith c g (Metric.ball x (δ + 2 * R))) :
    ‖fderiv ℝ (mollify m R g) x‖ ≤ c :=
  ((hasFDerivAt_mollify m hR hg x).differentiableAt.hasFDerivAt).le_of_lipschitzOn
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
    (lipschitzOnWith_mollify_ball_readable m hR hg x h)
omit [SecondCountableTopology V] in
/-- Pointwise reverse convergence: the gradient norms of the mollifications do not exceed the
asymptotic Lipschitz constant in the limit. -/
theorem solution (m : Measure V) [m.IsAddHaarMeasure]
    {g : V → ℝ} (hg : Continuous g) (x : V) :
    limsup (fun j ↦ ‖gradient (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.mollify m (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j) g) x‖ₑ) atTop ≤
      FunctionalInequalities.Energy.AsymptoticLipschitz.apply g x := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  set A : ℝ≥0∞ := FunctionalInequalities.Energy.AsymptoticLipschitz.apply g x with hA
  have hAtop : A ≠ ⊤ := hlt.ne
  have hstep : A < A + (ε : ℝ≥0∞) := ENNReal.lt_add_right hAtop (by exact_mod_cast hε.ne')
  obtain ⟨r, hr0, hsec⟩ := FunctionalInequalities.Energy.AsymptoticLipschitz.exists_secant_le hstep
  set c : ℝ≥0 := (A + (ε : ℝ≥0∞)).toNNReal with hc
  have hctop : A + (ε : ℝ≥0∞) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hAtop, ENNReal.coe_ne_top⟩
  have hcc : (c : ℝ≥0∞) = A + (ε : ℝ≥0∞) := ENNReal.coe_toNNReal hctop
  have hseq : FunctionalInequalities.Energy.AsymptoticLipschitz.secant g r x ≤ ENNReal.ofReal (c : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal, hcc]
    exact hsec
  have hlipball : LipschitzOnWith c g (Metric.ball x r) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
    exact FunctionalInequalities.Energy.AsymptoticLipschitz.dist_le_of_secant_le c.coe_nonneg hseq
      (by simpa [Metric.mem_ball, dist_comm] using hy)
      (by simpa [Metric.mem_ball, dist_comm] using hz)
  have hev : ∀ᶠ j in atTop, ‖gradient (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.mollify m (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j) g) x‖ₑ ≤ (c : ℝ≥0∞) := by
    have h3 : Tendsto (fun j ↦ 3 * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j) atTop (𝓝 0) := by
      simpa using FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.tendsto_radius.const_mul (3 : ℝ)
    filter_upwards [(tendsto_order.1 h3).2 r hr0] with j hj
    have hsub : Metric.ball x (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j + 2 * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j) ⊆ Metric.ball x r := by
      refine Metric.ball_subset_ball ?_
      linarith
    have hbd : ‖fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.mollify m (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j) g) x‖ ≤ (c : ℝ) :=
      FunctionalInequalities.Energy.norm_fderiv_mollify_le_of_lipschitzOnWith m (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius_pos j) (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius_pos j) hg x
        (hlipball.mono hsub)
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.norm_gradient_eq_norm_fderiv]
    exact hbd
  rw [← hcc]
  exact limsup_le_of_le (by isBoundedDefault) hev
