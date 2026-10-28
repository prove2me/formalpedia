-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_hessian_increment_le_generator_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:34.741099+00:00
-- url     : https://prove2.me/submissions/fc8789c5-bfc5-4673-a912-a85a1d80b37c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
import Theorems.Thm_FunctionalInequalities_Analysis_log_det_add_frobenius_sq_le_readable

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LN11AHessianIncrementCoercivity
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
private lemma FunctionalInequalities.Analysis.increment_fderiv {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Differentiable ℝ u)
    (h : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => u (y + h) + u (y - h) - 2 * u y) =
      fun y => fderiv ℝ u (y + h) + fderiv ℝ u (y - h) -
        (fderiv ℝ u y + fderiv ℝ u y) := by
  funext y
  have hp : DifferentiableAt ℝ (fun z => u (z + h)) y :=
    (hu (y + h)).comp y (differentiableAt_id.add_const h)
  have hm : DifferentiableAt ℝ (fun z => u (z - h)) y :=
    (hu (y - h)).comp y (differentiableAt_id.sub_const h)
  simp only [two_mul]
  rw [fderiv_fun_sub (hp.fun_add hm) ((hu y).fun_add (hu y)),
    fderiv_fun_add hp hm, fderiv_fun_add (hu y) (hu y),
    fderiv_comp_add_right]
  simpa only [sub_eq_add_neg] using
    congrArg
      (fun q => fderiv ℝ u (y + h) + q - (fderiv ℝ u y + fderiv ℝ u y))
      (fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := y) (-h))
private lemma FunctionalInequalities.Analysis.increment_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Differentiable ℝ u)
    (h x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => u (y + h) + u (y - h) - 2 * u y) x =
      gradient u (x + h) + gradient u (x - h) - 2 • gradient u x := by
  change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (fun y => u (y + h) + u (y - h) - 2 * u y) x) = _
  rw [increment_fderiv hu h]
  simp only [map_sub, map_add, gradient, two_smul]
private lemma FunctionalInequalities.Analysis.increment_hessian {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Differentiable ℝ u)
    (h x : EuclideanSpace ℝ (Fin n))
    (hx : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hp : DifferentiableAt ℝ (fderiv ℝ u) (x + h))
    (hm : DifferentiableAt ℝ (fderiv ℝ u) (x - h)) :
    hessianMatrix (fun y => u (y + h) + u (y - h) - 2 * u y) x =
      hessianMatrix u (x + h) + hessianMatrix u (x - h) -
        2 • hessianMatrix u x := by
  have dp : DifferentiableAt ℝ (fun y => fderiv ℝ u (y + h)) x :=
    hp.comp x (differentiableAt_id.add_const h)
  have dm : DifferentiableAt ℝ (fun y => fderiv ℝ u (y - h)) x :=
    hm.comp x (differentiableAt_id.sub_const h)
  ext i j
  change
    fderiv ℝ (fderiv ℝ (fun y => u (y + h) + u (y - h) - 2 * u y)) x _ _ = _
  rw [increment_fderiv hu h,
    fderiv_fun_sub (dp.fun_add dm) (hx.fun_add hx),
    fderiv_fun_add dp dm, fderiv_fun_add hx hx, fderiv_comp_add_right]
  have ht :
      fderiv ℝ (fun y => fderiv ℝ u (y - h)) x =
        fderiv ℝ (fderiv ℝ u) (x - h) := by
    simpa only [sub_eq_add_neg] using
      (fderiv_comp_add_right (𝕜 := ℝ) (f := fderiv ℝ u) (x := x) (-h))
  rw [ht]
  simp [hessianMatrix, bilinearIteratedFDerivTwo, two_smul]
private lemma FunctionalInequalities.Analysis.convex_fderiv_le_sub {n : ℕ}
    {V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hV : Differentiable ℝ V) (hc : ConvexOn ℝ univ V)
    (c a : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ V c (a - c) ≤ V a - V c := by
  let q : ℝ → ℝ := fun t => V (c + t • (a - c))
  have hq : ConvexOn ℝ univ q := by
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ α β hα hβ hab
    have he₀ :
        (α + β) • c + (α * s + β * t) • (a - c) =
          α • (c + s • (a - c)) + β • (c + t • (a - c)) := by
      module
    have he :
        c + (α * s + β * t) • (a - c) =
          α • (c + s • (a - c)) + β • (c + t • (a - c)) := by
      simpa only [hab, one_smul] using he₀
    simpa only [q, smul_eq_mul, he] using
      hc.2 (mem_univ (c + s • (a - c))) (mem_univ (c + t • (a - c)))
        hα hβ hab
  have hd : HasDerivAt q (fderiv ℝ V c (a - c)) 0 := by
    have hl :=
      ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (a - c)).const_add c
    have hv :
        HasFDerivAt V (fderiv ℝ V c) (c + (0 : ℝ) • (a - c)) := by
      simpa using (hV c).hasFDerivAt
    simpa [q, Function.comp_def] using hv.comp_hasDerivAt 0 hl
  have hs :=
    hq.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num) hd
  simpa [q, slope] using hs
/-- **Three-point log-det concavity** (weak Letwin route): for positive definite `A, B₊, B₋ ≤ K·Id`,
`(‖B₊ − A‖²_F + ‖B₋ − A‖²_F)/(2K²) ≤ tr(A⁻¹(B₊ + B₋ − 2A)) − log det B₊ − log det B₋ + 2 log det A`. -/
theorem FunctionalInequalities.Analysis.frobenius_add_frobenius_le_trace_sub_log_det {n : ℕ}
    {A Bp Bm : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} (hA : A.PosDef) (hBp : Bp.PosDef) (hBm : Bm.PosDef)
    (hAK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
    (hBpK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - Bp).PosSemidef)
    (hBmK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - Bm).PosSemidef) :
    ((∑ i, ∑ j, (Bp - A) i j ^ 2) + ∑ i, ∑ j, (Bm - A) i j ^ 2) / (2 * K ^ 2) ≤
      (A⁻¹ * (Bp + Bm - 2 • A)).trace - Real.log Bp.det - Real.log Bm.det + 2 * Real.log A.det := by
  have hp := log_det_add_frobenius_sq_le_readable hA hBp hAK hBpK
  have hm := log_det_add_frobenius_sq_le_readable hA hBm hAK hBmK
  have he : Bp + Bm - 2 • A = (Bp - A) + (Bm - A) := by
    rw [two_smul]
    abel
  rw [he, Matrix.mul_add, Matrix.trace_add, add_div]
  linarith
/-- **Pointwise coercivity of Hessian increments for a `C^{1,1}` Monge–Ampère solution** (weak Letwin route; KLS500 `weak_moment_centered_difference_coercivity_ae`): if a.e. `∇²u` is positive definite, `≤ K·Id`, and
`log det ∇²u = −u + V(∇u)` with `V` convex and differentiable, then for every `h`, at a.e. `x`, with
`w := u(· + h) + u(· − h) − 2u` and `H := ∇²u`,
`(‖H(x+h) − H(x)‖²_F + ‖H(x−h) − H(x)‖²_F)/(2K²) ≤ tr(H(x)⁻¹ ∇²w(x)) − DV(∇u(x))(∇w(x)) + w(x)`. -/
theorem solution {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : Differentiable ℝ V) (hVc : ConvexOn ℝ univ V) {K : ℝ}
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
      Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef)
    (h : EuclideanSpace ℝ (Fin n)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) +
          ∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) / (2 * K ^ 2) ≤
        ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            FunctionalInequalities.Probability.Stein.hessianMatrix (fun y => u (y + h) + u (y - h) - 2 * u y) x).trace -
          fderiv ℝ V (gradient u x) (gradient (fun y => u (y + h) + u (y - h) - 2 * u y) x) +
          (u (x + h) + u (x - h) - 2 * u x) := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hd :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        DifferentiableAt ℝ (fderiv ℝ u) x := by
    filter_upwards [hG.ae_differentiableAt
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
    rw [← toDual_comp_gradient]
    exact
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).differentiable.differentiableAt.comp
        x hx
  have hgood := hdata.and hd
  have hplus :=
    (measurePreserving_add_right
      (volume : Measure (EuclideanSpace ℝ (Fin n))) h).quasiMeasurePreserving.ae hgood
  have hminus :=
    (measurePreserving_add_right
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (-h)).quasiMeasurePreserving.ae hgood
  filter_upwards [hgood, hplus, hminus] with x hx hp hm
  simp only [← sub_eq_add_neg] at hm
  have hH := FunctionalInequalities.Analysis.increment_hessian hud h x hx.2 hp.2 hm.2
  have hg := FunctionalInequalities.Analysis.increment_gradient hud h x
  have hlog :=
    FunctionalInequalities.Analysis.frobenius_add_frobenius_le_trace_sub_log_det
      hx.1.1 hp.1.1 hm.1.1 hx.1.2.2 hp.1.2.2 hm.1.2.2
  rw [hp.1.2.1, hm.1.2.1, hx.1.2.1] at hlog
  have hVp := FunctionalInequalities.Analysis.convex_fderiv_le_sub hV hVc (gradient u x) (gradient u (x + h))
  have hVm := FunctionalInequalities.Analysis.convex_fderiv_le_sub hV hVc (gradient u x) (gradient u (x - h))
  have hconv :
      fderiv ℝ V (gradient u x)
          (gradient u (x + h) + gradient u (x - h) - 2 • gradient u x) ≤
        V (gradient u (x + h)) + V (gradient u (x - h)) -
          2 * V (gradient u x) := by
    simp only [two_smul, map_sub, map_add] at hVp hVm ⊢
    linarith
  rw [hH, hg]
  linarith only [hlog, hconv]
