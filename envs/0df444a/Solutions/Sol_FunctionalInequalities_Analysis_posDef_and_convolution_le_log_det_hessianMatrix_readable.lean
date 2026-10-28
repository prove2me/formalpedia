-- Prove2me | solution 1 for FunctionalInequalities.Analysis.posDef_and_convolution_le_log_det_hessianMatrix_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:32.485+00:00
-- url     : https://prove2.me/submissions/b485d23c-8025-405b-80db-4724abf06e40

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
import Theorems.Thm_FunctionalInequalities_Analysis_forall_posDef_add_log_det_le_trace_iff_readable
import Theorems.Thm_FunctionalInequalities_Analysis_posSemidef_hessianMatrix_of_upper_touch_readable
import Theorems.Thm_FunctionalInequalities_Analysis_convolution_hessian_integral_readable
import Theorems.Thm_FunctionalInequalities_Analysis_trace_integral_bound_readable

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12D8MollifiedLogdetBound
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
private lemma FunctionalInequalities.Analysis.convolution_shift {n : ℕ}
    (ρ u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x a : EuclideanSpace ℝ (Fin n)) :
    (∫ y, u (y + a) * ρ (x - y)) =
      convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + a) := by
  rw [← integral_sub_left_eq_self (fun y => u (y + a) * ρ (x - y)) volume x]
  unfold convolution
  apply integral_congr_ae
  filter_upwards [] with y
  have he : x - y + a = x + a - y := by abel
  simp only [sub_sub_cancel, he, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_comm _ _
private lemma FunctionalInequalities.Analysis.convolution_convex {n : ℕ}
    {ρ u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hconv : ConvexOn ℝ univ u) :
    ConvexOn ℝ univ (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hi (z : EuclideanSpace ℝ (Fin n)) :
      Integrable (fun y => ρ y * u (z - y)) volume := by
    have hc : Continuous (fun y => ρ y * u (z - y)) :=
      hρ.mul (hu.comp (continuous_const.sub continuous_id))
    exact hc.integrable_of_hasCompactSupport hρc.mul_right
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ s t hs ht hst
  change (∫ y, ρ y * u (s • a + t • b - y)) ≤
    s * (∫ y, ρ y * u (a - y)) + t * (∫ y, ρ y * u (b - y))
  calc
    _ ≤ ∫ y, s * (ρ y * u (a - y)) + t * (ρ y * u (b - y)) := by
      apply integral_mono (hi _) (((hi a).const_mul s).add ((hi b).const_mul t))
      intro y
      change ρ y * u (s • a + t • b - y) ≤
        s * (ρ y * u (a - y)) + t * (ρ y * u (b - y))
      have hc := hconv.2 (mem_univ (a - y)) (mem_univ (b - y)) hs ht hst
      have he : s • (a - y) + t • (b - y) = s • a + t • b - y := by
        calc
          _ = s • a + t • b - (s + t) • y := by module
          _ = _ := by rw [hst, one_smul]
      rw [he] at hc
      change u (s • a + t • b - y) ≤ s * u (a - y) + t * u (b - y) at hc
      calc
        _ ≤ ρ y * (s * u (a - y) + t * u (b - y)) :=
          mul_le_mul_of_nonneg_left hc (hρ0 y)
        _ = _ := by ring
    _ = _ := by
      rw [integral_add
        (f := fun y => s * (ρ y * u (a - y)))
        (g := fun y => t * (ρ y * u (b - y)))
        ((hi a).const_mul s) ((hi b).const_mul t),
        integral_const_mul, integral_const_mul]
/-- **Mollified log-det lower bound** (weak Letwin route; KLS500
`weak_moment_mollified_average_det_lower`, via Fatou instead of the viscosity–distribution lemma): if the
convex `u` has at almost every point a second-order expansion with a positive definite symmetric matrix
`B` with `F x ≤ log det B`, `F` continuous, then every mollification `uφ := φ.normed ⋆ u` has a positive
definite Hessian with `(φ.normed ⋆ F)(x) ≤ log det ∇²uφ(x)`. -/
theorem solution {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧ F x ≤ Real.log B.det ∧
        ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - FunctionalInequalities.Analysis.quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    (FunctionalInequalities.Probability.Stein.hessianMatrix (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x).PosDef ∧
      convolution (φ.normed volume) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x ≤
        Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix
          (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x).det := by
  classical
  let ρ := φ.normed volume
  let w := convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  let χ := fun y => ρ (x - y)
  let H := FunctionalInequalities.Probability.Stein.hessianMatrix w x
  let b := convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x
  have hρ : ContDiff ℝ 2 ρ := φ.contDiff_normed
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hρ0 : ∀ y, 0 ≤ ρ y := φ.nonneg_normed
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hw : ContDiff ℝ 2 w :=
    hρc.contDiff_convolution_left _ hρ hu.locallyIntegrable
  have hwconv : ConvexOn ℝ univ w :=
    FunctionalInequalities.Analysis.convolution_convex hρ.continuous hρc hρ0 hconv
  have hH : H.PosSemidef :=
    FunctionalInequalities.Analysis.posSemidef_hessianMatrix_of_upper_touch_readable hwconv hw.contDiffAt rfl
      (Filter.Eventually.of_forall fun _ => le_rfl)
  have hχ : ContDiff ℝ 2 χ := hρ.comp (contDiff_const.sub contDiff_id)
  have hχc : HasCompactSupport χ := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hχ0 : ∀ y, 0 ≤ χ y := fun y => hρ0 (x - y)
  have hχi : Integrable χ volume :=
    hχ.continuous.integrable_of_hasCompactSupport hχc
  have hχone : (∫ y, χ y) = 1 := by
    dsimp only [χ]
    rw [integral_sub_left_eq_self]
    exact φ.integral_normed
  have hb : (∫ y, F y * χ y) = b := by
    simpa only [χ, b, add_zero] using FunctionalInequalities.Analysis.convolution_shift ρ F x 0
  have hFi : Integrable (fun y => F y * χ y) volume :=
    (hF.mul hχ.continuous).integrable_of_hasCompactSupport hχc.mul_left
  have htrace : ∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef →
      b + Real.log J.det + n ≤ (J * H).trace := by
    intro J hJ
    have ht := FunctionalInequalities.Analysis.trace_integral_bound_readable hconv hF hae hχ hχc hχ0 H
      (fun v => FunctionalInequalities.Analysis.convolution_hessian_integral_readable hρ hρc hu x v) J hJ
    have he :
        (∫ y, (F y + Real.log J.det + n) * χ y) =
          b + Real.log J.det + n := by
      calc
        _ = ∫ y, (F y * χ y + Real.log J.det * χ y) + (n : ℝ) * χ y := by
          apply integral_congr_ae
          filter_upwards [] with y
          ring
        _ = _ := by
          rw [integral_add
              (f := fun y => F y * χ y + Real.log J.det * χ y)
              (g := fun y => (n : ℝ) * χ y)
              (hFi.add (hχi.const_mul (Real.log J.det))) (hχi.const_mul (n : ℝ)),
            integral_add
              (f := fun y => F y * χ y)
              (g := fun y => Real.log J.det * χ y)
              hFi (hχi.const_mul (Real.log J.det)),
            integral_const_mul, integral_const_mul, hχone, hb, mul_one, mul_one]
    exact he ▸ ht
  obtain ⟨hpos, hdet⟩ := (FunctionalInequalities.Analysis.forall_posDef_add_log_det_le_trace_iff_readable hH b).mp htrace
  exact ⟨hpos, (Real.le_log_iff_exp_le hpos.det_pos).mpr hdet⟩
