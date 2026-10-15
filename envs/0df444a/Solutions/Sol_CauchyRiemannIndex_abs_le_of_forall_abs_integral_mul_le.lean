-- Prove2me | solution 1 for CauchyRiemannIndex.abs_le_of_forall_abs_integral_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T20:38:12.761949+00:00
-- url     : https://prove2.me/submissions/7492ce9b-b2c2-413b-a584-741746f8d6af

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Filter Topology Set
open scoped Convolution

theorem solution (h : ℝ → ℝ) (K : ℝ)
    (hh : IntegrableOn h (Set.Ico 0 1))
    (hK : ∀ φ : ℝ → ℝ, Continuous φ → Function.Periodic φ 1 →
      |∫ t in Set.Ico (0 : ℝ) 1, φ t * h t| ≤ K * ∫ t in Set.Ico (0 : ℝ) 1, |φ t|) :
    ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)), |h t| ≤ K := by
  set g : ℝ → ℝ := (Set.Ico (0 : ℝ) 1).indicator h with hg_def
  have hgi : Integrable g := (integrable_indicator_iff measurableSet_Ico).2 hh
  -- bumps of radius `1/(k+2)`
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun k =>
    ⟨1 / (2 * ((k : ℝ) + 2)), 1 / ((k : ℝ) + 2), by positivity, by
      have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]; linarith⟩
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
    show Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1) |>.congr
      (fun k => by simp; ring_nf)
  have h'φ : ∀ᶠ k in atTop, (φ k).rOut ≤ 2 * (φ k).rIn := by
    refine Eventually.of_forall fun k => ?_
    show 1 / ((k : ℝ) + 2) ≤ 2 * (1 / (2 * ((k : ℝ) + 2)))
    have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    rw [mul_one_div, show (2 : ℝ) / (2 * ((k : ℝ) + 2)) = 1 / ((k : ℝ) + 2) by field_simp]
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    hφ h'φ hgi.locallyIntegrable
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    have : (volume : Measure ℝ) {(0 : ℝ)} = 0 := measure_singleton 0
    exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun t ht => by simpa using ht
  rw [ae_restrict_iff' measurableSet_Ico]
  filter_upwards [hae, hne] with x hx hx0 hxI
  have hxI' : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), hxI.2⟩
  have hgx : g x = h x := by simp [hg_def, hxI]
  rw [hgx] at hx
  -- eventually the support of the bump around `x` is inside `(0,1)`
  have hev : ∀ᶠ k in atTop, (φ k).rOut < min x (1 - x) :=
    hφ.eventually (gt_mem_nhds (lt_min hxI'.1 (by linarith [hxI'.2])))
  have hbound : ∀ᶠ k in atTop,
      |((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x| ≤ K := by
    filter_upwards [hev] with k hk
    set b := (φ k).normed volume with hb
    have hr1 : (φ k).rOut < x := hk.trans_le (min_le_left _ _)
    have hr2 : (φ k).rOut < 1 - x := hk.trans_le (min_le_right _ _)
    have hbz : ∀ y, (φ k).rOut ≤ |y| → b y = 0 := by
      intro y hy
      have : y ∉ Function.support b := by
        rw [hb, (φ k).support_normed_eq]; simpa [Metric.mem_ball, Real.dist_eq] using hy
      simpa using this
    -- the test function
    let ψ : ℝ → ℝ := (fun s => b (x - s)) ∘ Int.fract
    have hψc : Continuous ψ := by
      refine ContinuousOn.comp_fract'' ?_ ?_
      · exact ((φ k).continuous_normed.comp (continuous_const.sub continuous_id)).continuousOn
      · show b (x - 0) = b (x - 1)
        rw [hbz _ (by rw [sub_zero, abs_of_pos hxI'.1]; exact hr1.le),
          hbz _ (by rw [abs_sub_comm, abs_of_pos (by linarith [hxI'.2])]; exact hr2.le)]
    have hψp : Function.Periodic ψ 1 := fun s => by simp [ψ, Int.fract_add_one]
    have hψI : ∀ s ∈ Ico (0 : ℝ) 1, ψ s = b (x - s) := fun s hs => by
      simp [ψ, Int.fract_eq_self.2 hs]
    have hsupp : ∀ s ∉ Ico (0 : ℝ) 1, b (x - s) = 0 := by
      intro s hs
      apply hbz
      rcases lt_or_ge s 0 with h0 | h0
      · rw [abs_of_pos (by linarith [hxI'.1])]; linarith
      · have : 1 ≤ s := by
          by_contra h1; exact hs ⟨h0, lt_of_not_ge h1⟩
        rw [abs_of_neg (by linarith [hxI'.2])]; linarith
    have hconv : ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
        ∫ t in Ico (0 : ℝ) 1, ψ t * h t := by
      rw [convolution_eq_swap]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      rw [← integral_indicator measurableSet_Ico]
      congr 1; funext t
      by_cases ht : t ∈ Ico (0 : ℝ) 1
      · simp [hg_def, ht, hψI t ht, hb]
      · simp [hg_def, ht]
    have hnorm : ∫ t in Ico (0 : ℝ) 1, |ψ t| = 1 := by
      rw [setIntegral_congr_fun measurableSet_Ico (fun t ht => by
        rw [hψI t ht, abs_of_nonneg ((φ k).nonneg_normed _)])]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => hsupp t ht)]
      rw [integral_sub_left_eq_self (fun s => b s) volume x]
      exact (φ k).integral_normed
    rw [hconv]
    simpa [hnorm] using hK ψ hψc hψp
  exact le_of_tendsto (hx.abs) hbound

