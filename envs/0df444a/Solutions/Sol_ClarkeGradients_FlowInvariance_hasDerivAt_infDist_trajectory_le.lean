-- Prove2me | solution 1 for ClarkeGradients.FlowInvariance.hasDerivAt_infDist_trajectory_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:33:03.553358+00:00
-- url     : https://prove2.me/submissions/24344847-734e-4295-a55a-5f3d01284422

import Mathlib
import Definitions.Def_ClarkeGradients_FlowInvariance_tangentCone
import Definitions.Def_ClarkeGradients_FlowInvariance_IsTrajectory

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace P62eeecfb

/-- Lower bound on the squared distance near a point of the segment from `y` toward `x`,
where `y` is a nearest point of `F` to `x`. -/
lemma sqdist_lower {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    (x y : EuclideanSpace ℝ (Fin n)) (hnear : ∀ y' ∈ F, ‖x - y‖ ≤ ‖x - y'‖)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1 / 2) (h : EuclideanSpace ℝ (Fin n)) :
    ‖l • (x - y)‖ ^ 2 + 2 * inner ℝ (l • (x - y)) h - ‖h‖ ^ 2
      ≤ Metric.infDist (y + l • (x - y) + h) F ^ 2 := by
  set L := ‖l • (x - y)‖ ^ 2 + 2 * inner ℝ (l • (x - y)) h - ‖h‖ ^ 2 with hL
  rcases le_or_gt L 0 with hL0 | hL0
  · exact le_trans hL0 (sq_nonneg _)
  have key : ∀ y' ∈ F, L ≤ dist (y + l • (x - y) + h) y' ^ 2 := by
    intro y' hy'
    have hn := hnear y' hy'
    have hab : x - y' = (x - y) + (y - y') := by abel
    have hz : y + l • (x - y) + h - y' = l • (x - y) + h + (y - y') := by abel
    rw [dist_eq_norm, hz, hL]
    rw [hab] at hn
    have hn2 : ‖x - y‖ ^ 2 ≤ ‖(x - y) + (y - y')‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    rw [norm_add_sq_real] at hn2
    have hcs' := neg_le_of_abs_le (abs_real_inner_le_norm h (y - y'))
    rw [norm_add_sq_real, norm_add_sq_real, inner_add_left]
    simp only [real_inner_smul_left]
    have hA : 0 ≤ 2 * inner ℝ (x - y) (y - y') + ‖y - y'‖ ^ 2 := by linarith
    nlinarith [mul_nonneg hl0.le hA, mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 2 - l)
      (sq_nonneg ‖y - y'‖), sq_nonneg (‖h‖ - ‖y - y'‖ / 2)]
  have hsq : Real.sqrt L ≤ Metric.infDist (y + l • (x - y) + h) F := by
    rw [Metric.le_infDist hF]
    intro y' hy'
    calc Real.sqrt L ≤ Real.sqrt (dist (y + l • (x - y) + h) y' ^ 2) :=
          Real.sqrt_le_sqrt (key y' hy')
      _ = dist (y + l • (x - y) + h) y' := Real.sqrt_sq dist_nonneg
  calc L = Real.sqrt L ^ 2 := (Real.sq_sqrt hL0.le).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2


lemma hasFDerivAt_sqdist {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    (x y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ F) (hnear : ∀ y' ∈ F, ‖x - y‖ ≤ ‖x - y'‖)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1 / 2) :
    HasFDerivAt (fun p => Metric.infDist p F ^ 2) (2 • innerSL ℝ (l • (x - y)))
      (y + l • (x - y)) ∧ Metric.infDist (y + l • (x - y)) F ^ 2 = ‖l • (x - y)‖ ^ 2 := by
  have hup : ∀ h : EuclideanSpace ℝ (Fin n), Metric.infDist (y + l • (x - y) + h) F ^ 2
      ≤ ‖l • (x - y)‖ ^ 2 + 2 * inner ℝ (l • (x - y)) h + ‖h‖ ^ 2 := by
    intro h
    have h1 : Metric.infDist (y + l • (x - y) + h) F ≤ ‖l • (x - y) + h‖ := by
      have := Metric.infDist_le_dist_of_mem (x := y + l • (x - y) + h) hy
      have e : y + l • (x - y) + h - y = l • (x - y) + h := by abel
      rw [dist_eq_norm, e] at this
      exact this
    rw [← norm_add_sq_real]
    exact pow_le_pow_left₀ Metric.infDist_nonneg h1 2
  have hlo := sqdist_lower F hF x y hnear l hl0 hl1
  have h0 : Metric.infDist (y + l • (x - y)) F ^ 2 = ‖l • (x - y)‖ ^ 2 := by
    have a1 := hup 0
    have a2 := hlo 0
    simp only [add_zero, inner_zero_right, mul_zero, norm_zero] at a1 a2
    norm_num at a1 a2
    linarith
  refine ⟨?_, h0⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id (by norm_num))
  refine Asymptotics.IsBigO.of_bound' (Eventually.of_forall fun h => ?_)
  have a1 := hup h
  have a2 := hlo h
  have e : (2 • innerSL ℝ (l • (x - y))) h = 2 * inner ℝ (l • (x - y)) h := by
    rw [ContinuousLinearMap.smul_apply, innerSL_apply_apply, two_smul, two_mul]
  rw [e, h0, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖), abs_le]
  constructor <;> linarith

lemma gradient_dist {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    (x y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ F) (hnear : ∀ y' ∈ F, ‖x - y‖ ≤ ‖x - y'‖)
    (hxy : x - y ≠ 0) (l : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1 / 2) :
    DifferentiableAt ℝ (fun p => Metric.infDist p F) (y + l • (x - y)) ∧
      gradient (fun p => Metric.infDist p F) (y + l • (x - y)) = ‖x - y‖⁻¹ • (x - y) := by
  obtain ⟨hd, h0⟩ := hasFDerivAt_sqdist F hF x y hy hnear l hl0 hl1
  have heq : (fun p => Metric.infDist p F) = fun p => Real.sqrt (Metric.infDist p F ^ 2) := by
    funext p; rw [Real.sqrt_sq Metric.infDist_nonneg]
  have hne : Metric.infDist (y + l • (x - y)) F ^ 2 ≠ 0 := by
    rw [h0]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (smul_ne_zero hl0.ne' hxy))
  have hs := hd.sqrt hne
  rw [← heq] at hs
  have hg : HasGradientAt (fun p => Metric.infDist p F) (‖x - y‖⁻¹ • (x - y)) (y + l • (x - y)) := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hn : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr hxy
    have e : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (‖x - y‖⁻¹ • (x - y)) =
        (1 / (2 * Real.sqrt (Metric.infDist (y + l • (x - y)) F ^ 2))) •
          (2 • innerSL ℝ (l • (x - y))) := by
      refine ContinuousLinearMap.ext fun h => ?_
      rw [h0, Real.sqrt_sq (norm_nonneg _), ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, innerSL_apply_apply, InnerProductSpace.toDual_apply_apply,
        two_smul, real_inner_smul_left, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hl0, smul_eq_mul]
      field_simp
      ring
    rw [e]
    exact hs
  exact ⟨hg.differentiableAt, hg.gradient⟩

lemma mem_normalCone {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    (x y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ F) (hnear : ∀ y' ∈ F, ‖x - y‖ ≤ ‖x - y'‖)
    (hxy : x - y ≠ 0) :
    ‖x - y‖⁻¹ • (x - y) ∈ ClarkeGradients.FlowInvariance.normalCone F y := by
  refine subset_closure ⟨1, one_pos, ?_⟩
  rw [one_smul]
  apply subset_convexHull
  set l : ℕ → ℝ := fun i => 1 / (((i + 1 : ℕ) : ℝ) + 1) with hl
  have hl0 : ∀ i, 0 < l i := fun i => by simp only [hl]; positivity
  have hl1 : ∀ i, l i ≤ 1 / 2 := fun i => by
    simp only [hl]
    apply one_div_le_one_div_of_le (by norm_num)
    have : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
    linarith
  refine ⟨fun i => l i • (x - y), ?_, fun i => (gradient_dist F hF x y hy hnear hxy (l i)
    (hl0 i) (hl1 i)).1, ?_⟩
  · have ht : Tendsto l atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    simpa using ht.smul_const (x - y)
  · have : (fun i => gradient (fun p => Metric.infDist p F) (y + l i • (x - y)))
        = fun _ => ‖x - y‖⁻¹ • (x - y) := funext fun i =>
      (gradient_dist F hF x y hy hnear hxy (l i) (hl0 i) (hl1 i)).2
    rw [this]
    exact tendsto_const_nhds

end P62eeecfb

open MeasureTheory in
theorem solution {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hX : ∀ x, (X x).Nonempty ∧ IsCompact (X x)) (K : ℝ)
    (hK : ∀ x₁ x₂ : EuclideanSpace ℝ (Fin n), ∀ v₁ ∈ X x₁, ∃ v₂ ∈ X x₂,
      ‖v₁ - v₂‖ ≤ K * ‖x₁ - x₂‖)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F)
    (htan : ∀ y ∈ F, X y ⊆ ClarkeGradients.FlowInvariance.tangentCone F y)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : ClarkeGradients.FlowInvariance.IsTrajectory X x)
    (hx0 : x 0 ∈ F) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ d : ℝ,
      HasDerivAt (fun s => Metric.infDist (x s) F) d t →
        d ≤ K * Metric.infDist (x t) F := by
  filter_upwards [hx.2] with t ht d hd
  obtain ⟨w, hw, hxw⟩ := ht
  by_cases h0 : Metric.infDist (x t) F = 0
  · have hmin : IsLocalMin (fun s => Metric.infDist (x s) F) t :=
      Eventually.of_forall (fun s => by
        show Metric.infDist (x t) F ≤ Metric.infDist (x s) F
        rw [h0]; exact Metric.infDist_nonneg)
    rw [hmin.hasDerivAt_eq_zero hd, h0, mul_zero]
  · have hpos : 0 < Metric.infDist (x t) F := lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm h0)
    obtain ⟨y, hy, hyd⟩ := hFc.exists_infDist_eq_dist hF (x t)
    rw [dist_eq_norm] at hyd
    have hnear : ∀ y' ∈ F, ‖x t - y‖ ≤ ‖x t - y'‖ := fun y' hy' => by
      rw [← hyd, ← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hy'
    have ha : x t - y ≠ 0 := by
      intro h; rw [hyd, h, norm_zero] at hpos; exact lt_irrefl _ hpos
    have hu := P62eeecfb.mem_normalCone F hF (x t) y hy hnear ha
    obtain ⟨v, hv, hwv⟩ := hK (x t) y w hw
    have hvu : inner ℝ v (‖x t - y‖⁻¹ • (x t - y)) ≤ 0 := htan y hy hv _ hu
    rw [inner_smul_right] at hvu
    have hinvpos : 0 < ‖x t - y‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr ha)
    have hva : inner ℝ v (x t - y) ≤ 0 := by
      by_contra hc; rw [not_le] at hc; nlinarith
    have hg1 : HasDerivAt (fun s => ‖x s - y‖ ^ 2) (2 * inner ℝ (x t - y) w) t :=
      (hxw.sub_const y).norm_sq
    have hg2 : HasDerivAt (fun s => Metric.infDist (x s) F ^ 2)
        (2 * Metric.infDist (x t) F * d) t := by
      have := hd.pow 2
      rw [show 2 * Metric.infDist (x t) F * d
          = ((2 : ℕ) : ℝ) * Metric.infDist (x t) F ^ (2 - 1) * d by norm_num <;> ring]
      exact this
    have hmin : IsLocalMin (fun s => ‖x s - y‖ ^ 2 - Metric.infDist (x s) F ^ 2) t :=
      Eventually.of_forall (fun s => by
        show ‖x t - y‖ ^ 2 - Metric.infDist (x t) F ^ 2 ≤ ‖x s - y‖ ^ 2 - Metric.infDist (x s) F ^ 2
        have h1 : Metric.infDist (x s) F ≤ ‖x s - y‖ := by
          rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hy
        have h2 := pow_le_pow_left₀ Metric.infDist_nonneg h1 2
        rw [hyd]; linarith)
    have hder := hmin.hasDerivAt_eq_zero (hg1.sub hg2)
    have hcs : inner ℝ (x t - y) (w - v) ≤ ‖x t - y‖ * ‖w - v‖ := real_inner_le_norm _ _
    rw [inner_sub_right, real_inner_comm v (x t - y)] at hcs
    have hk2 : ‖x t - y‖ * ‖w - v‖ ≤ ‖x t - y‖ * (K * ‖x t - y‖) :=
      mul_le_mul_of_nonneg_left hwv (norm_nonneg _)
    rw [hyd] at hder hpos ⊢
    have hm : ‖x t - y‖ * d ≤ ‖x t - y‖ * (K * ‖x t - y‖) := by nlinarith
    exact le_of_mul_le_mul_left hm hpos
