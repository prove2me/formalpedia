-- Prove2me | solution 1 for FunctionalInequalities.Analysis.lipschitzWith_proximalPoint_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:47.255419+00:00
-- url     : https://prove2.me/submissions/2771af35-471d-4f76-9146-e15a27e8c0f5

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Proximal
import Theorems.Thm_FunctionalInequalities_Analysis_exists_subgradient_slope_le_inner_add_readable

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT12D2ProximalPoint
open Set
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem FunctionalInequalities.Analysis.proximal_subgradient_monotonicity
    {f : E → ℝ} {x x' z w : E}
    (hx : ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y)
    (hx' : ∀ y, f x' + ⟪w - x', y - x'⟫ ≤ f y) :
    ‖x - x'‖ ^ 2 ≤ ⟪x - x', z - w⟫ := by
  have h₁ : f x - ⟪z - x, x - x'⟫ ≤ f x' := by
    simpa only [← neg_sub x x', inner_neg_right, sub_eq_add_neg] using hx x'
  have h₂ := hx' x
  have hm : 0 ≤ ⟪(z - x) - (w - x'), x - x'⟫ := by
    rw [inner_sub_left]
    linarith
  have he : (z - x) - (w - x') = (z - w) - (x - x') := by
    abel
  rw [he, inner_sub_left, real_inner_self_eq_norm_sq] at hm
  have hc := real_inner_comm (x - x') (z - w)
  linarith
set_option maxHeartbeats 800000 in
private theorem FunctionalInequalities.Analysis.exists_proximal_minimizer
    [FiniteDimensional ℝ E] {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) (z : E) :
    ∃ x, ∀ y,
      f x + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 ≤
        f y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2 := by
  let φ : E → ℝ := fun x => f x + (1 / 2 : ℝ) * ‖x - z‖ ^ 2
  have hf : Continuous f :=
    continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hφ : Continuous φ :=
    hf.add (((continuous_id.sub continuous_const).norm.pow 2).const_mul (1 / 2 : ℝ))
  obtain ⟨g, hg, _⟩ := exists_subgradient_slope_le_inner_add_readable hconv z (0 : E)
  let R : ℝ := 2 * ‖g‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  obtain ⟨x, _, hx⟩ :=
    (isCompact_closedBall z R).exists_isMinOn
      ⟨z, Metric.mem_closedBall_self hR⟩ hφ.continuousOn
  refine ⟨x, ?_⟩
  intro y
  by_cases hy : y ∈ Metric.closedBall z R
  · exact (isMinOn_iff.mp hx) y hy
  · have hr : 2 * ‖g‖ + 1 < ‖y - z‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, not_le, R] using hy
    have hr0 : 0 < ‖y - z‖ := by
      linarith [norm_nonneg g]
    have hprod :=
      mul_pos hr0 (show 0 < ‖y - z‖ - 2 * ‖g‖ by linarith)
    have hi := neg_le_of_abs_le (abs_real_inner_le_norm g (y - z))
    have ha := hg y
    have hxz := (isMinOn_iff.mp hx) z (Metric.mem_closedBall_self hR)
    dsimp [φ] at hxz ⊢
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero] at hxz
    nlinarith
set_option maxHeartbeats 800000 in
private theorem FunctionalInequalities.Analysis.subgradient_of_proximal_minimizer
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) {x z : E}
    (hx : ∀ y,
      f x + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 ≤
        f y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2) :
    ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y := by
  intro y
  have ht : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2 := by
    intro t ht ht1
    have he : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    have hf := hconv.2 (mem_univ x) (mem_univ y)
      (sub_nonneg.mpr ht1) ht.le (show 1 - t + t = 1 by ring)
    rw [he] at hf
    simp only [smul_eq_mul] at hf
    have hm := hx (x + t • (y - x))
    have he' : x + t • (y - x) - z = (x - z) + t • (y - x) := by
      abel
    rw [he', norm_add_sq_real, inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht] at hm
    have hmul :
        0 ≤ t * (f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2) := by
      nlinarith
    exact nonneg_of_mul_nonneg_right hmul ht
  have hcont : Continuous
      (fun t : ℝ => f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2) :=
    continuous_const.add ((continuous_id.div_const 2).mul continuous_const)
  have hev : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      0 ≤ f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2 := by
    have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), 0 < t :=
      self_mem_nhdsWithin
    have hsmall : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
    exact (hpos.and hsmall).mono (fun t h => ht t h.1 h.2.le)
  have hlim : 0 ≤ f y - f x + ⟪x - z, y - x⟫ := by
    simpa only [zero_div, zero_mul, add_zero] using
      ge_of_tendsto ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds) hev
  have hi : ⟪z - x, y - x⟫ = -⟪x - z, y - x⟫ := by
    rw [← neg_sub x z, inner_neg_left]
  rw [hi]
  linarith
section FiniteDimensional
variable [FiniteDimensional ℝ E]
/-- `z − proximalPoint f z` is a subgradient of the convex `f` at `proximalPoint f z`. -/
theorem FunctionalInequalities.Analysis.proximalPoint_spec {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (z : E) :
    ∀ y, f (proximalPoint f z) + ⟪z - proximalPoint f z, y - proximalPoint f z⟫ ≤ f y := by
  obtain ⟨x, hx⟩ := exists_proximal_minimizer hconv z
  exact Classical.epsilon_spec
    (p := fun x : E => ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y)
    ⟨x, subgradient_of_proximal_minimizer hconv hx⟩
/-- Firm nonexpansiveness of the proximal map. -/
theorem FunctionalInequalities.Analysis.sq_norm_proximalPoint_sub_le_inner {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (z w : E) :
    ‖proximalPoint f z - proximalPoint f w‖ ^ 2 ≤
      ⟪proximalPoint f z - proximalPoint f w, z - w⟫ := by
  exact proximal_subgradient_monotonicity
    (proximalPoint_spec hconv z) (proximalPoint_spec hconv w)
/-- The proximal map is `1`-Lipschitz. -/
theorem solution {f : E → ℝ} (hconv : ConvexOn ℝ univ f) :
    LipschitzWith 1 (FunctionalInequalities.Analysis.proximalPoint f) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h := FunctionalInequalities.Analysis.sq_norm_proximalPoint_sub_le_inner hconv z w
  have hi := real_inner_le_norm (FunctionalInequalities.Analysis.proximalPoint f z - FunctionalInequalities.Analysis.proximalPoint f w) (z - w)
  have hb : ‖FunctionalInequalities.Analysis.proximalPoint f z - FunctionalInequalities.Analysis.proximalPoint f w‖ ^ 2 ≤
      ‖FunctionalInequalities.Analysis.proximalPoint f z - FunctionalInequalities.Analysis.proximalPoint f w‖ * ‖z - w‖ :=
    h.trans hi
  by_contra hn
  have hlt : ‖z - w‖ < ‖FunctionalInequalities.Analysis.proximalPoint f z - FunctionalInequalities.Analysis.proximalPoint f w‖ :=
    lt_of_not_ge hn
  have hp : 0 < ‖FunctionalInequalities.Analysis.proximalPoint f z - FunctionalInequalities.Analysis.proximalPoint f w‖ :=
    lt_of_le_of_lt (norm_nonneg _) hlt
  have hm := mul_pos hp (sub_pos.mpr hlt)
  nlinarith
