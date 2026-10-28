-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_exists_secondOrder_expansion_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:07.240572+00:00
-- url     : https://prove2.me/submissions/7283f611-c19c-4e14-8ebe-7d861253f83a

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder
import Theorems.Thm_FunctionalInequalities_Analysis_eventually_abs_sub_quadratic_le_of_subgradient_expansion_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_subgradient_slope_le_inner_add_readable
import Theorems.Thm_FunctionalInequalities_Analysis_inner_hasFDerivAt_resolvent_symm_readable
import Theorems.Thm_FunctionalInequalities_Analysis_lipschitzWith_proximalPoint_readable
import Theorems.Thm_FunctionalInequalities_Analysis_subgradient_expansion_of_hasFDerivAt_resolvent_readable
import Theorems.Thm_FunctionalInequalities_Analysis_volume_image_eq_zero_of_lipschitzOnWith_readable

section
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
/-- Uniqueness: if `z − x` is a subgradient of `f` at `x`, then `x` is the proximal point of `z`. -/
theorem FunctionalInequalities.Analysis.proximalPoint_eq_of_subgradient {f : E → ℝ} (hconv : ConvexOn ℝ univ f) {x z : E}
    (hx : ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y) : proximalPoint f z = x := by
  have h := proximal_subgradient_monotonicity (proximalPoint_spec hconv z) hx
  simp only [sub_self, inner_zero_right] at h
  have hn : ‖proximalPoint f z - x‖ = 0 := by
    nlinarith [norm_nonneg (proximalPoint f z - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
end FiniteDimensional
end InnerProduct
end LT12D2ProximalPoint
end
end

noncomputable section
open Set Filter
open scoped RealInnerProductSpace Topology
section LT12D6AlexandrovTheorem
open MeasureTheory Set Filter
/-- **Alexandrov's theorem** (A. D. Alexandrov 1939; Evans–Gariepy, *Measure theory and fine properties of
functions*, Thm 6.9; weak Letwin route): a convex function on a finite-dimensional real inner
product space has, at almost every point, a unique subgradient `p` and a second-order expansion
`f y = f x + ⟪p, y − x⟫ + ½ ⟪B (y − x), y − x⟫ + o(‖y − x‖²)` with a symmetric `B`. -/
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂(volume : Measure E), ∃ p : E, ∃ B : E →L[ℝ] E,
      (∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫) ∧
      (∀ q : E, (∀ y, f x + ⟪q, y - x⟫ ≤ f y) → q = p) ∧
      ∀ ε > 0, ∀ᶠ y in 𝓝 x,
        |f y - f x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by
  classical
  let P : E → E := FunctionalInequalities.Analysis.proximalPoint f
  have hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y :=
    FunctionalInequalities.Analysis.proximalPoint_spec hconv
  have hLip : LipschitzWith 1 P := FunctionalInequalities.Analysis.lipschitzWith_proximalPoint_readable hconv
  let N₁ : Set E := {z | ¬ DifferentiableAt ℝ P z}
  let N₂ : Set E :=
    {z | DifferentiableAt ℝ P z ∧ (fderiv ℝ P z).det = 0}
  have hN₁ : (volume : Measure E) N₁ = 0 :=
    ae_iff.mp (hLip.ae_differentiableAt (μ := (volume : Measure E)))
  have hImage₁ : (volume : Measure E) (P '' N₁) = 0 :=
    FunctionalInequalities.Analysis.volume_image_eq_zero_of_lipschitzOnWith_readable hLip.lipschitzOnWith hN₁
  have hImage₂ : (volume : Measure E) (P '' N₂) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (volume : Measure E) (f' := fun z => fderiv ℝ P z)
    · intro z hz
      exact hz.1.hasFDerivAt.hasFDerivWithinAt
    · intro z hz
      exact hz.2
  let Bad : Set E := P '' N₁ ∪ P '' N₂
  have hBad : (volume : Measure E) Bad = 0 :=
    measure_union_null hImage₁ hImage₂
  have hGood : ∀ᵐ x ∂(volume : Measure E), x ∉ Bad := by
    rw [ae_iff]
    exact measure_mono_null (fun a ha => not_not.mp ha) hBad
  filter_upwards [hGood] with x hx
  have hx₁ : x ∉ P '' N₁ := fun h => hx (Or.inl h)
  have hx₂ : x ∉ P '' N₂ := fun h => hx (Or.inr h)
  obtain ⟨p₁, hp₁, _⟩ := FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_readable hconv x 0
  let z : E := x + p₁
  have hzsub : z - x = p₁ := by
    simp only [z, add_sub_cancel_left]
  have hPz : P z = x := by
    apply FunctionalInequalities.Analysis.proximalPoint_eq_of_subgradient hconv
    simpa only [hzsub] using hp₁
  have hDiff : DifferentiableAt ℝ P z := by
    by_contra h
    exact hx₁ ⟨z, h, hPz⟩
  have hDet : (fderiv ℝ P z).det ≠ 0 := by
    intro h
    exact hx₂ ⟨z, ⟨hDiff, h⟩, hPz⟩
  let T : E ≃L[ℝ] E :=
    (LinearMap.equivOfDetNeZero (fderiv ℝ P z : E →ₗ[ℝ] E) hDet).toContinuousLinearEquiv
  have hTcoe : (T : E →L[ℝ] E) = fderiv ℝ P z := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have hT : HasFDerivAt P (T : E →L[ℝ] E) z := by
    rw [hTcoe]
    exact hDiff.hasFDerivAt
  have hInvSymm : ∀ v w, ⟪T.symm v, w⟫ = ⟪v, T.symm w⟫ := by
    intro v w
    have h := (FunctionalInequalities.Analysis.inner_hasFDerivAt_resolvent_symm_readable hP hT (T.symm v) (T.symm w)).1
    change ⟪T (T.symm v), T.symm w⟫ = ⟪T.symm v, T (T.symm w)⟫ at h
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm
  let B : E →L[ℝ] E :=
    (T.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E
  have hBsymm : ∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫ := by
    intro v w
    change ⟪T.symm v - v, w⟫ = ⟪v, T.symm w - w⟫
    rw [inner_sub_left, inner_sub_right, hInvSymm v w]
  have hExpansion := FunctionalInequalities.Analysis.subgradient_expansion_of_hasFDerivAt_resolvent_readable hP hT
  rw [hPz] at hExpansion
  refine ⟨z - x, B, hBsymm, hExpansion.1, ?_⟩
  apply FunctionalInequalities.Analysis.eventually_abs_sub_quadratic_le_of_subgradient_expansion_readable hconv
  intro ε hε
  filter_upwards [hExpansion.2 ε hε] with y hy
  intro q hq
  change ‖q - (z - x) - (T.symm (y - x) - (y - x))‖ ≤ ε * ‖y - x‖
  exact hy q hq
