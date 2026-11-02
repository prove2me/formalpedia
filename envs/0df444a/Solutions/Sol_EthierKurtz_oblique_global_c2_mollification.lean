-- Prove2me | solution 1 for EthierKurtz.oblique_global_c2_mollification
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T05:36:54.763162+00:00
-- url     : https://prove2.me/submissions/dab985e4-1a9c-47ca-985b-8d8b6590dfcb

import Mathlib
import Definitions.Def_EthierKurtz_ComponentHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal

section E1a

/-! D2 library (relay 7): EthierKurtz.oblique_graph_exponent_closure. E1a: cone condition from an outward normal. -/

set_option autoImplicit false

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz.D2

lemma sum_mul_le_norm {d : ℕ} (v w : EuclideanSpace ℝ (Fin d)) :
    ∑ i, v i * w i ≤ ‖v‖ * ‖w‖ := by
  have h := real_inner_le_norm v w
  have e : inner ℝ v w = ∑ i, v i * w i := by
    simp [PiLp.inner_apply, mul_comm]
  linarith [e ▸ h]

lemma sum_mul_self {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    ∑ i, v i * v i = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [sq]

/-- E1a. Cone condition at a boundary point with an outward unit normal: points of the closure near `x₀`, pushed
inward by `3 t` along the normal, carry a ball of radius `t` inside `Ω`. -/
lemma cone_of_outward {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {x₀ v : EuclideanSpace ℝ (Fin d)}
    (h : IsOutwardUnitNormal Ω x₀ v) :
    ∃ r₀ t₀ : ℝ, 0 < r₀ ∧ 0 < t₀ ∧ ∀ x ∈ closure Ω, dist x x₀ < r₀ → ∀ t : ℝ, 0 < t → t ≤ t₀ →
      Metric.ball (x - (3 * t) • v) t ⊆ Ω := by
  obtain ⟨_, hv, V, hV, hx₀V, r, s, hs, hr, hr0, hΩ, hD⟩ := h
  obtain ⟨R₁, hR₁, hball⟩ := Metric.isOpen_iff.1 hV x₀ hx₀V
  have hcont : ContinuousOn (fderiv ℝ r) V :=
    hr.continuousOn_fderiv_of_isOpen hV le_rfl
  have hcx : ContinuousAt (fderiv ℝ r) x₀ := hcont.continuousAt (hV.mem_nhds hx₀V)
  obtain ⟨R₂, hR₂, hR₂b⟩ := Metric.continuousAt_iff.1 hcx (s / 10) (by positivity)
  set R := min R₁ R₂ with hRdef
  have hR : 0 < R := lt_min hR₁ hR₂
  have hBV : Metric.ball x₀ R ⊆ V := fun y hy => hball (Metric.ball_subset_ball (min_le_left _ _) hy)
  have hdiff : ∀ y ∈ Metric.ball x₀ R, DifferentiableAt ℝ r y := fun y hy =>
    (hr.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds (hBV hy))
  -- g = r - Dr(x₀) has small derivative on the ball
  set L := fderiv ℝ r x₀ with hL
  have hg : ∀ y ∈ Metric.ball x₀ R, ‖fderiv ℝ (fun z => r z - L z) y‖ ≤ s / 10 := by
    intro y hy
    rw [fderiv_fun_sub (hdiff y hy) L.differentiableAt, L.fderiv]
    have := hR₂b (show dist y x₀ < R₂ from lt_of_lt_of_le hy (min_le_right _ _))
    rw [dist_eq_norm] at this
    exact this.le
  have hgd : ∀ y ∈ Metric.ball x₀ R, DifferentiableAt ℝ (fun z => r z - L z) y := fun y hy =>
    (hdiff y hy).sub L.differentiableAt
  -- r ≤ 0 on the closure near x₀
  have hcl : ∀ x ∈ closure Ω, x ∈ Metric.ball x₀ R → r x ≤ 0 := by
    intro x hx hxB
    have hrc : ContinuousAt r x := (hdiff x hxB).continuousAt
    by_contra hpos
    push Not at hpos
    have hev : ∀ᶠ y in 𝓝 x, 0 < r y ∧ y ∈ Metric.ball x₀ R :=
      (hrc.eventually (lt_mem_nhds hpos)).and (Metric.isOpen_ball.mem_nhds hxB)
    obtain ⟨y, ⟨hy1, hy2⟩, hyΩ⟩ := (mem_closure_iff_nhds.1 hx) _ hev
    have := (hΩ y (hBV hy2)).1 hyΩ
    linarith
  refine ⟨R / 2, R / 8, by positivity, by positivity, ?_⟩
  intro x hx hxd t ht htle y hy
  have hxB : x ∈ Metric.ball x₀ R := by
    rw [Metric.mem_ball]; linarith
  have hyx : ‖y - x‖ ≤ 4 * t := by
    have h1 : ‖y - (x - (3 * t) • v)‖ < t := by rw [← dist_eq_norm]; exact hy
    have h2 : y - x = (y - (x - (3 * t) • v)) - (3 * t) • v := by abel
    rw [h2]
    calc ‖(y - (x - (3 * t) • v)) - (3 * t) • v‖ ≤ ‖y - (x - (3 * t) • v)‖ + ‖(3 * t) • v‖ := norm_sub_le _ _
      _ ≤ t + 3 * t := by
          rw [norm_smul, hv, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
      _ = 4 * t := by ring
  have hyB : y ∈ Metric.ball x₀ R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ‖x - x₀‖ < R / 2 := by rw [← dist_eq_norm]; exact hxd
    calc ‖y - x₀‖ = ‖(y - x) + (x - x₀)‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖x - x₀‖ := norm_add_le _ _
      _ < R := by linarith
  have hmvt := (convex_ball x₀ R).norm_image_sub_le_of_norm_fderiv_le hgd hg hxB hyB
  -- L (y - x) ≤ -2 t s
  have hLyx : L (y - x) ≤ -(2 * t * s) := by
    rw [hD]
    set w := y - (x - (3 * t) • v) with hw
    have hwn : ‖w‖ < t := by rw [hw, ← dist_eq_norm]; exact hy
    have e : y - x = w - (3 * t) • v := by rw [hw]; abel
    rw [e]
    have hsum : ∑ i, v i * (w - (3 * t) • v) i = ∑ i, v i * w i - 3 * t * ∑ i, v i * v i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hsum, sum_mul_self, hv]
    have hc := sum_mul_le_norm v w
    rw [hv] at hc
    have : s * (∑ i, v i * w i) ≤ s * t := by
      apply mul_le_mul_of_nonneg_left _ hs.le; linarith
    nlinarith
  have hrx := hcl x hx hxB
  have key : r y - r x ≤ L (y - x) + s / 10 * ‖y - x‖ := by
    have h3 : r y - r x - L (y - x) ≤ ‖(r y - L y) - (r x - L x)‖ := by
      rw [map_sub]
      have : r y - r x - (L y - L x) = (r y - L y) - (r x - L x) := by ring
      rw [this]; exact le_abs_self _
    linarith
  have hry : r y < 0 := by
    have : s / 10 * ‖y - x‖ ≤ s / 10 * (4 * t) := mul_le_mul_of_nonneg_left hyx (by positivity)
    nlinarith
  exact (hΩ y (hBV hyB)).2 hry

end EthierKurtz.D2

end E1a

section E1

/-! D2 library, E1 (relay 8): local C^2 mollification up to the boundary along an inward cone. -/

set_option autoImplicit false

open Filter Set Metric MeasureTheory ContinuousLinearMap
open scoped Topology Convolution Manifold

namespace EthierKurtz.D2E1

variable {d : ℕ}

/-- Smooth cutoff equal to one on a thickening of a compact set inside an open set. -/
lemma cutoff {K U : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ, ∃ δ : ℝ, 0 < δ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∀ y ∈ thickening δ K, χ y = 1 := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hd : Disjoint (thickening δ K)ᶜ (closure (thickening (δ / 2) K)) := by
    rw [disjoint_compl_left_iff_subset]
    exact (closure_thickening_subset_cthickening _ _).trans
      (cthickening_subset_thickening' hδ (by linarith) K)
  obtain ⟨χ, hχ, -, h0, h1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d))) (n := (⊤ : ℕ∞))
    isOpen_thickening.isClosed_compl isClosed_closure hd
  have hsupp : Function.support χ ⊆ thickening δ K := by
    intro y hy
    by_contra h
    exact hy ((h0 y).1 h)
  have hts : tsupport χ ⊆ cthickening δ K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening _ _)
  refine ⟨χ, δ / 2, by positivity, contMDiff_iff_contDiff.1 hχ,
    (hK.cthickening).of_isClosed_subset (isClosed_tsupport χ) hts,
    hts.trans hsub, fun y hy => (h1 y).1 (subset_closure hy)⟩

/-- The convolution with `(lsmul ℝ ℝ).precompR` is the convolution with `lsmul ℝ ℝ` (CLM-valued). -/
lemma conv_precompR (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) :
    (φ ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin d)), volume] G) =
      (φ ⋆[lsmul ℝ ℝ, volume] G) := by
  funext x
  simp only [convolution]
  congr 1

/-- Directional derivative of a convolution falls on the compactly supported `C¹` factor. -/
lemma conv_partial {φ g : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : LocallyIntegrable φ volume)
    (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (e : EuclideanSpace ℝ (Fin d)) :
    (fun x => fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] g) x e) =
      (φ ⋆[lsmul ℝ ℝ, volume] (fun y => fderiv ℝ g y e)) := by
  funext x
  rw [(hcg.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hφ hg x).fderiv]
  exact convolution_precompR_apply (lsmul ℝ ℝ) hφ (hcg.fderiv (𝕜 := ℝ)) (hg.continuous_fderiv one_ne_zero) x e

/-- Full derivative of a convolution. -/
lemma conv_fderiv {φ g : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : LocallyIntegrable φ volume)
    (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (x : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] g) x = (φ ⋆[lsmul ℝ ℝ, volume] (fderiv ℝ g)) x := by
  rw [(hcg.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hφ hg x).fderiv, conv_precompR]

/-- Segments from a point to the pushed ball stay inside `Ω` (cone condition). -/
lemma seg_sub {Ω : Set (EuclideanSpace ℝ (Fin d))} {x₀ v x y : EuclideanSpace ℝ (Fin d)} {r₀ t₀ ε : ℝ}
    (hcone : ∀ x ∈ closure Ω, dist x x₀ < r₀ → ∀ t : ℝ, 0 < t → t ≤ t₀ →
      Metric.ball (x - (3 * t) • v) t ⊆ Ω)
    (hx : x ∈ Ω) (hxd : dist x x₀ < r₀) (hε : 0 < ε) (hεt : ε ≤ t₀)
    (hy : y ∈ Metric.ball (x - (3 * ε) • v) ε) : segment ℝ x y ⊆ Ω := by
  rw [segment_eq_image']
  rintro p ⟨s, ⟨hs0, hs1⟩, rfl⟩
  rcases hs0.eq_or_lt with h | h
  · subst h; simpa using hx
  · refine hcone x (subset_closure hx) hxd (s * ε) (by positivity)
      (by nlinarith) ?_
    rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
    have e : x + s • (y - x) - (x - (3 * (s * ε)) • v) = s • (y - (x - (3 * ε) • v)) := by
      simp only [smul_sub, smul_smul]; module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos h]
    exact mul_lt_mul_of_pos_left hy h

/-- Choice of the mollification scale. -/
lemma scale_choice {μ t₀ δ₁ η C₁ : ℝ} (hμ : 0 < μ) (ht₀ : 0 < t₀) (hδ₁ : 0 < δ₁) (hη : 0 < η)
    {ι : Type} [Finite ι] (ρ₀ M : ι → ℝ) (hρ₀ : ∀ k, 0 < ρ₀ k) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ t₀ ∧ |C₁| * (4 * ε) ≤ η ∧ 4 * ε < δ₁ ∧
      ∀ k, 5 * ε ≤ ρ₀ k ∧ M k * (5 * ε) ^ μ ≤ η := by
  have hA : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hcont : ∀ (h : ℝ → ℝ) (b : ℝ), ContinuousAt h 0 → h 0 < b → ∀ᶠ ε in 𝓝[>] (0 : ℝ), h ε < b :=
    fun h b hh hb => (hh.eventually (eventually_lt_nhds hb)).filter_mono nhdsWithin_le_nhds
  have h1 := hcont (fun ε => ε) t₀ continuousAt_id ht₀
  have h2 := hcont (fun ε => |C₁| * (4 * ε)) η (by fun_prop) (by simpa using hη)
  have h3 := hcont (fun ε => 4 * ε) δ₁ (by fun_prop) (by simpa using hδ₁)
  have h4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k, 5 * ε < ρ₀ k ∧ M k * (5 * ε) ^ μ < η := by
    rw [Filter.eventually_all]
    intro k
    refine (hcont (fun ε => 5 * ε) (ρ₀ k) (by fun_prop) (by simpa using hρ₀ k)).and
      (hcont (fun ε => M k * (5 * ε) ^ μ) η ?_ ?_)
    · exact continuousAt_const.mul
        ((continuousAt_const.mul continuousAt_id).rpow_const (Or.inr hμ.le))
    · simp [Real.zero_rpow hμ.ne', hη]
  obtain ⟨ε, hε, e1, e2, e3, e4⟩ := (hA.and (h1.and (h2.and (h3.and h4)))).exists
  exact ⟨ε, hε, e1.le, e2.le, e3, fun k => ⟨(e4 k).1.le, (e4 k).2.le⟩⟩

/-- E1. Local `C²` mollification up to the boundary along an inward cone. -/
lemma local_mollify {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {x₀ v : EuclideanSpace ℝ (Fin d)} {r₀ t₀ μ : ℝ} (hr₀ : 0 < r₀) (ht₀ : 0 < t₀) (hv : ‖v‖ ≤ 1)
    (hμ : 0 < μ)
    (hcone : ∀ x ∈ closure Ω, dist x x₀ < r₀ → ∀ t : ℝ, 0 < t → t ≤ t₀ →
      Metric.ball (x - (3 * t) • v) t ⊆ Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiffOn ℝ 2 f Ω) {C₁ : ℝ}
    (hC₁ : ∀ y ∈ Ω, ‖fderiv ℝ f y‖ ≤ C₁)
    (hUC : ∀ η > 0, ∃ δ > 0, ∀ y ∈ Ω, ∀ z ∈ Ω, dist y z < δ →
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ η)
    (hH : ∀ i j, ComponentHolder Ω μ (fun x => fderiv ℝ (fun y => fderiv ℝ f y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)))
    (η : ℝ) (hη : 0 < η) :
    ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
      ∀ x ∈ Ω, dist x x₀ < r₀ / 2 →
        |F x - f x| ≤ η ∧ ‖fderiv ℝ F x - fderiv ℝ f x‖ ≤ η ∧
        ∀ i j, |fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1) -
          fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)| ≤ η := by
  classical
  choose ρ₀ M hρ₀ hM hHol using fun k : Fin d × Fin d => (hH k.1 k.2).2
  obtain ⟨δ₁, hδ₁, hUC'⟩ := hUC η hη
  obtain ⟨ε, hε, hεt, hεC, hεδ, hεk⟩ := scale_choice (C₁ := C₁) hμ ht₀ hδ₁ hη ρ₀ M hρ₀
  set s : EuclideanSpace ℝ (Fin d) := (3 * ε) • v with hs
  have hsn : ‖s‖ ≤ 3 * ε := by
    rw [hs, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith [norm_nonneg v]
  set K : Set (EuclideanSpace ℝ (Fin d)) :=
    (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 - s + p.2) ''
      ((closedBall x₀ (r₀ / 2) ∩ closure Ω) ×ˢ closedBall 0 (ε / 2)) with hKdef
  have hK : IsCompact K :=
    (((isCompact_closedBall x₀ (r₀ / 2)).inter_right isClosed_closure).prod
      (isCompact_closedBall 0 (ε / 2))).image (by fun_prop)
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨⟨x, w⟩, ⟨⟨hx1, hx2⟩, hw⟩, rfl⟩
    refine hcone x hx2 (lt_of_le_of_lt (mem_closedBall.1 hx1) (by linarith)) ε hε hεt ?_
    rw [mem_ball, dist_eq_norm]
    have : ‖w‖ ≤ ε / 2 := mem_closedBall_zero_iff.1 hw
    have e : x - s + w - (x - (3 * ε) • v) = w := by rw [hs]; abel
    rw [e]
    linarith
  obtain ⟨χ, δ, hδ, hχs, hχc, hχU, hχ1⟩ := cutoff hK hΩ hKΩ
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun y => χ y * f y with hgdef
  have hg2 : ContDiff ℝ 2 g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Ω
    · exact (hχs.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.mul (hf.contDiffAt (hΩ.mem_nhds hy))
    · have h0 : χ =ᶠ[𝓝 y] 0 := (notMem_tsupport_iff_eventuallyEq).1 (fun h => hy (hχU h))
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (h0.mono fun z hz => by simp only [hgdef, hz, Pi.zero_apply, zero_mul])
  have hgc : HasCompactSupport g := hχc.mul_right
  have heq : ∀ y ∈ thickening δ K, g =ᶠ[𝓝 y] f := fun y hy =>
    Filter.eventually_of_mem (isOpen_thickening.mem_nhds hy) fun z hz => by simp [hgdef, hχ1 z hz]
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hφli : LocallyIntegrable (φ.normed volume) volume := φ.integrable_normed.locallyIntegrable
  have hφsupp : Function.support (φ.normed volume) ⊆ ball 0 (ε / 2) := φ.support_normed_eq.le
  refine ⟨fun x => (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) (x - s), ?_, ?_⟩
  · exact (φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (n := ⊤) φ.contDiff_normed hg2.continuous.locallyIntegrable).comp
      (contDiff_id.sub contDiff_const)
  intro x hx hxd
  -- geometry of the integration ball
  have hyK : ∀ y ∈ ball (x - s) (ε / 2), y ∈ thickening δ K := by
    intro y hy
    refine self_subset_thickening hδ K ⟨(x, y - (x - s)), ⟨⟨mem_closedBall.2 hxd.le,
      subset_closure hx⟩, ?_⟩, by simp only; abel⟩
    rw [mem_closedBall_zero_iff, ← dist_eq_norm]
    exact (mem_ball.1 hy).le
  have hyseg : ∀ y ∈ ball (x - s) (ε / 2), segment ℝ x y ⊆ Ω := fun y hy =>
    seg_sub hcone hx (by linarith) hε hεt (ball_subset_ball (by linarith) hy)
  have hyx : ∀ y ∈ ball (x - s) (ε / 2), ‖y - x‖ < 4 * ε := by
    intro y hy
    have h1 : ‖y - (x - s)‖ < ε / 2 := by rw [← dist_eq_norm]; exact hy
    have e : y - x = (y - (x - s)) - s := by abel
    rw [e]
    calc ‖(y - (x - s)) - s‖ ≤ ‖y - (x - s)‖ + ‖s‖ := norm_sub_le _ _
      _ < 4 * ε := by linarith
  have hdiff : ∀ z ∈ Ω, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn two_ne_zero).differentiableAt (hΩ.mem_nhds hz)
  refine ⟨?_, ?_, ?_⟩
  · -- values
    rw [← Real.dist_eq]
    refine dist_convolution_le hη.le hφsupp φ.nonneg_normed φ.integral_normed
      hg2.continuous.aestronglyMeasurable (fun y hy => ?_)
    have hgy : g y = f y := (heq y (hyK y hy)).eq_of_nhds
    rw [hgy, Real.dist_eq, ← Real.norm_eq_abs]
    have hseg := hyseg y hy
    have hmvt := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => hdiff z (hseg hz)) (fun z hz => hC₁ z (hseg hz))
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    have h4 := hyx y hy
    calc ‖f y - f x‖ ≤ C₁ * ‖y - x‖ := hmvt
      _ ≤ |C₁| * ‖y - x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |C₁| * (4 * ε) := mul_le_mul_of_nonneg_left h4.le (abs_nonneg _)
      _ ≤ η := hεC
  · -- first derivatives
    rw [fderiv_comp_sub, conv_fderiv hφli hgc (hg2.of_le (by norm_num)), ← dist_eq_norm]
    refine dist_convolution_le hη.le hφsupp φ.nonneg_normed φ.integral_normed
      (hg2.continuous_fderiv two_ne_zero).aestronglyMeasurable (fun y hy => ?_)
    rw [(heq y (hyK y hy)).fderiv_eq, dist_eq_norm]
    refine hUC' y (hyseg y hy (right_mem_segment ℝ x y)) x hx ?_
    rw [dist_eq_norm]; linarith [hyx y hy]
  · -- second partials
    intro i j
    set ej : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single j 1
    set ei : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
    set gj : EuclideanSpace ℝ (Fin d) → ℝ := fun y => fderiv ℝ g y ej with hgj
    have hgj1 : ContDiff ℝ 1 gj :=
      (hg2.fderiv_right (m := 1) (le_of_eq one_add_one_eq_two)).clm_apply contDiff_const
    have hgjc : HasCompactSupport gj := by
      refine (hgc.fderiv (𝕜 := ℝ)).mono' ?_
      intro y hy
      apply subset_tsupport
      intro h
      apply hy
      simp [hgj, h]
    have e1 : (fun y => fderiv ℝ (fun x => (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) (x - s)) y ej) =
        fun y => (φ.normed volume ⋆[lsmul ℝ ℝ, volume] gj) (y - s) := by
      funext y
      rw [fderiv_comp_sub]
      exact congrFun (conv_partial hφli hgc (hg2.of_le (by norm_num)) ej) (y - s)
    rw [e1, fderiv_comp_sub]
    rw [show fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] gj) (x - s) ei =
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (fun y => fderiv ℝ gj y ei)) (x - s) from
        congrFun (conv_partial hφli hgjc hgj1 ei) (x - s)]
    rw [← Real.dist_eq]
    refine dist_convolution_le hη.le hφsupp φ.nonneg_normed φ.integral_normed
      ((hgj1.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
      (fun y hy => ?_)
    have hgjeq : gj =ᶠ[𝓝 y] (fun z => fderiv ℝ f z ej) :=
      Filter.eventually_of_mem (isOpen_thickening.mem_nhds (hyK y hy)) fun z hz => by
        simp only [hgj, (heq z hz).fderiv_eq]
    rw [hgjeq.fderiv_eq, Real.dist_eq]
    have hseg := hyseg y hy
    have h5 : 5 * ε ≤ ρ₀ (i, j) := (hεk (i, j)).1
    have hball : segment ℝ x y ⊆ Ω ∩ ball x (5 * ε) := by
      refine subset_inter hseg ((convex_ball x (5 * ε)).segment_subset (mem_ball_self (by positivity)) ?_)
      rw [mem_ball, dist_eq_norm]; linarith [hyx y hy]
    have hcomp := (convex_segment x y).isPreconnected.subset_connectedComponentIn
      (left_mem_segment ℝ x y) hball
    have := hHol (i, j) (5 * ε) (by positivity) h5 x x ⟨hx, mem_ball_self (by positivity)⟩
      y (hcomp (right_mem_segment ℝ x y)) x (hcomp (left_mem_segment ℝ x y))
    exact this.trans (hεk (i, j)).2

end EthierKurtz.D2E1

end E1

section E1G

/-! D2 library, E1' (relay 10): global C^2 mollification on a bounded open set with outward normals.
Uses E1 `EthierKurtz.D2E1.local_mollify` and E1a `EthierKurtz.D2.cone_of_outward` above. -/

set_option autoImplicit false

open Filter Set Metric
open scoped Topology Manifold ContDiff

namespace EthierKurtz.E1G

variable {d : ℕ}

lemma clm_expand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] F) (a : EuclideanSpace ℝ (Fin d)) :
    L a = ∑ i, a i • L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr a]
  simp [map_sum, map_smul]

lemma opNorm_le_sum_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] F) :
    ‖L‖ ≤ ∑ i, ‖L (EuclideanSpace.single i 1)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) fun a => ?_
  rw [clm_expand L a, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact PiLp.norm_apply_le a i

/-- Cone datum at every point of the closure: outward normal at frontier points, `v = 0` inside. -/
lemma cone_datum {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {normal : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ closure Ω) :
    ∃ r₀ t₀ : ℝ, ∃ v : EuclideanSpace ℝ (Fin d), 0 < r₀ ∧ 0 < t₀ ∧ ‖v‖ ≤ 1 ∧
      ∀ x ∈ closure Ω, dist x x₀ < r₀ → ∀ t : ℝ, 0 < t → t ≤ t₀ →
        Metric.ball (x - (3 * t) • v) t ⊆ Ω := by
  by_cases hfr : x₀ ∈ frontier Ω
  · obtain ⟨r₀, t₀, hr₀, ht₀, h⟩ := EthierKurtz.D2.cone_of_outward (hnormal x₀ hfr)
    exact ⟨r₀, t₀, normal x₀, hr₀, ht₀, (hnormal x₀ hfr).2.1.le, h⟩
  · have hx : x₀ ∈ Ω := by
      have : x₀ ∈ interior Ω := by
        by_contra h
        exact hfr ⟨hx₀, h⟩
      rwa [hΩ.interior_eq] at this
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx
    refine ⟨R / 2, R / 2, 0, by linarith, by linarith, by simp, ?_⟩
    intro x _ hxd t _ ht y hy
    apply hball
    simp only [smul_zero, sub_zero, Metric.mem_ball] at hy ⊢
    linarith [dist_triangle y x x₀]

lemma partial2_eq {g : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hg : DifferentiableAt ℝ (fderiv ℝ g) x) (i j : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have h := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).hasFDerivAt.comp x
    hg.hasFDerivAt
  rw [show (fun y => fderiv ℝ g y (EuclideanSpace.single j 1)) =
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))) ∘ fderiv ℝ g from rfl, h.fderiv]
  rfl

lemma d2_norm_le
    {T : EuclideanSpace ℝ (Fin d) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {a : ℝ}
    (h : ∀ i j, |T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ a) :
    ‖T‖ ≤ (d : ℝ) * ((d : ℝ) * a) := by
  have hi : ∀ i, ‖T (EuclideanSpace.single i 1)‖ ≤ (d : ℝ) * a := by
    intro i
    refine (opNorm_le_sum_basis _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => a) fun j _ => ?_).trans (le_of_eq (by simp))
    rw [Real.norm_eq_abs]; exact h i j
  refine (opNorm_le_sum_basis T).trans ?_
  refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
  simp

lemma iFDW_norm {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    ‖iteratedFDerivWithin ℝ 0 g U x‖ = |g x| ∧
    ‖iteratedFDerivWithin ℝ 1 g U x‖ = ‖fderiv ℝ g x‖ ∧
    ‖iteratedFDerivWithin ℝ 2 g U x‖ = ‖fderiv ℝ (fderiv ℝ g) x‖ := by
  refine ⟨by rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs], ?_, ?_⟩
  · rw [iteratedFDerivWithin_of_isOpen 1 hU hx, norm_iteratedFDeriv_one]
  · rw [iteratedFDerivWithin_of_isOpen 2 hU hx, ← norm_iteratedFDeriv_fderiv,
      norm_iteratedFDeriv_one]

lemma sub_derivs {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {F f : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ContDiffOn ℝ 2 F U) (hf : ContDiffOn ℝ 2 f U)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    fderiv ℝ (fun y => F y - f y) x = fderiv ℝ F x - fderiv ℝ f x ∧
    fderiv ℝ (fderiv ℝ (fun y => F y - f y)) x =
      fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ f) x := by
  have dF : ∀ y ∈ U, DifferentiableAt ℝ F y := fun y hy =>
    (hF.differentiableOn (by norm_num) y hy).differentiableAt (hU.mem_nhds hy)
  have df : ∀ y ∈ U, DifferentiableAt ℝ f y := fun y hy =>
    (hf.differentiableOn (by norm_num) y hy).differentiableAt (hU.mem_nhds hy)
  have hDF : ContDiffOn ℝ 1 (fun y => fderiv ℝ F y) U :=
    hF.fderiv_of_isOpen hU (by norm_num)
  have hDf : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y) U :=
    hf.fderiv_of_isOpen hU (by norm_num)
  have ddF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hDF.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)
  have ddf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hDf.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)
  have hev : fderiv ℝ (fun y => F y - f y) =ᶠ[𝓝 x] fun y => fderiv ℝ F y - fderiv ℝ f y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_sub (dF y hy) (df y hy)
  refine ⟨fderiv_sub (dF x hx) (df x hx), ?_⟩
  rw [hev.fderiv_eq]
  exact fderiv_sub ddF ddf

/-- E1'. Global `C²` mollification of a `C^{2,μ}` function on a bounded open set with outward unit
normals along its frontier, whose gradient extends continuously to the closure. -/
theorem global_mollify {Ω : Set (EuclideanSpace ℝ (Fin d))} (hb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) {normal : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x)) {μ : ℝ} (hμ : 0 < μ)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiffOn ℝ 2 f Ω)
    {J : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)}
    (hJ : ContinuousOn J (closure Ω)) (hJf : ∀ x ∈ Ω, fderiv ℝ f x = J x)
    (hH : ∀ i j, ComponentHolder Ω μ (fun x => fderiv ℝ (fun y => fderiv ℝ f y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)))
    (η : ℝ) (hη : 0 < η) :
    ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
      ∀ x ∈ Ω, |F x - f x| ≤ η ∧ ‖fderiv ℝ F x - fderiv ℝ f x‖ ≤ η ∧
        ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ f) x‖ ≤ η := by
  classical
  have hK : IsCompact (closure Ω) := hb.isCompact_closure
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hJ
  have hC₁' : ∀ y ∈ Ω, ‖fderiv ℝ f y‖ ≤ C₁ := fun y hy => by
    rw [hJf y hy]; exact hC₁ y (subset_closure hy)
  have hUC : ∀ η > 0, ∃ δ > 0, ∀ y ∈ Ω, ∀ z ∈ Ω, dist y z < δ →
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ η := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ :=
      Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hJ) ε hε
    refine ⟨δ, hδ, fun y hy z hz hyz => ?_⟩
    rw [hJf y hy, hJf z hz, ← dist_eq_norm]
    exact (h y (subset_closure hy) z (subset_closure hz) hyz).le
  choose! r₀ t₀ v hr₀ ht₀ hv hcone using
    fun x (hx : x ∈ closure Ω) => cone_datum hΩ hnormal hx
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun p : closure Ω => Metric.ball (p : EuclideanSpace ℝ (Fin d)) (r₀ p.1 / 2))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (half_pos (hr₀ x hx))⟩)
  let U : t → Set (EuclideanSpace ℝ (Fin d)) := fun k =>
    Metric.ball (k.1 : EuclideanSpace ℝ (Fin d)) (r₀ k.1.1 / 2)
  have hcov : closure Ω ⊆ ⋃ k, U k := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin d)) isClosed_closure U (fun _ => Metric.isOpen_ball) hcov
  obtain ⟨φ, hφs, hφU, hφ1⟩ : ∃ φ : t → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ k)) ∧ (∀ k, tsupport (φ k) ⊆ U k) ∧
      ∀ y ∈ closure Ω, ∑ k, φ k y = 1 :=
    ⟨fun k => ψ k, fun k => contMDiff_iff_contDiff.mp ((ψ k).contMDiff), hψ,
      fun y hy => by rw [← finsum_eq_sum_of_fintype]; exact ψ.sum_eq_one hy⟩
  have hφc : ∀ k : t, HasCompactSupport (φ k) := fun k =>
    (isCompact_closedBall (k.1 : EuclideanSpace ℝ (Fin d)) (r₀ k.1.1 / 2)).of_isClosed_subset
      (isClosed_tsupport _) ((hφU k).trans Metric.ball_subset_closedBall)
  have hB : ∀ k : t, ∀ m : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ m (φ k) x‖ ≤ B := fun k m =>
    (ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
      (hφs k)).bounded_above_of_compact_support ((hφc k).iteratedFDeriv m)
  choose B hB using hB
  set M : ℝ := ∑ k : t, (|B k 0| + |B k 1| + |B k 2|) + 1 with hM
  have hBM : ∀ k : t, ∀ m ≤ 2, ∀ x, ‖iteratedFDeriv ℝ m (φ k) x‖ ≤ M := by
    intro k m hm x
    have h1 : |B k 0| + |B k 1| + |B k 2| ≤ ∑ k : t, (|B k 0| + |B k 1| + |B k 2|) :=
      Finset.single_le_sum (f := fun k : t => |B k 0| + |B k 1| + |B k 2|)
        (fun k _ => by positivity) (Finset.mem_univ k)
    have h2 : B k m ≤ |B k 0| + |B k 1| + |B k 2| := by
      interval_cases m <;>
        linarith [le_abs_self (B k 0), le_abs_self (B k 1), le_abs_self (B k 2),
          abs_nonneg (B k 0), abs_nonneg (B k 1), abs_nonneg (B k 2)]
    linarith [hB k m x]
  have hM0 : 0 < M := by
    have : 0 ≤ ∑ k : t, (|B k 0| + |B k 1| + |B k 2|) :=
      Finset.sum_nonneg fun k _ => by positivity
    linarith
  set N : ℕ := Fintype.card t with hN
  set a : ℝ := η / (4 * M * (N + 1)) with ha
  have ha0 : 0 < a := by positivity
  set η' : ℝ := a / ((d : ℝ) * d + 1) with hη'
  have hη'0 : 0 < η' := by positivity
  have hη'a : (d : ℝ) * ((d : ℝ) * η') + η' = a := by
    rw [hη']; field_simp
  have hη'1 : η' ≤ a := by nlinarith [sq_nonneg (d : ℝ)]
  have hη'2 : (d : ℝ) * ((d : ℝ) * η') ≤ a := by linarith
  choose F hFs hFb using fun k : t =>
    EthierKurtz.D2E1.local_mollify hΩ (hr₀ _ k.1.2) (ht₀ _ k.1.2) (hv _ k.1.2) hμ (hcone _ k.1.2) hf hC₁' hUC hH
      η' hη'0
  have hF2 : ∀ k, ContDiffOn ℝ 2 (F k) Ω := fun k =>
    ((hFs k).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hφ2 : ∀ k, ContDiffOn ℝ 2 (φ k) Ω := fun k =>
    ((hφs k).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  -- local bounds of `h_k = F k - f`
  have hloc : ∀ k : t, ∀ x ∈ Ω, dist x k.1.1 < r₀ k.1.1 / 2 → ∀ m ≤ 2,
      ‖iteratedFDerivWithin ℝ m (fun y => F k y - f y) Ω x‖ ≤ a := by
    intro k x hx hxk m hm
    obtain ⟨b0, b1, b2⟩ := hFb k x hx hxk
    obtain ⟨e0, e1, e2⟩ := iFDW_norm hΩ (g := fun y => F k y - f y) hx
    obtain ⟨s1, s2⟩ := sub_derivs hΩ (hF2 k) hf hx
    have ddF : DifferentiableAt ℝ (fderiv ℝ (F k)) x :=
      ((hFs k).fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiable (by norm_num) x
    have ddf : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (((hf.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).differentiableOn (by norm_num)) x
        hx).differentiableAt (hΩ.mem_nhds hx)
    interval_cases m
    · rw [e0]; linarith
    · rw [e1, s1]; linarith
    · rw [e2, s2]
      refine (d2_norm_le (a := η') fun i j => ?_).trans hη'2
      have := b2 i j
      rw [partial2_eq ddF, partial2_eq ddf] at this
      simpa using this
  -- each product term
  have hterm : ∀ k : t, ∀ x ∈ Ω, ∀ m ≤ 2,
      ‖iteratedFDerivWithin ℝ m (fun y => φ k y * (F k y - f y)) Ω x‖ ≤ 4 * M * a := by
    intro k x hx m hm
    have hm' : ((m : ℕ) : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hm
    refine (norm_iteratedFDerivWithin_mul_le (hφ2 k) ((hF2 k).sub hf) hΩ.uniqueDiffOn hx
      hm').trans ?_
    have hle : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (φ k) Ω x‖ *
        ‖iteratedFDerivWithin ℝ (m - i) (fun y => F k y - f y) Ω x‖ ≤
        (m.choose i : ℝ) * (M * a) := by
      intro i hi
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [iteratedFDerivWithin_of_isOpen i hΩ hx]
      by_cases hxk : dist x k.1.1 < r₀ k.1.1 / 2
      · exact mul_le_mul (hBM k i (by omega) x) (hloc k x hx hxk (m - i) (by omega))
          (norm_nonneg _) hM0.le
      · have hnot : x ∉ tsupport (φ k) := fun h => hxk (hφU k h)
        have h0 : iteratedFDeriv ℝ i (φ k) x = 0 := by
          by_contra hne
          exact hnot (support_iteratedFDeriv_subset i hne)
        rw [h0, norm_zero, zero_mul]
        positivity
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.sum_mul]
    have hs : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m := by
      exact_mod_cast Nat.sum_range_choose m
    rw [hs]
    have h4 : (2 : ℝ) ^ m ≤ 4 := by interval_cases m <;> norm_num
    have : 0 ≤ M * a := by positivity
    nlinarith
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∑ k, φ k x * F k x with hG
  have hGs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G :=
    ContDiff.sum fun k _ => (hφs k).mul (hFs k)
  refine ⟨G, hGs, fun x hx => ?_⟩
  have hEq : EqOn (fun y => G y - f y) (∑ k : t, fun y => φ k y * (F k y - f y)) Ω := by
    intro y hy
    simp only [Finset.sum_apply, hG]
    have h1 := hφ1 y (subset_closure hy)
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
  have hall : ∀ m ≤ 2, ‖iteratedFDerivWithin ℝ m (fun y => G y - f y) Ω x‖ ≤ η := by
    intro m hm
    have hm' : ((m : ℕ) : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hm
    rw [iteratedFDerivWithin_congr hEq hx m, iteratedFDerivWithin_sum_apply hΩ.uniqueDiffOn hx
      (fun k _ => (((hφ2 k).mul ((hF2 k).sub hf)).of_le hm').contDiffWithinAt hx)]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hterm k x hx m hm).trans ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, ha]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    rw [show (N : ℝ) * (4 * M * (η / (4 * M * (N + 1)))) = η * (N / (N + 1)) by
      field_simp]
    have : (N : ℝ) / (N + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  have hG2 : ContDiffOn ℝ 2 G Ω := ((hGs).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  obtain ⟨e0, e1, e2⟩ := iFDW_norm hΩ (g := fun y => G y - f y) hx
  obtain ⟨s1, s2⟩ := sub_derivs hΩ hG2 hf hx
  refine ⟨?_, ?_, ?_⟩
  · have := hall 0 (by norm_num); rwa [e0] at this
  · have := hall 1 (by norm_num); rwa [e1, s1] at this
  · have := hall 2 le_rfl; rwa [e2, s2] at this

end EthierKurtz.E1G

end E1G

open EthierKurtz in
theorem solution (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hbounded : Bornology.IsBounded Ω)
    (hopen : IsOpen Ω) (normal : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x)) (μ : ℝ) (hμ : 0 < μ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiffOn ℝ 2 f Ω)
    (J : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (hJ : ContinuousOn J (closure Ω)) (hJf : ∀ x ∈ Ω, fderiv ℝ f x = J x)
    (hH : ∀ i j, ComponentHolder Ω μ (fun x => fderiv ℝ (fun y => fderiv ℝ f y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)))
    (η : ℝ) (hη : 0 < η) :
    ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
      ∀ x ∈ Ω, |F x - f x| ≤ η ∧ ‖fderiv ℝ F x - fderiv ℝ f x‖ ≤ η ∧
        ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ f) x‖ ≤ η := by
  exact EthierKurtz.E1G.global_mollify hbounded hopen hnormal hμ hf hJ hJf hH η hη
