-- Prove2me | solution 1 for EthierKurtz.componentHolder_extends_closure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T05:35:32.008513+00:00
-- url     : https://prove2.me/submissions/2cde8f56-cd72-4cb4-8405-065c8e0e29be

import Mathlib
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_ComponentHolder

set_option autoImplicit false

open Filter
open scoped Topology BoundedContinuousFunction

namespace Pd67abb68C2b

open EthierKurtz

/-- Two points close to a frontier point with a C^1 defining function are joined inside
`Ω ∩ ball x0 ρ` through the interior point `x0 - (ρ/2) n`. -/
lemma connected_near {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (x0 n : EuclideanSpace ℝ (Fin d)) (hx0 : IsOutwardUnitNormal Ω x0 n) :
    ∃ ρ₁ κ : ℝ, 0 < ρ₁ ∧ 0 < κ ∧ κ < 1 ∧ ∀ ρ, 0 < ρ → ρ ≤ ρ₁ →
      ∀ y ∈ Ω ∩ Metric.ball x0 (κ * ρ), ∀ w ∈ Ω ∩ Metric.ball x0 (κ * ρ),
        w ∈ connectedComponentIn (Ω ∩ Metric.ball x0 ρ) y := by
  obtain ⟨-, hn1, V, hV, hx0V, r, σ, hσ, hr, hr0, hΩ, hL⟩ := hx0
  set L := fderiv ℝ r x0 with hLdef
  set K := ‖L‖ with hK
  have hLn : L n = σ := by
    rw [hL]
    have h2 := EuclideanSpace.real_norm_sq_eq n
    rw [hn1] at h2
    have : (∑ i, n i * n i) = 1 := by
      rw [← one_pow 2, h2]; congr 1; ext i; ring
    rw [this, mul_one]
  have hcont := hr.continuousOn_fderiv_of_isOpen hV le_rfl
  have hdiff : DifferentiableOn ℝ r V := hr.differentiableOn one_ne_zero
  -- uniform closeness of the derivative near x0
  have hη : 0 < σ / 4 := by linarith
  obtain ⟨ρ₁, hρ₁, hball⟩ : ∃ ρ₁ > 0, Metric.ball x0 ρ₁ ⊆ V ∧
      ∀ z ∈ Metric.ball x0 ρ₁, ‖fderiv ℝ r z - L‖ ≤ σ / 4 := by
    have hca : ContinuousAt (fun x => fderiv ℝ r x) x0 :=
      hcont.continuousAt (hV.mem_nhds hx0V)
    obtain ⟨δ₁, hδ₁, h1⟩ := Metric.isOpen_iff.mp hV x0 hx0V
    obtain ⟨δ₂, hδ₂, h2⟩ := Metric.continuousAt_iff.mp hca (σ / 4) hη
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun z hz => h1 ?_, fun z hz => ?_⟩
    · exact Metric.ball_subset_ball (min_le_left _ _) hz
    · have := h2 (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _))
      rw [dist_eq_norm] at this
      exact this.le
  have hK1 : 0 < K + 1 := by positivity
  set κ := min (1 / 8 : ℝ) (σ / (4 * (K + 1))) with hκ
  have hκpos : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκ8 : κ ≤ 1 / 8 := min_le_left _ _
  have hκK : K * κ ≤ σ / 4 := by
    have h1 : κ ≤ σ / (4 * (K + 1)) := min_le_right _ _
    have h2 : K * κ ≤ (K + 1) * κ := by nlinarith [norm_nonneg L]
    have h3 : (K + 1) * κ ≤ (K + 1) * (σ / (4 * (K + 1))) :=
      mul_le_mul_of_nonneg_left h1 hK1.le
    have h4 : (K + 1) * (σ / (4 * (K + 1))) = σ / 4 := by field_simp
    linarith
  refine ⟨ρ₁, κ, hρ₁, hκpos, by linarith, ?_⟩
  intro ρ hρ hρρ₁ y hy w hw
  set p : EuclideanSpace ℝ (Fin d) := x0 - (ρ / 2) • n with hp
  have hpx0 : ‖p - x0‖ = ρ / 2 := by
    rw [hp, sub_sub_cancel_left, norm_neg, norm_smul, hn1, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  -- every point of a segment from a point near x0 to p lies in Ω ∩ ball x0 ρ
  have hseg : ∀ y ∈ Ω ∩ Metric.ball x0 (κ * ρ), segment ℝ y p ⊆ Ω ∩ Metric.ball x0 ρ := by
    intro y hy
    have hyx : ‖y - x0‖ < κ * ρ := by
      have := Metric.mem_ball.mp hy.2; rwa [dist_eq_norm] at this
    have hyb : y ∈ Metric.ball x0 ρ := by
      rw [Metric.mem_ball, dist_eq_norm]; nlinarith
    have hpb : p ∈ Metric.ball x0 ρ := by
      rw [Metric.mem_ball, dist_eq_norm, hpx0]; linarith
    have hsub : segment ℝ y p ⊆ Metric.ball x0 ρ :=
      (convex_ball x0 ρ).segment_subset hyb hpb
    intro z hz
    refine ⟨?_, hsub hz⟩
    have hzb := hsub hz
    have hballρ : Metric.ball x0 ρ ⊆ Metric.ball x0 ρ₁ := Metric.ball_subset_ball hρρ₁
    have hzV : z ∈ V := hball.1 (hballρ hzb)
    have hyV : y ∈ V := hball.1 (hballρ hyb)
    refine (hΩ z hzV).mpr ?_
    have hry : r y < 0 := (hΩ y hyV).mp hy.1
    -- mean value estimate on the ball
    have hmvt : ‖r z - r y - L (z - y)‖ ≤ σ / 4 * ‖z - y‖ := by
      refine (convex_ball x0 ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (f' := fun x => fderiv ℝ r x) (fun x hx => ?_) (fun x hx => hball.2 x (hballρ hx))
        hyb hzb
      have hxV : x ∈ V := hball.1 (hballρ hx)
      exact ((hdiff x hxV).differentiableAt (hV.mem_nhds hxV)).hasFDerivAt.hasFDerivWithinAt
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
    have hzy : s • y + t • p - y = t • (p - y) := by
      obtain rfl : s = 1 - t := by linarith
      module
    rw [hzy] at hmvt
    have hLpy : L (p - y) = L (x0 - y) - (ρ / 2) * σ := by
      have : p - y = (x0 - y) - (ρ / 2) • n := by rw [hp]; abel
      rw [this, map_sub, map_smul, hLn, smul_eq_mul]
    have hLx : L (x0 - y) ≤ K * (κ * ρ) := by
      have h1 : L (x0 - y) ≤ ‖L (x0 - y)‖ := le_abs_self _
      have h2 : ‖L (x0 - y)‖ ≤ K * ‖x0 - y‖ := L.le_opNorm _
      have h3 : ‖x0 - y‖ < κ * ρ := by rwa [norm_sub_rev]
      nlinarith [norm_nonneg L]
    have hpy : ‖p - y‖ ≤ ρ := by
      have : p - y = (p - x0) - (y - x0) := by abel
      rw [this]
      calc ‖(p - x0) - (y - x0)‖ ≤ ‖p - x0‖ + ‖y - x0‖ := norm_sub_le _ _
        _ ≤ ρ := by rw [hpx0]; nlinarith
    have hnorm : ‖t • (p - y)‖ ≤ t * ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left hpy ht
    have habs := (abs_le.mp (le_of_eq_of_le (Real.norm_eq_abs _).symm hmvt)).2
    rw [map_smul, smul_eq_mul, hLpy] at habs
    have hKκ : K * (κ * ρ) ≤ σ / 4 * ρ := by nlinarith
    have e1 := mul_le_mul_of_nonneg_left hnorm hη.le
    have e2 := mul_le_mul_of_nonneg_left (hLx.trans hKκ) ht
    nlinarith
  have hpy := hseg y hy
  have hpw := hseg w hw
  have hconn : IsPreconnected (segment ℝ y p ∪ segment ℝ p w) := by
    refine IsPreconnected.union p (right_mem_segment ℝ y p) (left_mem_segment ℝ p w)
      (convex_segment y p).isPreconnected (convex_segment p w).isPreconnected
  have hsub : segment ℝ y p ∪ segment ℝ p w ⊆ Ω ∩ Metric.ball x0 ρ := by
    refine Set.union_subset hpy ?_
    rw [segment_symm]; exact hpw
  exact hconn.subset_connectedComponentIn (Or.inl (left_mem_segment ℝ y p)) hsub
    (Or.inr (right_mem_segment ℝ p w))

end Pd67abb68C2b

open EthierKurtz in
theorem solution (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ)
    (normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hφ : ComponentHolder Ω μ φ) :
    ∃ ψ : (closure Ω) →ᵇ ℝ, ∀ x : closure Ω, (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ Ω →
      ψ x = φ x := by
  obtain ⟨hcontφ, ρ₀, M, hρ₀, hM, hH⟩ := hφ
  have hosc : ∀ x0 ∈ frontier Ω, ∀ ε > 0, ∃ s > 0, ∀ y ∈ Ω ∩ Metric.ball x0 s,
      ∀ w ∈ Ω ∩ Metric.ball x0 s, |φ y - φ w| ≤ ε := by
    intro x0 hx0 ε hε
    obtain ⟨ρ₁, κ, hρ₁, hκ, hκ1, hc⟩ :=
      Pd67abb68C2b.connected_near Ω x0 (normal x0) (hnormal x0 hx0)
    obtain ⟨ρ, hρ, hρle, hρε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ min ρ₀ ρ₁ ∧ M * ρ ^ μ ≤ ε := by
      have hca : ContinuousAt (fun x : ℝ => M * x ^ μ) 0 :=
        continuousAt_const.mul (Real.continuousAt_rpow_const 0 μ (Or.inr hμ.le))
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hca ε hε
      refine ⟨min (min ρ₀ ρ₁) (δ / 2), lt_min (lt_min hρ₀ hρ₁) (by linarith),
        min_le_left _ _, ?_⟩
      have hpos : 0 < min (min ρ₀ ρ₁) (δ / 2) := lt_min (lt_min hρ₀ hρ₁) (by linarith)
      have hd : dist (min (min ρ₀ ρ₁) (δ / 2)) 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
        exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have := hδ' hd
      rw [Real.zero_rpow hμ.ne', mul_zero, Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans this.le
    refine ⟨κ * ρ, by positivity, fun y hy w hw => ?_⟩
    have hyc := hc ρ hρ (hρle.trans (min_le_right _ _)) y hy w hw
    have hyb : y ∈ Ω ∩ Metric.ball x0 ρ :=
      ⟨hy.1, Metric.ball_subset_ball (by nlinarith) hy.2⟩
    have hyy : y ∈ connectedComponentIn (Ω ∩ Metric.ball x0 ρ) y :=
      mem_connectedComponentIn hyb
    exact (hH ρ hρ (hρle.trans (min_le_left _ _)) x0 y hyb y hyy w hyc).trans hρε
  have hlim : ∀ x ∈ closure Ω, ∃ v, Tendsto φ (𝓝[Ω] x) (𝓝 v) := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · exact ⟨φ x, hcontφ x hxΩ⟩
    · have hfr : x ∈ frontier Ω := ⟨hx, by rwa [hopen.interior_eq]⟩
      haveI : (𝓝[Ω] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
      refine cauchy_map_iff_exists_tendsto.mp ?_
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨s, hs, hS⟩ := hosc x hfr (ε / 2) (by linarith)
      refine ⟨φ '' (Ω ∩ Metric.ball x s),
        image_mem_map (inter_mem_nhdsWithin Ω (Metric.ball_mem_nhds x hs)), ?_⟩
      rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
      rw [Real.dist_eq]
      linarith [hS y hy w hw]
  have hcon : ContinuousOn (extendFrom Ω φ) (closure Ω) :=
    continuousOn_extendFrom subset_rfl hlim
  haveI : CompactSpace (closure Ω) :=
    isCompact_iff_compactSpace.mp hbounded.isCompact_closure
  refine ⟨BoundedContinuousFunction.mkOfCompact
    ⟨(closure Ω).restrict (extendFrom Ω φ), hcon.restrict⟩, fun x hx => ?_⟩
  exact extendFrom_extends hcontφ x hx
