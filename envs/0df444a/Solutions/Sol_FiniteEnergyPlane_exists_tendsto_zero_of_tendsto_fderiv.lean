-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tendsto_zero_of_tendsto_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-22T18:17:38.754737+00:00
-- url     : https://prove2.me/submissions/6715fe1a-5327-4b7a-8d0b-2a7c1a63d7c4

import Mathlib



/-!
# Nondegenerate zeros persist under `C¹`-small perturbations

`f` has a strict derivative `L` (an isomorphism) at a zero `p`; the perturbations `h k` have
`h k p → 0` and `fderiv (h k) → 0` uniformly near `p`. Then `f + h k` is injective on a fixed ball
around `p` for large `k`, and has zeros `x k → p`.
-/

namespace FiniteEnergyPlane

open Metric Filter Topology Set
open scoped NNReal

theorem exists_tendsto_zero_of_tendsto_fderiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {L : E ≃L[ℝ] F} {p : E} (hf : HasStrictFDerivAt f (L : E →L[ℝ] F) p)
    (hp : f p = 0) {h : ℕ → E → F} {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hd : ∀ k, ∀ x ∈ ball p δ₀, DifferentiableAt ℝ (h k) x)
    (h0 : Tendsto (fun k => h k p) atTop (𝓝 0))
    (hD : TendstoUniformlyOn (fun k x => fderiv ℝ (h k) x) 0 atTop (ball p δ₀)) :
    ∃ δ > 0, (∀ᶠ k in atTop, InjOn (fun x => f x + h k x) (ball p δ)) ∧
      ∃ x : ℕ → E, Tendsto x atTop (𝓝 p) ∧ ∀ᶠ k in atTop, f (x k) + h k (x k) = 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · haveI : Subsingleton F := (Equiv.subsingleton_congr L.toEquiv).1 hE
    refine ⟨1, one_pos, Eventually.of_forall fun k x _ y _ _ => Subsingleton.elim x y,
      fun _ => p, tendsto_const_nhds, Eventually.of_forall fun k => Subsingleton.elim _ _⟩
  set N : ℝ≥0 := ‖(L.symm : F →L[ℝ] E)‖₊ with hN
  have hNpos : 0 < N := by
    rw [hN, nnnorm_pos]
    intro h0'
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    apply hv
    have : (L.symm : F →L[ℝ] E) (L v) = 0 := by rw [h0']; rfl
    simpa using this
  set c : ℝ≥0 := N⁻¹ / 4 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  obtain ⟨s, hs, hfs⟩ := hf.approximates_deriv_on_nhds (Or.inr hcpos)
  obtain ⟨δ₁, hδ₁, hδ₁s⟩ := Metric.mem_nhds_iff.1 hs
  set δ := min δ₁ δ₀ with hδ
  have hδpos : 0 < δ := lt_min hδ₁ hδ₀
  have hδsub : ball p δ ⊆ s := (ball_subset_ball (min_le_left _ _)).trans hδ₁s
  have hδsub₀ : ball p δ ⊆ ball p δ₀ := ball_subset_ball (min_le_right _ _)
  -- eventually the perturbation is `c`-Lipschitz on `ball p δ`
  have hDev : ∀ᶠ k in atTop, ∀ x ∈ ball p δ₀, ‖fderiv ℝ (h k) x‖₊ ≤ c := by
    have := (Metric.tendstoUniformlyOn_iff.1 hD) c hcpos
    filter_upwards [this] with k hk x hx
    have := hk x hx
    simp only [Pi.zero_apply, dist_zero_left] at this
    exact_mod_cast this.le
  have happ : ∀ᶠ k in atTop,
      ApproximatesLinearOn (fun x => f x + h k x) (L : E →L[ℝ] F) (ball p δ) (2 * c) := by
    filter_upwards [hDev] with k hk
    have hlip : LipschitzOnWith c (h k) (ball p δ) :=
      (convex_ball p δ).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun x hx => hd k x (hδsub₀ hx)) (fun x hx => hk x (hδsub₀ hx))
    intro x hx y hy
    have h1 := hfs x (hδsub hx) y (hδsub hy)
    have h2 := hlip.norm_sub_le hx hy
    calc ‖f x + h k x - (f y + h k y) - (L : E →L[ℝ] F) (x - y)‖
        = ‖(f x - f y - (L : E →L[ℝ] F) (x - y)) + (h k x - h k y)‖ := by congr 1; abel
      _ ≤ ‖f x - f y - (L : E →L[ℝ] F) (x - y)‖ + ‖h k x - h k y‖ := norm_add_le _ _
      _ ≤ c * ‖x - y‖ + c * ‖x - y‖ := add_le_add h1 h2
      _ = ((2 * c : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; ring
  have h2c : 2 * c < N⁻¹ := by
    rw [hc]
    have : 0 < N⁻¹ := inv_pos.2 hNpos
    rw [← NNReal.coe_lt_coe]; push_cast
    have : (0 : ℝ) < (N : ℝ)⁻¹ := by exact_mod_cast this
    linarith
  have hinj : ∀ᶠ k in atTop, InjOn (fun x => f x + h k x) (ball p δ) := by
    filter_upwards [happ] with k hk
    exact hk.injOn (Or.inr h2c)
  -- zeros in every small closed ball
  have hzero : ∀ r, 0 < r → r < δ → ∀ᶠ k in atTop, ∃ x ∈ closedBall p r, f x + h k x = 0 := by
    intro r hr hrδ
    have hρ : (0 : ℝ) < ((N : ℝ)⁻¹ - (2 * c : ℝ≥0)) * r := by
      apply mul_pos _ hr
      have : ((2 * c : ℝ≥0) : ℝ) < ((N⁻¹ : ℝ≥0) : ℝ) := by exact_mod_cast h2c
      push_cast at this ⊢; linarith
    have hev := (Metric.tendsto_nhds.1 h0) _ hρ
    filter_upwards [happ, hev] with k hk hk0
    have hsub : closedBall p r ⊆ ball p δ := closedBall_subset_ball hrδ
    have hsurj := hk.surjOn_closedBall_of_nonlinearRightInverse
      L.toNonlinearRightInverse hr.le hsub
    have hmem : (0 : F) ∈ closedBall (f p + h k p)
        (((L.toNonlinearRightInverse.nnnorm : ℝ)⁻¹ - ((2 * c : ℝ≥0) : ℝ)) * r) := by
      rw [mem_closedBall, dist_comm, dist_zero_right, hp, zero_add]
      have := hk0
      rw [dist_zero_right] at this
      exact this.le
    obtain ⟨x, hx, hx0⟩ := hsurj hmem
    exact ⟨x, hx, hx0⟩
  -- choose the zeros
  classical
  let x : ℕ → E := fun k =>
    if hk : ∃ x ∈ ball p δ, f x + h k x = 0 then Classical.choose hk else p
  have hxspec : ∀ k, (∃ x ∈ ball p δ, f x + h k x = 0) →
      x k ∈ ball p δ ∧ f (x k) + h k (x k) = 0 := by
    intro k hk
    simp only [x, dif_pos hk]
    exact Classical.choose_spec hk
  have hball : ∀ r, 0 < r → r < δ → ∀ᶠ k in atTop, x k ∈ closedBall p r ∧
      f (x k) + h k (x k) = 0 := by
    intro r hr hrδ
    filter_upwards [hzero r hr hrδ, hinj] with k ⟨x', hx', hx'0⟩ hk
    have hx'b : x' ∈ ball p δ := closedBall_subset_ball hrδ hx'
    obtain ⟨hxk, hxk0⟩ := hxspec k ⟨x', hx'b, hx'0⟩
    have : x k = x' := hk hxk hx'b (by simp only; rw [hxk0, hx'0])
    exact ⟨this ▸ hx', hxk0⟩
  refine ⟨δ, hδpos, hinj, x, ?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro r hr
    have hr' : 0 < min (r / 2) (δ / 2) := lt_min (half_pos hr) (half_pos hδpos)
    filter_upwards [hball _ hr' (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδpos))]
      with k hk
    exact lt_of_le_of_lt (mem_closedBall.1 hk.1)
      (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr))
  · filter_upwards [hball (δ / 2) (half_pos hδpos) (half_lt_self hδpos)] with k hk
    exact hk.2

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology Set
open scoped NNReal

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {L : E ≃L[ℝ] F} {p : E} (hf : HasStrictFDerivAt f (L : E →L[ℝ] F) p)
    (hp : f p = 0) {h : ℕ → E → F} {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hd : ∀ k, ∀ x ∈ ball p δ₀, DifferentiableAt ℝ (h k) x)
    (h0 : Tendsto (fun k => h k p) atTop (𝓝 0))
    (hD : TendstoUniformlyOn (fun k x => fderiv ℝ (h k) x) 0 atTop (ball p δ₀)) :
    ∃ δ > 0, (∀ᶠ k in atTop, InjOn (fun x => f x + h k x) (ball p δ)) ∧
      ∃ x : ℕ → E, Tendsto x atTop (𝓝 p) ∧ ∀ᶠ k in atTop, f (x k) + h k (x k) = 0 :=
  exists_tendsto_zero_of_tendsto_fderiv hf hp hδ₀ hd h0 hD
