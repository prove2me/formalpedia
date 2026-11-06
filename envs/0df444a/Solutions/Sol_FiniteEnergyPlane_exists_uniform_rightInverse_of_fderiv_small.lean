-- Prove2me | solution 1 for FiniteEnergyPlane.exists_uniform_rightInverse_of_fderiv_small
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-05T20:25:20.98683+00:00
-- url     : https://prove2.me/submissions/5f6e85c3-14d6-4383-aa62-b3973bf4c29a

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.MeanValue

open Metric Filter Topology
open scoped NNReal

namespace FiniteEnergyPlane

theorem exists_uniform_rightInverse_of_fderiv_small_aux {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (Φ : X → Y) (d : ℕ → X → Y) (e : X ≃L[ℝ] Y) (p₀ : X) (R : ℝ) (hR : 0 < R)
    (hΦ : ContDiffAt ℝ 1 Φ p₀) (he : fderiv ℝ Φ p₀ = (e : X →L[ℝ] Y))
    (hd : ∀ k, ∀ p ∈ ball p₀ R, DifferentiableAt ℝ (d k) p)
    (hdu : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ p ∈ ball p₀ R, ‖fderiv ℝ (d k) p‖ ≤ ε)
    (hd0 : Tendsto (fun k => d k p₀) atTop (𝓝 0)) :
    ∃ K > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ η ∈ Set.Ioc 0 R₀, ∃ δ > (0 : ℝ), ∀ᶠ k in atTop, ∃ Ψ : Y → X,
      ContinuousOn Ψ (ball (Φ p₀) δ) ∧
      (∀ y ∈ ball (Φ p₀) δ, Ψ y ∈ ball p₀ η ∧ Φ (Ψ y) + d k (Ψ y) = y) ∧
      ∀ p ∈ ball p₀ η, ∀ y ∈ ball (Φ p₀) δ, ‖p - Ψ y‖ ≤ K * ‖y - (Φ p + d k p)‖ := by
  set N : ℝ≥0 := ‖(e.symm : Y →L[ℝ] X)‖₊ with hNdef
  have hN : 0 < N := e.nnnorm_symm_pos
  have hNi : 0 < N⁻¹ := inv_pos.2 hN
  set c : ℝ≥0 := N⁻¹ / 2 with hcdef
  have hc0 : 0 < c := by simp [hcdef, hNi]
  have hcN : c < N⁻¹ := by
    rw [hcdef]; exact NNReal.half_lt_self hNi.ne'
  have hc : Subsingleton X ∨ c < N⁻¹ := Or.inr hcN
  have hκ : 0 < N⁻¹ - c := tsub_pos_of_lt hcN
  set κ : ℝ := ((N⁻¹ - c : ℝ≥0) : ℝ) with hκdef
  have hκ' : 0 < κ := by exact_mod_cast hκ
  have hs := hΦ.hasStrictFDerivAt (by norm_num)
  rw [he] at hs
  obtain ⟨s₀, hs₀, hA⟩ := hs.approximates_deriv_on_nhds (c := c / 2)
    (Or.inr (half_pos hc0))
  obtain ⟨R₁, hR₁, hR₁s⟩ := Metric.mem_nhds_iff.1 hs₀
  set R₀ := min R R₁ with hR₀
  have hR₀pos : 0 < R₀ := lt_min hR hR₁
  refine ⟨((N⁻¹ - c)⁻¹ : ℝ≥0), by exact_mod_cast inv_pos.2 hκ, R₀, hR₀pos, fun η hη => ?_⟩
  have hηR : ball p₀ η ⊆ ball p₀ R := ball_subset_ball (hη.2.trans (min_le_left _ _))
  have hηs : ball p₀ η ⊆ s₀ := (ball_subset_ball (hη.2.trans (min_le_right _ _))).trans hR₁s
  have hη0 : 0 < η := hη.1
  refine ⟨κ * η / 4, by positivity, ?_⟩
  have hdu' := hdu ((c : ℝ) / 2) (by positivity)
  have hd0' : ∀ᶠ k in atTop, ‖d k p₀‖ < κ * η / 4 := by
    have := (tendsto_norm.comp hd0)
    simp only [norm_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hdu', hd0'] with k hk hk0
  set F : X → Y := fun p => Φ p + d k p with hF
  have happ : ApproximatesLinearOn F (e : X →L[ℝ] Y) (ball p₀ η) c := by
    intro x hx y hy
    have h1 := (hA.mono_set hηs) x hx y hy
    have h2 : ‖d k x - d k y‖ ≤ (c : ℝ) / 2 * ‖x - y‖ :=
      (convex_ball p₀ η).norm_image_sub_le_of_norm_fderiv_le
        (fun z hz => hd k z (hηR hz)) (fun z hz => hk z (hηR hz)) hy hx
    have h3 : F x - F y - (e : X →L[ℝ] Y) (x - y) =
        (Φ x - Φ y - (e : X →L[ℝ] Y) (x - y)) + (d k x - d k y) := by
      simp only [hF]; abel
    rw [h3]
    refine (norm_add_le _ _).trans ?_
    have h1' : ‖Φ x - Φ y - (e : X →L[ℝ] Y) (x - y)‖ ≤ (c : ℝ) / 2 * ‖x - y‖ := by
      simpa using h1
    linarith
  set PH := happ.toOpenPartialHomeomorph F (ball p₀ η) hc isOpen_ball with hPH
  have hclosed : closedBall p₀ (η / 2) ⊆ ball p₀ η := closedBall_subset_ball (half_lt_self hη0)
  have hsurj := happ.surjOn_closedBall_of_nonlinearRightInverse e.toNonlinearRightInverse
    (half_pos hη0).le hclosed
  have hT : ball (Φ p₀) (κ * η / 4) ⊆ PH.target := by
    intro y hy
    have hFp : F p₀ = Φ p₀ + d k p₀ := rfl
    have hmem : y ∈ closedBall (F p₀) ((((e.toNonlinearRightInverse.nnnorm : ℝ≥0) : ℝ)⁻¹ - c) *
        (η / 2)) := by
      have heq : (((e.toNonlinearRightInverse.nnnorm : ℝ≥0) : ℝ)⁻¹ - c) = κ := by
        have hle : c ≤ N⁻¹ := hcN.le
        rw [hκdef, NNReal.coe_sub hle, NNReal.coe_inv]
        rfl
      rw [heq, mem_closedBall, dist_eq_norm, hFp]
      have h1 : y - (Φ p₀ + d k p₀) = (y - Φ p₀) - d k p₀ := by abel
      rw [h1]
      have h2 : ‖y - Φ p₀‖ < κ * η / 4 := by simpa [dist_eq_norm] using hy
      have h3 := norm_sub_le (y - Φ p₀) (d k p₀)
      linarith
    obtain ⟨p, hp, hpy⟩ := hsurj hmem
    exact ⟨p, hclosed hp, hpy⟩
  refine ⟨PH.symm, PH.continuousOn_symm.mono hT, fun y hy => ?_, fun p hp y hy => ?_⟩
  · have hyT := hT hy
    exact ⟨PH.map_target hyT, PH.right_inv hyT⟩
  · have hyT := hT hy
    have hq : PH.symm y ∈ ball p₀ η := PH.map_target hyT
    have hval : F (PH.symm y) = y := PH.right_inv hyT
    have hanti := (happ.antilipschitz hc).le_mul_dist ⟨p, hp⟩ ⟨PH.symm y, hq⟩
    simp only [Set.domRestrict_apply, dist_eq_norm] at hanti
    rw [Subtype.dist_eq, dist_eq_norm] at hanti
    have h4 : ‖F p - y‖ = ‖y - (Φ p + d k p)‖ := norm_sub_rev _ _
    rw [hval, h4] at hanti
    exact hanti

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology

theorem solution {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (Φ : X → Y) (d : ℕ → X → Y) (e : X ≃L[ℝ] Y) (p₀ : X) (R : ℝ) (hR : 0 < R)
    (hΦ : ContDiffAt ℝ 1 Φ p₀) (he : fderiv ℝ Φ p₀ = (e : X →L[ℝ] Y))
    (hd : ∀ k, ∀ p ∈ ball p₀ R, DifferentiableAt ℝ (d k) p)
    (hdu : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ p ∈ ball p₀ R, ‖fderiv ℝ (d k) p‖ ≤ ε)
    (hd0 : Tendsto (fun k => d k p₀) atTop (𝓝 0)) :
    ∃ K > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ η ∈ Set.Ioc 0 R₀, ∃ δ > (0 : ℝ), ∀ᶠ k in atTop, ∃ Ψ : Y → X,
      ContinuousOn Ψ (ball (Φ p₀) δ) ∧
      (∀ y ∈ ball (Φ p₀) δ, Ψ y ∈ ball p₀ η ∧ Φ (Ψ y) + d k (Ψ y) = y) ∧
      ∀ p ∈ ball p₀ η, ∀ y ∈ ball (Φ p₀) δ, ‖p - Ψ y‖ ≤ K * ‖y - (Φ p + d k p)‖ :=
  FiniteEnergyPlane.exists_uniform_rightInverse_of_fderiv_small_aux Φ d e p₀ R hR hΦ he hd hdu hd0
