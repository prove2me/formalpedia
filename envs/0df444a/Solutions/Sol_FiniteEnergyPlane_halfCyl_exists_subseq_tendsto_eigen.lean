-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_exists_subseq_tendsto_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-28T21:36:37.238526+00:00
-- url     : https://prove2.me/submissions/71bfb58f-c6ba-4494-aa31-a2423786a7dc

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_tendstoUniformly_of_tendsto_intervalIntegral_sq
import Theorems.Thm_FiniteEnergyPlane_halfCyl_exists_subseq_tendsto_eigen_L2
import Theorems.Thm_FiniteEnergyPlane_halfCyl_slice_deriv_sq_le



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem halfCyl_exists_subseq_tendsto_eigen_aux {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ s₀ : ℝ, (∀ s ≥ s₀, 0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) ∧
      ∀ σ : ℕ → ℝ, Tendsto σ atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
          TendstoUniformly (fun (k : ℕ) (t : ℝ) =>
            (Real.sqrt (∫ x in (0:ℝ)..1, ‖ζ (σ (φ k), x)‖ ^ 2))⁻¹ • ζ (σ (φ k), t)) e atTop := by
  obtain ⟨μ, hμ, s₀, hpos, hL⟩ := halfCyl_exists_subseq_tendsto_eigen_L2 S hS hSper Sinf hSinf
    hSinf' hSas ζ hζ hne C δ₀ hgrowth
  obtain ⟨M, s₁, hM⟩ := halfCyl_slice_deriv_sq_le S hS hSper Sinf hSinf hSinf' hSas ζ hζ hne C δ₀
    hgrowth
  refine ⟨μ, hμ, s₀, hpos, fun σ hσ => ?_⟩
  obtain ⟨φ, hφ, e, he, hconv⟩ := hL σ hσ
  refine ⟨φ, hφ, e, he, ?_⟩
  -- the slices are smooth loops
  have hslice : ∀ s > 0, ContDiff ℝ ∞ (fun x => ζ (s, x)) := by
    intro s hs
    rw [← contDiffOn_univ]
    exact hζ.1.comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
      (fun x _ => ⟨hs, Set.mem_univ _⟩)
  have hτ : Tendsto (fun k => σ (φ k)) atTop atTop := hσ.comp hφ.tendsto_atTop
  have hev : ∀ᶠ k in atTop, max (max s₀ s₁) 1 ≤ σ (φ k) := hτ.eventually_ge_atTop _
  set F : ℕ → ℝ := fun k => ∫ x in (0:ℝ)..1, ‖ζ (σ (φ k), x)‖ ^ 2 with hF
  set f' : ℕ → ℝ → CauchyRiemannIndex.Vec n := fun k t =>
    (Real.sqrt (F k))⁻¹ • deriv (fun x => ζ (σ (φ k), x)) t with hf'
  refine tendstoUniformly_of_tendsto_intervalIntegral_sq
    (fun k t => (Real.sqrt (F k))⁻¹ • ζ (σ (φ k), t)) f' ?_ ?_ ?_ e he.1.continuous he.2.1 M
    ?_ hconv
  · filter_upwards [hev] with k hk t
    have hs : 0 < σ (φ k) := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hk)
    have hd := ((hslice _ hs).differentiable (by simp)).differentiableAt (x := t)
    exact hd.hasDerivAt.const_smul ((Real.sqrt (F k))⁻¹)
  · filter_upwards [hev] with k hk
    have hs : 0 < σ (φ k) := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hk)
    exact ((hslice _ hs).continuous_deriv (by simp)).const_smul ((Real.sqrt (F k))⁻¹)
  · exact Eventually.of_forall fun k t => by simp only [hζ.2.1]
  · filter_upwards [hev] with k hk
    have hk₀ : s₀ ≤ σ (φ k) := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
    have hk₁ : s₁ ≤ σ (φ k) := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
    have hFpos : 0 < F k := hpos _ hk₀
    have hb := hM _ hk₁
    have hsq : (Real.sqrt (F k))⁻¹ ^ 2 = (F k)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hFpos.le]
    calc ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2
        = (F k)⁻¹ * ∫ t in (0:ℝ)..1, ‖deriv (fun x => ζ (σ (φ k), x)) t‖ ^ 2 := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun t _ => ?_
          simp only [hf', norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hsq]
      _ ≤ (F k)⁻¹ * (M * F k) := by gcongr
      _ = M := by field_simp

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ s₀ : ℝ, (∀ s ≥ s₀, 0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) ∧
      ∀ σ : ℕ → ℝ, Tendsto σ atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
          TendstoUniformly (fun (k : ℕ) (t : ℝ) =>
            (Real.sqrt (∫ x in (0:ℝ)..1, ‖ζ (σ (φ k), x)‖ ^ 2))⁻¹ • ζ (σ (φ k), t)) e atTop :=
  FiniteEnergyPlane.halfCyl_exists_subseq_tendsto_eigen_aux S hS hSper Sinf hSinf hSinf' hSas ζ hζ hne C δ₀ hgrowth
