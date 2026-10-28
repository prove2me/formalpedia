-- Prove2me | solution 1 for FunctionalInequalities.Analysis.support_of_max_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:28.798183+00:00
-- url     : https://prove2.me/submissions/bb7a02ff-11ee-4a75-a6c8-56a282adb62a

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT12ASubgradientImageMonotone
open Set
open scoped Topology
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 lemma solution
    {u : E → ℝ} {Ω : Set E} (hu : ConvexOn ℝ univ u) (hΩ : IsOpen Ω)
    (x₀ x₁ p : E) (c : ℝ) (hx₁ : x₁ ∈ Ω)
    (hmax :
      IsMaxOn (fun z => c + ⟪p, z - x₀⟫ - u z) (closure Ω) x₁) :
    ∀ y, u x₁ + ⟪p, y - x₁⟫ ≤ u y := by
  let ell : E → ℝ := fun z => c + ⟪p, z - x₀⟫
  let a : ℝ := ell x₁ - u x₁
  let f : E → ℝ := fun z => u z - ell z + a
  have hell :
      ∀ (x y : E) (α β : ℝ), α + β = 1 →
        ell (α • x + β • y) = α • ell x + β • ell y := by
    intro x y α β hab
    dsimp [ell]
    have harg :
        α • x + β • y - x₀ = α • (x - x₀) + β • (y - x₀) := by
      calc
        α • x + β • y - x₀ =
            α • x + β • y - (α + β) • x₀ := by
              rw [hab, one_smul]
        _ = α • (x - x₀) + β • (y - x₀) := by
          rw [add_smul, smul_sub, smul_sub]
          abel
    rw [harg, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    change c + (α * ⟪p, x - x₀⟫ + β * ⟪p, y - x₀⟫) =
      α * (c + ⟪p, x - x₀⟫) + β * (c + ⟪p, y - x₀⟫)
    calc
      c + (α * ⟪p, x - x₀⟫ + β * ⟪p, y - x₀⟫) =
          (α + β) * c +
            (α * ⟪p, x - x₀⟫ + β * ⟪p, y - x₀⟫) := by
              simp [hab]
      _ = α * (c + ⟪p, x - x₀⟫) +
            β * (c + ⟪p, y - x₀⟫) := by ring
  have hfconv : ConvexOn ℝ univ f := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β hα hβ hab
    have h := hu.2 (show x ∈ (univ : Set E) by simp)
      (show y ∈ (univ : Set E) by simp) hα hβ hab
    have h' : u (α • x + β • y) ≤ α * u x + β * u y := by
      simpa only [smul_eq_mul] using h
    calc
      f (α • x + β • y) =
          u (α • x + β • y) - (α * ell x + β * ell y) + a := by
            simp only [f, hell x y α β hab, smul_eq_mul]
      _ ≤ (α * u x + β * u y) - (α * ell x + β * ell y) + a := by
            linarith
      _ = α • f x + β • f y := by
            change
              (α * u x + β * u y) - (α * ell x + β * ell y) + a =
                α * (u x - ell x + a) + β * (u y - ell y + a)
            calc
              (α * u x + β * u y) - (α * ell x + β * ell y) + a =
                  α * (u x - ell x) + β * (u y - ell y) + (α + β) * a := by
                    simp [hab]
                    ring
              _ = α * (u x - ell x + a) + β * (u y - ell y + a) := by
                    ring
  have hnonneg : ∀ z ∈ Ω, 0 ≤ f z := by
    intro z hz
    have hzmax := hmax (subset_closure hz)
    dsimp [f, a, ell] at hzmax ⊢
    linarith
  have hxzero : f x₁ = 0 := by
    dsimp [f, a]
    ring
  intro y
  have hfy : 0 ≤ f y := by
    by_contra hy
    have hy' : f y < 0 := lt_of_not_ge hy
    have hpre :
        (AffineMap.lineMap x₁ y) ⁻¹' Ω ∈ 𝓝 (0 : ℝ) :=
      (AffineMap.lineMap_continuous (p := x₁) (q := y)).continuousAt.preimage_mem_nhds
        (hΩ.mem_nhds (show AffineMap.lineMap x₁ y 0 ∈ Ω by
          rw [AffineMap.lineMap_apply_zero]
          exact hx₁))
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
    let t : ℝ := min (ε / 2) (1 / 2)
    have ht : 0 < t := by
      dsimp [t]
      exact lt_min (by linarith) (by norm_num)
    have htε : t < ε := by
      dsimp [t]
      exact (min_le_left _ _).trans_lt (by linarith)
    have ht1 : t < 1 := by
      dsimp [t]
      exact (min_le_right _ _).trans_lt (by norm_num)
    have htΩ : AffineMap.lineMap x₁ y t ∈ Ω := by
      apply hεsub
      have hdist : dist t 0 < ε := by
        rw [Real.dist_eq]
        simpa [abs_of_pos ht] using htε
      exact hdist
    let z : E := AffineMap.lineMap x₁ y t
    have hzΩ : z ∈ Ω := by
      simpa [z] using htΩ
    have hzseg : z ∈ openSegment ℝ x₁ y := by
      exact lineMap_mem_openSegment ℝ x₁ y ⟨ht, ht1⟩
    have hxz : f x₁ ≤ f z := by
      simpa [hxzero] using hnonneg z hzΩ
    have hzy : f z ≤ f y :=
      hfconv.le_right_of_left_le
        (x := x₁) (y := y) (z := z)
        (show x₁ ∈ (univ : Set E) by simp)
        (show y ∈ (univ : Set E) by simp)
        hzseg hxz
    exact (not_lt_of_ge (hnonneg z hzΩ)) (lt_of_le_of_lt hzy hy')
  have helldiff : ell y - ell x₁ = ⟪p, y - x₁⟫ := by
    dsimp [ell]
    simp only [inner_sub_right]
    ring
  dsimp [f, a] at hfy
  linarith [helldiff]
