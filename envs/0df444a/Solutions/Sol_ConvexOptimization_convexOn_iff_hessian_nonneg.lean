-- Prove2me | solution 1 for ConvexOptimization.convexOn_iff_hessian_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-15T14:35:04.647+00:00
-- url     : https://prove2.me/submissions/84724ac2-0c11-41b3-923d-ad718c64be74

import Mathlib

open Set
open scoped RealInnerProductSpace ENNReal

theorem solution {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiffOn ℝ 2 f Ω) :
    ConvexOn ℝ Ω f ↔
      ∀ x ∈ Ω, ∀ v : EuclideanSpace ℝ (Fin n),
        0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  constructor
  · intro hconv x hx v
    let E := EuclideanSpace ℝ (Fin n)
    let L : ℝ → E := fun t ↦ t • v + x
    let A : ℝ →ᵃ[ℝ] E :=
      { toFun := L
        linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight v
        map_vadd' := by intro p w; simp [L, add_smul]; module }
    let S : Set ℝ := A ⁻¹' Ω
    let g : ℝ → ℝ := f ∘ A
    let q : ℝ → ℝ := fun t ↦ fderiv ℝ f (A t) v
    have hA0 : A 0 = x := by simp [A, L]
    have h0 : (0 : ℝ) ∈ S := by simpa [S, hA0] using hx
    have hSopen : IsOpen S := hΩo.preimage A.continuous_of_finiteDimensional
    have hSconv : Convex ℝ S := hΩc.affine_preimage A
    have hgconv : ConvexOn ℝ S g := hconv.comp_affineMap A
    have hLderiv : ∀ t : ℝ, HasDerivAt A v t := by
      intro t
      exact (((hasDerivAt_id t).smul_const v).add_const x).congr_deriv (one_smul ℝ v)
    have hg' : ∀ t ∈ S, HasDerivAt g (q t) t := by
      intro t ht
      have hft : DifferentiableAt ℝ f (A t) :=
        (hf.contDiffAt (hΩo.mem_nhds ht)).differentiableAt (by norm_num)
      simpa [g, q, Function.comp_def] using hft.hasFDerivAt.comp_hasDerivAt t (hLderiv t)
    have hq' : HasDerivAt q (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
      have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt (hΩo.mem_nhds hx)
      have hdf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
        (hfx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
      have hdfA : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (A 0) := by
        simpa [hA0] using hdf
      have hcomp := hdfA.comp_hasDerivAt 0 (hLderiv 0)
      have heval := ((ContinuousLinearMap.apply ℝ ℝ) v).hasFDerivAt.comp_hasDerivAt 0 hcomp
      simpa [q, hA0, Function.comp_def] using heval
    have hmonoDeriv : MonotoneOn (deriv g) S :=
      hgconv.monotoneOn_deriv fun t ht ↦ (hg' t ht).differentiableAt
    have hmonoQ : MonotoneOn q S := by
      intro a ha b hb hab
      simpa [(hg' a ha).deriv, (hg' b hb).deriv] using hmonoDeriv ha hb hab
    have hacc : AccPt (0 : ℝ) (Filter.principal S) := by
      rw [accPt_principal_iff_nhdsWithin]
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hSopen 0 h0
      apply (left_nhdsWithin_Ioo_neBot hε).mono
      apply nhdsWithin_mono 0
      intro t ht
      refine ⟨hball ?_, ?_⟩
      · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
        exact ht.2
      · simpa using ht.1.ne'
    exact hq'.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmonoQ
  · intro hessian
    refine ⟨hΩc, ?_⟩
    intro x hx y hy a b ha hb hab
    let E := EuclideanSpace ℝ (Fin n)
    let d : E := y - x
    let L : ℝ → E := fun t ↦ t • d + x
    let g : ℝ → ℝ := f ∘ L
    let q : ℝ → ℝ := fun t ↦ fderiv ℝ f (L t) d
    let r : ℝ → ℝ := fun t ↦ fderiv ℝ (fderiv ℝ f) (L t) d d
    have hLderiv : ∀ t : ℝ, HasDerivAt L d t := by
      intro t
      exact (((hasDerivAt_id t).smul_const d).add_const x).congr_deriv (one_smul ℝ d)
    have hLmem : ∀ t ∈ Icc (0 : ℝ) 1, L t ∈ Ω := by
      intro t ht
      rw [show L t = (1 - t) • x + t • y by simp [L, d]; module]
      exact hΩc hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have hg' : ∀ t ∈ interior (Icc (0 : ℝ) 1), HasDerivAt g (q t) t := by
      intro t ht
      have htm : L t ∈ Ω := hLmem t (interior_subset ht)
      have hft : DifferentiableAt ℝ f (L t) :=
        (hf.contDiffAt (hΩo.mem_nhds htm)).differentiableAt (by norm_num)
      simpa [g, q, Function.comp_def] using hft.hasFDerivAt.comp_hasDerivAt t (hLderiv t)
    have hq' : ∀ t ∈ interior (Icc (0 : ℝ) 1), HasDerivAt q (r t) t := by
      intro t ht
      have htm : L t ∈ Ω := hLmem t (interior_subset ht)
      have hft : ContDiffAt ℝ 2 f (L t) := hf.contDiffAt (hΩo.mem_nhds htm)
      have hdf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (L t)) (L t) :=
        (hft.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
      have hcomp := hdf.comp_hasDerivAt t (hLderiv t)
      have heval := ((ContinuousLinearMap.apply ℝ ℝ) d).hasFDerivAt.comp_hasDerivAt t hcomp
      simpa [q, r, Function.comp_def] using heval
    have hgcont : ContinuousOn g (Icc (0 : ℝ) 1) := by
      intro t ht
      have htm : L t ∈ Ω := hLmem t ht
      have hft : ContinuousAt f (L t) :=
        (hf.contDiffAt (hΩo.mem_nhds htm)).continuousAt
      show ContinuousWithinAt g (Icc (0 : ℝ) 1) t
      simpa [g] using
        ((hft.comp (hLderiv t).continuousAt).continuousWithinAt :
          ContinuousWithinAt (f ∘ L) (Icc (0 : ℝ) 1) t)
    have hgconv : ConvexOn ℝ (Icc (0 : ℝ) 1) g := by
      apply convexOn_of_hasDerivWithinAt2_nonneg (D := Icc (0 : ℝ) 1)
        (convex_Icc (0 : ℝ) 1) hgcont
      · exact fun t ht ↦ (hg' t ht).hasDerivWithinAt
      · exact fun t ht ↦ (hq' t ht).hasDerivWithinAt
      · intro t ht
        exact hessian (L t) (hLmem t (interior_subset ht)) d
    have hline := hgconv.2 (mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
      (mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) ha hb hab
    have hL0 : L 0 = x := by simp [L]
    have hL1 : L 1 = y := by simp [L, d]
    have hLb : L b = a • x + b • y := by
      rw [show L b = b • (y - x) + x by rfl]
      have ha' : 1 - b = a := by linarith
      rw [← ha']
      module
    simpa [g, hL0, hL1, hLb] using hline
