-- Prove2me | solution 1 for EntropicBarrier.Universal.lemma5_nConcave_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:47:59.695995+00:00
-- url     : https://prove2.me/submissions/fe182471-11ee-44a8-bc31-2df7527b3a6b

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_Marginal

open scoped RealInnerProductSpace
open MeasureTheory

namespace P4c441f4f

lemma concave_iff_deriv2 {U : Set ℝ} (hU : IsOpen U) (hc : Convex ℝ U) {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f U) (hf' : DifferentiableOn ℝ (deriv f) U) :
    ConcaveOn ℝ U f ↔ ∀ x ∈ U, deriv (deriv f) x ≤ 0 := by
  constructor
  · intro h x hx
    have hanti := h.antitoneOn_deriv (fun y hy => (hf y hy).differentiableAt (hU.mem_nhds hy))
    have h1 : derivWithin (deriv f) U x ≤ 0 := hanti.derivWithin_nonpos
    rwa [derivWithin_of_isOpen hU hx] at h1
  · intro h
    exact concaveOn_of_deriv2_nonpos' hc hf hf' (fun x hx => by simpa using h x hx)

end P4c441f4f

open EntropicBarrier.Universal in
theorem solution (n a b : ℝ) (hn : 0 < n) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ 2 φ (Set.Ioo a b)) (hpos : ∀ x ∈ Set.Ioo a b, 0 < φ x) :
    IsNConcaveOn n (Set.Ioo a b) φ ↔
      ∀ x ∈ Set.Ioo a b,
        deriv (deriv (fun t => Real.log (φ t))) x ≤
          -(1 / n) * (deriv (fun t => Real.log (φ t)) x) ^ 2 := by
  set U := Set.Ioo a b with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have hcv : Convex ℝ U := convex_Ioo a b
  set ζ : ℝ → ℝ := fun t => Real.log (φ t) with hζdef
  set g : ℝ → ℝ := fun t => Real.exp (ζ t * (1 / n)) with hgdef
  have hζ : ContDiffOn ℝ 2 ζ U := hφ.log (fun x hx => (hpos x hx).ne')
  have hg : ContDiffOn ℝ 2 g U := (hζ.mul contDiffOn_const).exp
  have hζd : DifferentiableOn ℝ ζ U := hζ.differentiableOn (by norm_num)
  have hζd' : DifferentiableOn ℝ (deriv ζ) U :=
    (hζ.deriv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num)
  have hgd : DifferentiableOn ℝ g U := hg.differentiableOn (by norm_num)
  have hgd' : DifferentiableOn ℝ (deriv g) U :=
    (hg.deriv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num)
  have hEq : Set.EqOn g (fun x => φ x ^ (1 / n)) U := by
    intro x hx
    simp only [hgdef, hζdef]
    rw [Real.rpow_def_of_pos (hpos x hx)]
  have hderg : ∀ y ∈ U, HasDerivAt g (g y * (deriv ζ y * (1 / n))) y := by
    intro y hy
    have h1 : HasDerivAt ζ (deriv ζ y) y := ((hζd y hy).differentiableAt (hU.mem_nhds hy)).hasDerivAt
    exact (h1.mul_const (1 / n)).exp
  have hkey : ∀ x ∈ U, deriv (deriv g) x =
      g x * (1 / n) * (deriv (deriv ζ) x + (1 / n) * (deriv ζ x) ^ 2) := by
    intro x hx
    have hev : deriv g =ᶠ[nhds x] fun y => g y * (deriv ζ y * (1 / n)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (hderg y hy).deriv
    rw [hev.deriv_eq]
    have h2 : HasDerivAt (deriv ζ) (deriv (deriv ζ) x) x :=
      ((hζd' x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
    have h3 : HasDerivAt (fun y => g y * (deriv ζ y * (1 / n)))
        (g x * (deriv ζ x * (1 / n)) * (deriv ζ x * (1 / n)) + g x * (deriv (deriv ζ) x * (1 / n))) x :=
      (hderg x hx).mul (h2.mul_const (1 / n))
    rw [h3.deriv]
    ring
  have hconc : IsNConcaveOn n U φ ↔ ConcaveOn ℝ U g := by
    unfold IsNConcaveOn
    exact ⟨fun h => h.congr hEq.symm, fun h => h.congr hEq⟩
  rw [hconc, P4c441f4f.concave_iff_deriv2 hU hcv hgd hgd']
  apply forall₂_congr
  intro x hx
  rw [hkey x hx]
  have hgpos : 0 < g x * (1 / n) := mul_pos (Real.exp_pos _) (by positivity)
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have : 0 < deriv (deriv ζ) x + 1 / n * deriv ζ x ^ 2 := by linarith
    have := mul_pos hgpos this
    linarith
  · intro h
    have : deriv (deriv ζ) x + 1 / n * deriv ζ x ^ 2 ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hgpos.le this
