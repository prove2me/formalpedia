-- Prove2me | solution 1 for FiniteEnergyPlane.snd_eq_of_fderiv_eq_radial
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T21:30:24.560906+00:00
-- url     : https://prove2.me/submissions/47f88c04-abed-43fc-ad27-1db1b2f291c4

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_range_eq_or_disjoint_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_shiftA_comp_affine_of_range_eq
import Theorems.Thm_FiniteEnergyPlane_proj_not_mem_range_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_injective_proj_of_isEmbeddedPlane
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_lift_of_injective_fderiv



/-! Transversality of a curve of leaves to a family of embedded fast planes. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The parameter component of the pulled back radial field is constant along the leaves. -/
theorem snd_eq_of_fderiv_eq_radial_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (r : ℝ) (f : ℂ × ℂ → V 1)
    (hf : ContDiffOn ℝ 1 f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hfinj : Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hdf : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p))
    (hslice : ∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
      IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ)))
    (τ : ℂ) (hτ : τ ∈ ball (0 : ℂ) r) (w w' : ℂ) (Δ Δ' : ℂ × ℂ)
    (hΔ : fderiv ℝ f (w, τ) Δ = f (w, τ)) (hΔ' : fderiv ℝ f (w', τ) Δ' = f (w', τ)) :
    Δ.2 = Δ'.2 := by
  have hOo : IsOpen (Set.univ ×ˢ ball (0 : ℂ) r : Set (ℂ × ℂ)) := isOpen_univ.prod isOpen_ball
  have hdim : Module.finrank ℝ (ℂ × ℂ) = Module.finrank ℝ (V 1) := by
    rw [Module.finrank_prod, Complex.finrank_real_complex, Module.finrank_fin_fun]
  have hf0 : ∀ z, ∀ σ ∈ ball (0 : ℂ) r, f (z, σ) ≠ 0 := fun z σ hσ =>
    (hslice σ hσ).1.1.2.1 z trivial
  -- the lift of the radial curve
  have hlift : ∀ (w : ℂ) (Δ : ℂ × ℂ), fderiv ℝ f (w, τ) Δ = f (w, τ) →
      ∃ ε > 0, ∃ c : ℝ → ℂ × ℂ, HasDerivAt c ((2 : ℝ) • Δ) 0 ∧ ∀ s ∈ ball (0 : ℝ) ε,
        (c s).2 ∈ ball (0 : ℂ) r ∧ f (c s) = Real.exp (2 * s) • f (w, τ) := by
    intro w Δ hΔ
    have hp : ((w, τ) : ℂ × ℂ) ∈ (Set.univ ×ˢ ball (0 : ℂ) r : Set (ℂ × ℂ)) := ⟨trivial, hτ⟩
    have hg : ContDiffOn ℝ 1 (fun s : ℝ => Real.exp (2 * s) • f (w, τ)) (ball (0 : ℝ) 1) := by
      fun_prop
    obtain ⟨ε, hε, c, hc, hc0, hcO⟩ := exists_contDiffOn_lift_of_injective_fderiv hdim
      (n := 1) le_rfl hOo (by exact_mod_cast hf) hp (hdf _ hp) (t₀ := (0 : ℝ)) one_pos
      (by exact_mod_cast hg) (by simp)
    refine ⟨ε, hε, c, ?_, fun s hs => ⟨(hcO s hs).1.2, (hcO s hs).2⟩⟩
    have hcd : HasDerivAt c (deriv c 0) 0 :=
      ((hc.differentiableOn (by simp)).differentiableAt (ball_mem_nhds 0 hε)).hasDerivAt
    have hfd : HasFDerivAt f (fderiv ℝ f (w, τ)) (c 0) := by
      rw [hc0]
      exact ((hf.differentiableOn one_ne_zero).differentiableAt (hOo.mem_nhds hp)).hasFDerivAt
    have h1 : HasDerivAt (fun s => f (c s)) (fderiv ℝ f (w, τ) (deriv c 0)) 0 :=
      hfd.comp_hasDerivAt (0 : ℝ) hcd
    have hcurve : HasDerivAt (fun s : ℝ => Real.exp (2 * s) • f (w, τ)) ((2 : ℝ) • f (w, τ)) 0 := by
      have h1 : HasDerivAt (fun c : ℝ => Real.exp (2 * c)) 2 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).const_mul 2).exp
        simpa using this
      exact h1.smul_const _
    have h2 : HasDerivAt (fun s => f (c s)) ((2 : ℝ) • f (w, τ)) 0 := by
      refine hcurve.congr_of_eventuallyEq ?_
      filter_upwards [ball_mem_nhds (0 : ℝ) hε] with s hs using (hcO s hs).2
    have h3 : deriv c 0 = (2 : ℝ) • Δ := by
      refine hdf _ hp ?_
      rw [h1.unique h2, map_smul, hΔ]
    rwa [h3] at hcd
  -- the leaf through `c s` is the translated leaf
  have hleaf : ∀ (w₁ : ℂ) (p : ℂ × ℂ) (s : ℝ), p.2 ∈ ball (0 : ℂ) r →
      f p = Real.exp (2 * s) • f (w₁, τ) →
      ∀ z, ∃ z', f (z', p.2) = Real.exp (2 * s) • f (z, τ) := by
    intro w₁ p s hp hfp z
    obtain ⟨hu, huP, hue⟩ := hslice τ hτ
    obtain ⟨hv, hvP, hve⟩ := hslice p.2 hp
    have humiss := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz _ hu huP hue
    have hvmiss := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz _ hv hvP hve
    have hpe : proj H (f (p.1, p.2)) = proj H (f (w₁, τ)) := by
      show proj H (f p) = _
      rw [hfp]
      exact (proj_aCoord_exp_smul H hH s _ (hf0 w₁ τ hτ)).1
    have hrange : Set.range (proj H ∘ fun z => f (z, p.2)) =
        Set.range (proj H ∘ fun z => f (z, τ)) := by
      rcases range_eq_or_disjoint_of_isFastPlane H hH J hJ P _ _ hv hvP hve hu huP hue
        hvmiss humiss with h | h
      · exact h
      · exact absurd h (Set.not_disjoint_iff.2 ⟨_, ⟨p.1, rfl⟩, ⟨w₁, hpe.symm⟩⟩)
    obtain ⟨c, A, B, hA, hAB⟩ := exists_shiftA_comp_affine_of_range_eq H hH J hJ P hcz _ _
      hv hvP hve hu huP hue hrange
    have hAB' : ∀ z, f (A * z + B, p.2) = Real.exp (2 * c) • f (z, τ) := hAB
    have hcs : c = s := by
      have hx := hAB' ((p.1 - B) / A)
      rw [mul_div_cancel₀ _ hA, sub_add_cancel] at hx
      have h1 : f p = Real.exp (2 * c) • f ((p.1 - B) / A, τ) := hx
      have h2 : proj H (f ((p.1 - B) / A, τ)) = proj H (f (w₁, τ)) := by
        rw [← hpe, hx]
        exact ((proj_aCoord_exp_smul H hH c _ (hf0 _ τ hτ)).1).symm
      have h3 : (p.1 - B) / A = w₁ := injective_proj_of_isEmbeddedPlane H hH J hJ P _ hu huP hue h2
      rw [h3, hfp] at h1
      have h4 := smul_left_injective ℝ (hf0 w₁ τ hτ) h1
      have h5 := Real.exp_injective h4
      linarith
    exact ⟨A * z + B, by rw [hAB', hcs]⟩
  obtain ⟨ε, hε, c, hc, hcs⟩ := hlift w Δ hΔ
  obtain ⟨ε', hε', c', hc', hcs'⟩ := hlift w' Δ' hΔ'
  have heq : (fun s => (c s).2) =ᶠ[𝓝 0] fun s => (c' s).2 := by
    filter_upwards [ball_mem_nhds (0 : ℝ) hε, ball_mem_nhds (0 : ℝ) hε'] with s hs hs'
    obtain ⟨a, ha⟩ := hleaf w (c s) s (hcs s hs).1 (hcs s hs).2 0
    obtain ⟨b, hb⟩ := hleaf w' (c' s) s (hcs' s hs').1 (hcs' s hs').2 0
    have hm1 : ((a, (c s).2) : ℂ × ℂ) ∈ (Set.univ ×ˢ ball (0 : ℂ) r : Set (ℂ × ℂ)) :=
      ⟨trivial, (hcs s hs).1⟩
    have hm2 : ((b, (c' s).2) : ℂ × ℂ) ∈ (Set.univ ×ˢ ball (0 : ℂ) r : Set (ℂ × ℂ)) :=
      ⟨trivial, (hcs' s hs').1⟩
    have := hfinj hm1 hm2 (ha.trans hb.symm)
    exact (Prod.ext_iff.1 this).2
  have hd : HasDerivAt (fun s => (c s).2) ((2 : ℝ) • Δ).2 0 :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hd' : HasDerivAt (fun s => (c' s).2) ((2 : ℝ) • Δ').2 0 :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc'
  have h := hd.unique (hd'.congr_of_eventuallyEq heq)
  exact smul_right_injective ℂ (two_ne_zero (α := ℝ)) h

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (r : ℝ) (f : ℂ × ℂ → V 1)
    (hf : ContDiffOn ℝ 1 f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hfinj : Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hdf : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p))
    (hslice : ∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
      IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ)))
    (τ : ℂ) (hτ : τ ∈ ball (0 : ℂ) r) (w w' : ℂ) (Δ Δ' : ℂ × ℂ)
    (hΔ : fderiv ℝ f (w, τ) Δ = f (w, τ)) (hΔ' : fderiv ℝ f (w', τ) Δ' = f (w', τ)) :
    Δ.2 = Δ'.2 :=
  snd_eq_of_fderiv_eq_radial_aux H hH J hJ P hcz r f hf hfinj hdf hslice τ hτ w w' Δ Δ' hΔ hΔ'
