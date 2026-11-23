-- Prove2me | solution 1 for FiniteEnergyPlane.injective_fderiv_proj_of_fastPlane_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T21:50:03.662124+00:00
-- url     : https://prove2.me/submissions/4e0af345-db3d-4b0d-a272-b14db1d219ea

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_immersion_transverse
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_fderiv_proj_eq_zero_iff
import Theorems.Thm_FiniteEnergyPlane_snd_eq_of_fderiv_eq_radial



/-! Transversality of a curve of leaves to a family of embedded fast planes. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem injective_fderiv_proj_of_fastPlane_family_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (r : ℝ) (f : ℂ × ℂ → V 1)
    (hf : ContDiffOn ℝ 1 f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hfinj : Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hdf : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p))
    (hslice : ∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
      IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ)))
    (I : Set ℝ) (hI : IsOpen I) (ζ τ : ℝ → ℂ) (hζ : DifferentiableOn ℝ ζ I)
    (hτ : DifferentiableOn ℝ τ I) (hτI : ∀ t ∈ I, τ t ∈ ball (0 : ℂ) r)
    (hfy : ∀ t ∈ I, f (ζ t, τ t) = y t) :
    ∀ t ∈ I, ∀ w : ℂ,
      Function.Injective (fderiv ℝ (fun p : ℝ × ℂ => proj H (f (p.2, τ p.1))) (t, w)) := by
  intro t ht w
  have hOo : IsOpen (Set.univ ×ˢ ball (0 : ℂ) r : Set (ℂ × ℂ)) := isOpen_univ.prod isOpen_ball
  have hdim : Module.finrank ℝ (ℂ × ℂ) = Module.finrank ℝ (V 1) := by
    rw [Module.finrank_prod, Complex.finrank_real_complex, Module.finrank_fin_fun]
  have hτt := hτI t ht
  obtain ⟨hu, huP, hue⟩ := hslice (τ t) hτt
  have hf0 : ∀ z, f (z, τ t) ≠ 0 := fun z => hu.1.2.1 z trivial
  have hmem : ∀ z, ((z, τ t) : ℂ × ℂ) ∈ (Set.univ ×ˢ ball (0 : ℂ) r : Set (ℂ × ℂ)) :=
    fun z => ⟨trivial, hτt⟩
  have hfd : ∀ z, HasFDerivAt f (fderiv ℝ f (z, τ t)) (z, τ t) := fun z =>
    ((hf.differentiableOn one_ne_zero).differentiableAt (hOo.mem_nhds (hmem z))).hasFDerivAt
  have hpd : ∀ z, HasFDerivAt (proj H) (fderiv ℝ (proj H) (f (z, τ t))) (f (z, τ t)) := fun z =>
    ((contDiffAt_aCoord_proj H hH _ (hf0 z)).2.differentiableAt (by simp)).hasFDerivAt
  -- derivative of the projected leaf
  have hleafd : ∀ z v : ℂ, fderiv ℝ (fun z => proj H (f (z, τ t))) z v =
      fderiv ℝ (proj H) (f (z, τ t)) (fderiv ℝ f (z, τ t) (v, 0)) := by
    intro z v
    have h1 : HasFDerivAt (fun z : ℂ => f (z, τ t)) _ z :=
      (hfd z).comp (f := fun z : ℂ => (z, τ t)) z (hasFDerivAt_prodMk_left z (τ t))
    have h2 : HasFDerivAt (fun z : ℂ => proj H (f (z, τ t))) _ z :=
      (hpd z).comp (f := fun z : ℂ => f (z, τ t)) z h1
    rw [h2.fderiv]
    simp
  have htrans := isFastPlane_immersion_transverse H hH J hJ _ hu
  -- surjectivity of `Df`
  have hsurj : ∀ z, Function.Surjective (fderiv ℝ f (z, τ t)) := fun z =>
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (fderiv ℝ f (z, τ t)).toLinearMap) hdim).1 (hdf _ (hmem z))
  obtain ⟨Δ, hΔ⟩ := hsurj w (f (w, τ t))
  obtain ⟨Δ', hΔ'⟩ := hsurj (ζ t) (f (ζ t, τ t))
  have hη : Δ.2 = Δ'.2 := snd_eq_of_fderiv_eq_radial H hH J hJ P hcz r f hf hfinj hdf hslice
    (τ t) hτt w (ζ t) Δ Δ' hΔ hΔ'
  -- derivative of the map
  have hτd : HasDerivAt τ (deriv τ t) t := (hτ.differentiableAt (hI.mem_nhds ht)).hasDerivAt
  have hζd : HasDerivAt ζ (deriv ζ t) t := (hζ.differentiableAt (hI.mem_nhds ht)).hasDerivAt
  have hinner : HasFDerivAt (fun p : ℝ × ℂ => (p.2, τ p.1))
      ((ContinuousLinearMap.snd ℝ ℝ ℂ).prod
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv τ t)).comp
          (ContinuousLinearMap.fst ℝ ℝ ℂ))) (t, w) :=
    hasFDerivAt_snd.prodMk
      (hτd.hasFDerivAt.comp (f := (Prod.fst : ℝ × ℂ → ℝ)) (t, w) hasFDerivAt_fst)
  have hm1 : HasFDerivAt (fun p : ℝ × ℂ => f (p.2, τ p.1)) _ (t, w) :=
    (hfd w).comp (f := fun p : ℝ × ℂ => (p.2, τ p.1)) (t, w) hinner
  have hm2 : HasFDerivAt (fun p : ℝ × ℂ => proj H (f (p.2, τ p.1))) _ (t, w) :=
    (hpd w).comp (f := fun p : ℝ × ℂ => f (p.2, τ p.1)) (t, w) hm1
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  rw [hm2.fderiv] at hv
  have hv' : fderiv ℝ (proj H) (f (w, τ t)) (fderiv ℝ f (w, τ t) (v.2, v.1 • deriv τ t)) = 0 := by
    simpa using hv
  obtain ⟨lam, hlam⟩ := (fderiv_proj_eq_zero_iff H hH _ (hf0 w) _).1 hv'
  have hker : (v.2, v.1 • deriv τ t) = lam • Δ := by
    refine hdf _ (hmem w) ?_
    rw [hlam, map_smul, hΔ]
  have hk1 : v.2 = lam • Δ.1 := congrArg Prod.fst hker
  have hk2 : v.1 • deriv τ t = lam • Δ.2 := congrArg Prod.snd hker
  by_cases hv1 : v.1 = 0
  · -- `δt = 0`
    rw [hv1, zero_smul] at hk2
    rcases smul_eq_zero.1 hk2.symm with h | h
    · rw [h, zero_smul] at hk1
      exact Prod.ext hv1 hk1
    · exfalso
      have hΔe : Δ = (Δ.1, 0) := Prod.ext rfl h
      have hΔ1 : Δ.1 ≠ 0 := by
        intro h1
        have : Δ = 0 := Prod.ext h1 h
        rw [this, map_zero] at hΔ
        exact hf0 w hΔ.symm
      refine htrans w Δ.1 hΔ1 0 ?_
      rw [hleafd, ← hΔe, hΔ, zero_smul]
      exact (fderiv_proj_eq_zero_iff H hH _ (hf0 w) _).2 ⟨1, (one_smul _ _).symm⟩
  · -- `δt ≠ 0`: the Reeb field would be tangent to the leaf at `y t`
    exfalso
    set μ := v.1⁻¹ * lam with hμ
    have hτμ : deriv τ t = μ • Δ'.2 := by
      rw [hμ, mul_smul, ← hη, ← hk2, smul_smul, inv_mul_cancel₀ hv1, one_smul]
    have hcurve : HasDerivAt (fun s => (ζ s, τ s)) (deriv ζ t, deriv τ t) t := hζd.prodMk hτd
    have h1 : HasDerivAt (fun s => f (ζ s, τ s)) (fderiv ℝ f (ζ t, τ t) (deriv ζ t, deriv τ t)) t :=
      (hfd (ζ t)).comp_hasDerivAt t hcurve
    have h2 : HasDerivAt (fun s => f (ζ s, τ s)) (reeb H (y t)) t := by
      refine (hy.2 t).congr_of_eventuallyEq ?_
      filter_upwards [hI.mem_nhds ht] with s hs using hfy s hs
    have h3 := h1.unique h2
    have hy0 : ∀ s, y s ≠ 0 := by
      intro s hs
      have h := hH.2.2 (y s) (hy.1 s)
      rw [hs, map_zero] at h
      exact lt_irrefl _ h
    have hprojy : ∀ s, proj H (y s) = y s := by
      intro s
      obtain ⟨r₀, hr₀, hr₀u⟩ := hH.2.1 (y s) (hy0 s)
      have hex : ∃ r : ℝ, 0 < r ∧ H (r • y s) = 1 := ⟨r₀, hr₀⟩
      have h1 : scaleToS H (y s) = 1 := by
        unfold scaleToS
        rw [dif_pos hex, hr₀u _ (Classical.choose_spec hex), hr₀u 1 ⟨one_pos, ?_⟩]
        rw [one_smul]; exact hy.1 s
      unfold proj
      rw [h1, one_smul]
    have hR : fderiv ℝ (proj H) (f (ζ t, τ t)) (reeb H (y t)) = reeb H (y t) := by
      have hp := hpd (ζ t)
      rw [hfy t ht] at hp ⊢
      have h4 : HasDerivAt (fun s => proj H (y s)) (fderiv ℝ (proj H) (y t) (reeb H (y t))) t :=
        hp.comp_hasDerivAt t (hy.2 t)
      rw [funext hprojy] at h4
      exact h4.unique (hy.2 t)
    have hRne : reeb H (y t) ≠ 0 := by
      intro h
      have h1 := (reeb_spec H hH (y t) (hy.1 t)).2.1
      rw [h] at h1
      simp [liouville, omega0, dot] at h1
    have hvec : (deriv ζ t, deriv τ t) = (deriv ζ t - μ • Δ'.1, (0 : ℂ)) + μ • Δ' := by
      refine Prod.ext ?_ ?_
      · simp
      · simp [hτμ]
    have hfin : fderiv ℝ (fun z => proj H (f (z, τ t))) (ζ t) (deriv ζ t - μ • Δ'.1) =
        reeb H (y t) := by
      rw [hleafd]
      have h5 : fderiv ℝ f (ζ t, τ t) (deriv ζ t - μ • Δ'.1, 0) =
          reeb H (y t) - μ • f (ζ t, τ t) := by
        rw [← h3, hvec, map_add, map_smul, hΔ', add_sub_cancel_right]
      rw [h5, map_sub, hR, (fderiv_proj_eq_zero_iff H hH _ (hf0 (ζ t)) _).2 ⟨μ, rfl⟩, sub_zero]
    by_cases hv0 : deriv ζ t - μ • Δ'.1 = 0
    · rw [hv0, map_zero] at hfin
      exact hRne hfin.symm
    · refine htrans (ζ t) _ hv0 1 ?_
      rw [hfin, one_smul, hfy t ht, hprojy]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (r : ℝ) (f : ℂ × ℂ → V 1)
    (hf : ContDiffOn ℝ 1 f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hfinj : Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hdf : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p))
    (hslice : ∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
      IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ)))
    (I : Set ℝ) (hI : IsOpen I) (ζ τ : ℝ → ℂ) (hζ : DifferentiableOn ℝ ζ I)
    (hτ : DifferentiableOn ℝ τ I) (hτI : ∀ t ∈ I, τ t ∈ ball (0 : ℂ) r)
    (hfy : ∀ t ∈ I, f (ζ t, τ t) = y t) :
    ∀ t ∈ I, ∀ w : ℂ,
      Function.Injective (fderiv ℝ (fun p : ℝ × ℂ => proj H (f (p.2, τ p.1))) (t, w)) :=
  injective_fderiv_proj_of_fastPlane_family_aux H hH J hJ P hcz y hy r f hf hfinj hdf hslice I hI ζ τ hζ hτ hτI hfy
