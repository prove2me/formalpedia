-- Prove2me | solution 1 for BirkhoffGlobalSection.contact_angular_lift_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:01:09.684376+00:00
-- url     : https://prove2.me/submissions/d1e9ebe1-4d69-4feb-9eea-806a9a8779a0

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology

set_option linter.unusedVariables false in
private theorem convex_model_contact_variation_path_ne_zero : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p : Plane) (hp : p ≠ 0),
    convexModelContactVariationPath M q Z t p ≠ 0 := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.2.2.2.2.2.2

/-- A nonvanishing continuous complex trajectory has a global continuous logarithm,
with any prescribed logarithm at the initial time. -/
private theorem complex_curve_log_lift (z : ℝ → ℂ) (hz : Continuous z)
    (hne : ∀ t, z t ≠ 0) (a : ℂ) (ha : Complex.exp a = z 0) :
    ∃ f : ℝ → ℂ, Continuous f ∧ f 0 = a ∧ ∀ t, Complex.exp (f t) = z t := by
  let g : C(ℝ, {z : ℂ // z ≠ 0}) := ⟨fun t => ⟨z t, hne t⟩, hz.subtype_mk _⟩
  obtain ⟨f, hf, _⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
    g 0 a (Subtype.ext ha)
  refine ⟨f, f.continuous, hf.1, ?_⟩
  intro t
  exact congrArg Subtype.val (congrFun hf.2 t)

/-- A nonzero planar curve has a positive continuous radius and a continuous
angle on the whole real time axis. -/
private theorem plane_curve_polar_lift (v : ℝ → Plane) (hv : Continuous v)
    (hne : ∀ t, v t ≠ 0) :
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ t, 0 < ρ t) ∧ ∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)] := by
  let z : ℝ → ℂ := fun t => ⟨v t 0, v t 1⟩
  have hz : Continuous z := by
    have h0 := Complex.continuous_ofReal.comp ((continuous_apply 0).comp hv)
    have h1 := Complex.continuous_ofReal.comp ((continuous_apply 1).comp hv)
    convert! h0.add (h1.mul_const Complex.I) using 1
    funext t
    apply Complex.ext <;> simp [z]
  have hn (t : ℝ) : z t ≠ 0 := by
    intro h
    apply hne t
    ext i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  obtain ⟨f, hf, _, he⟩ := complex_curve_log_lift z hz hn (Complex.log (z 0)) (Complex.exp_log (hn 0))
  refine ⟨fun t => Real.exp (f t).re, fun t => (f t).im,
    Real.continuous_exp.comp (Complex.continuous_re.comp hf),
    Complex.continuous_im.comp hf, fun t => Real.exp_pos _, ?_⟩
  intro t
  ext i
  fin_cases i
  · simpa [z, Complex.exp_re] using (congrArg Complex.re (he t)).symm
  · simpa [z, Complex.exp_im] using (congrArg Complex.im (he t)).symm

/-- Continuous angles with the same direction have equal increments, regardless
of the choice of their initial representative. -/
private theorem continuous_angle_increment_unique (θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hcos : ∀ t, Real.cos (θ t) = Real.cos (ψ t))
    (hsin : ∀ t, Real.sin (θ t) = Real.sin (ψ t)) :
    ∀ t, θ t - θ 0 = ψ t - ψ 0 := by
  have he (t : ℝ) : Circle.exp (θ t) = Circle.exp (ψ t) := by
    apply Subtype.ext
    apply Complex.ext <;> simp [Circle.coe_exp, Complex.exp_re, Complex.exp_im, hcos, hsin]
  have hl : (fun t => θ t) = (fun t => ψ t + (θ 0 - ψ 0)) := by
    apply Circle.isCoveringMap_exp.eq_of_comp_eq hθ
      (hψ.add continuous_const) (a := 0)
    · funext t
      simp only [Function.comp_apply, Pi.add_apply, Circle.exp_add, Circle.exp_sub]
      rw [← he t, ← he 0]
      simp
    · change θ 0 = ψ 0 + (θ 0 - ψ 0)
      ring
  intro t
  have ht := congrFun hl t
  linarith

/-- Positive polar descriptions of the same vector have the same radius and direction. -/
private theorem plane_positive_polar_unique (v : Plane) (ρ σ θ ψ : ℝ)
    (hρ : 0 < ρ) (hσ : 0 < σ)
    (hθ : v = ![ρ * Real.cos θ, ρ * Real.sin θ])
    (hψ : v = ![σ * Real.cos ψ, σ * Real.sin ψ]) :
    ρ = σ ∧ Real.cos θ = Real.cos ψ ∧ Real.sin θ = Real.sin ψ := by
  have h0 := congrFun (hθ.symm.trans hψ) 0
  have h1 := congrFun (hθ.symm.trans hψ) 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hnorm (r a : ℝ) : (r * Real.cos a)^2 + (r * Real.sin a)^2 = r^2 := by
    calc
      _ = r^2 * (Real.cos a ^ 2 + Real.sin a ^ 2) := by ring
      _ = r^2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have he : ρ^2 = σ^2 := by
    rw [← hnorm ρ θ, ← hnorm σ ψ, h0, h1]
  have hr : ρ = σ := by nlinarith
  refine ⟨hr, ?_, ?_⟩
  · rw [← hr] at h0
    exact mul_left_cancel₀ hρ.ne' h0
  · rw [← hr] at h1
    exact mul_left_cancel₀ hρ.ne' h1

/-- The angular increment of a nonzero trajectory does not depend on its positive polar lift. -/
private theorem plane_polar_increment_unique (v : ℝ → Plane) (ρ σ θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ t, 0 < ρ t) (hσ : ∀ t, 0 < σ t)
    (hvθ : ∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)])
    (hvψ : ∀ t, v t = ![σ t * Real.cos (ψ t), σ t * Real.sin (ψ t)]) :
    ∀ t, θ t - θ 0 = ψ t - ψ 0 := by
  have h := fun t => plane_positive_polar_unique (v t) (ρ t) (σ t) (θ t) (ψ t)
    (hρ t) (hσ t) (hvθ t) (hvψ t)
  exact continuous_angle_increment_unique θ ψ hθ hψ (fun t => (h t).2.1) (fun t => (h t).2.2)

/-- Actual supplied contact variations admit a continuous positive polar lift,
with continuity and nonvanishing derived from the variational hypotheses. -/
private theorem convex_model_contact_variation_polar_lift {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane) (hp : p ≠ 0) :
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      ∀ t, convexModelContactVariationPath M q Z t p =
        ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)] := by
  apply plane_curve_polar_lift
  · exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.2.2.1
      M q Z hs (continuous_iff_continuousAt.mpr (fun t => (hq t).continuousAt))
      (continuous_iff_continuousAt.mpr (fun t => (hZ t).continuousAt)) p
  · exact fun t => convex_model_contact_variation_path_ne_zero M q Z hs hq hZ hZ0 t p hp

/-- Any two continuous positive polar descriptions of a model variation have
the same angular increment, giving a well-defined rotation measurement. -/
private theorem convex_model_contact_variation_increment_unique {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (p : Plane) (ρ σ θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ t, 0 < ρ t) (hσ : ∀ t, 0 < σ t)
    (hvθ : ∀ t, convexModelContactVariationPath M q Z t p =
      ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)])
    (hvψ : ∀ t, convexModelContactVariationPath M q Z t p =
      ![σ t * Real.cos (ψ t), σ t * Real.sin (ψ t)]) :
    ∀ t, θ t - θ 0 = ψ t - ψ 0 :=
  plane_polar_increment_unique _ ρ σ θ ψ hθ hψ hρ hσ hvθ hvψ

/-- Once existence is established, a winding lower bound on every lift is
equivalent to the same lower bound on one continuous positive polar lift. -/
private theorem plane_curve_polar_bound_iff (v : ℝ → Plane) (hv : Continuous v)
    (hne : ∀ t, v t ≠ 0) (T L : ℝ) :
    (∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ v t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      L < θ T - θ 0) ↔
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      (∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧ L < θ T - θ 0 := by
  constructor
  · intro h
    obtain ⟨ρ, θ, hρ, hθ, hp, he⟩ := plane_curve_polar_lift v hv hne
    exact ⟨ρ, θ, hρ, hθ, hp, he, h θ hθ (fun t => ⟨ρ t, hp t, he t⟩)⟩
  · rintro ⟨ρ, θ, _, hθ, hp, he, hbound⟩ ψ hψ hpolar
    classical
    choose σ hσ hσeq using hpolar
    have hi := plane_polar_increment_unique v ρ σ θ ψ hθ hψ hp hσ he hσeq T
    rwa [← hi]


set_option linter.unusedVariables false in
theorem solution :
(∀ (z : ℝ → ℂ) (hz : Continuous z)
    (hne : ∀ t, z t ≠ 0) (a : ℂ) (ha : Complex.exp a = z 0),
    ∃ f : ℝ → ℂ, Continuous f ∧ f 0 = a ∧ ∀ t, Complex.exp (f t) = z t) ∧
(∀ (v : ℝ → Plane) (hv : Continuous v)
    (hne : ∀ t, v t ≠ 0),
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ t, 0 < ρ t) ∧ ∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧
(∀ (θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hcos : ∀ t, Real.cos (θ t) = Real.cos (ψ t))
    (hsin : ∀ t, Real.sin (θ t) = Real.sin (ψ t)),
    ∀ t, θ t - θ 0 = ψ t - ψ 0) ∧
(∀ (v : Plane) (ρ σ θ ψ : ℝ)
    (hρ : 0 < ρ) (hσ : 0 < σ)
    (hθ : v = ![ρ * Real.cos θ, ρ * Real.sin θ])
    (hψ : v = ![σ * Real.cos ψ, σ * Real.sin ψ]),
    ρ = σ ∧ Real.cos θ = Real.cos ψ ∧ Real.sin θ = Real.sin ψ) ∧
(∀ (v : ℝ → Plane) (ρ σ θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ t, 0 < ρ t) (hσ : ∀ t, 0 < σ t)
    (hvθ : ∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)])
    (hvψ : ∀ t, v t = ![σ t * Real.cos (ψ t), σ t * Real.sin (ψ t)]),
    ∀ t, θ t - θ 0 = ψ t - ψ 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane) (hp : p ≠ 0),
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      ∀ t, convexModelContactVariationPath M q Z t p =
        ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (p : Plane) (ρ σ θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ t, 0 < ρ t) (hσ : ∀ t, 0 < σ t)
    (hvθ : ∀ t, convexModelContactVariationPath M q Z t p =
      ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)])
    (hvψ : ∀ t, convexModelContactVariationPath M q Z t p =
      ![σ t * Real.cos (ψ t), σ t * Real.sin (ψ t)]),
    ∀ t, θ t - θ 0 = ψ t - ψ 0) ∧
(∀ (v : ℝ → Plane) (hv : Continuous v)
    (hne : ∀ t, v t ≠ 0) (T L : ℝ),
    (∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ v t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      L < θ T - θ 0) ↔
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      (∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧ L < θ T - θ 0) := by
  exact ⟨@complex_curve_log_lift, ⟨@plane_curve_polar_lift, ⟨@continuous_angle_increment_unique, ⟨@plane_positive_polar_unique, ⟨@plane_polar_increment_unique, ⟨@convex_model_contact_variation_polar_lift, ⟨@convex_model_contact_variation_increment_unique, @plane_curve_polar_bound_iff⟩⟩⟩⟩⟩⟩⟩
