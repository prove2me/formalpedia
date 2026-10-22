-- Prove2me | solution 1 for BirkhoffGlobalSection.contact_winding_width_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T13:39:48.073511+00:00
-- url     : https://prove2.me/submissions/0593e730-4320-4432-a955-c2e9640ba853

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_interval_bundle
import Mathlib.Algebra.Ring.Periodic

open BirkhoffGlobalSection Set Topology

set_option maxHeartbeats 800000

set_option linter.unusedVariables false in
private theorem convex_model_contact_variation_joint_polar_lift : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase),
    ∃ ρ θ : ℝ × ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      ∀ x, convexModelContactVariationPath M q Z x.1 ![Real.cos x.2, Real.sin x.2] =
        ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)] := by
  exact BirkhoffGlobalSection.contact_winding_interval_bundle.2.2.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem plane_family_winding_interval : ∀ (θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (T : ℝ),
    ∃ a b : ℝ, a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = a) ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = b) := by
  exact BirkhoffGlobalSection.contact_winding_interval_bundle.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem winding_image_lower_rule_threshold_iff : ∀ (d : ℝ → ℝ) (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b),
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔
      ∀ s ∈ Icc 0 (2 * Real.pi), (k : ℝ) < d s := by
  exact BirkhoffGlobalSection.contact_winding_interval_bundle.2.2.2.2.2.2.2.2.2

/-- A continuous angle gap cannot leave its initial half-turn sector without
meeting one of its two boundary angles. -/
private theorem continuous_angle_gap_trapped (g : ℝ → ℝ) (hg : Continuous g)
    (h0 : 0 < g 0) (hpi : g 0 < Real.pi)
    (hne0 : ∀ t, g t ≠ 0) (hnepi : ∀ t, g t ≠ Real.pi) :
    ∀ t, 0 < g t ∧ g t < Real.pi := by
  intro t
  constructor
  · by_contra! h
    obtain ⟨u, hu⟩ := intermediate_value_univ t 0 hg (show (0 : ℝ) ∈ Icc (g t) (g 0) from ⟨h, h0.le⟩)
    exact hne0 u hu
  · by_contra! h
    obtain ⟨u, hu⟩ := intermediate_value_univ 0 t hg
      (show Real.pi ∈ Icc (g 0) (g t) from ⟨hpi.le, h⟩)
    exact hnepi u hu

/-- Area preservation forces ordered directions initially separated by less
than pi to stay separated by an angle strictly between zero and pi. -/
private theorem area_preserving_polar_angle_gap (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (harea : ∀ t p r, A t p 0 * A t r 1 - A t p 1 * A t r 0 = p 0 * r 1 - p 1 * r 0)
    (s r : ℝ) (hsr : s < r) (hr : r - s < Real.pi) :
    ∀ t, 0 < θ (t, r) - θ (t, s) ∧ θ (t, r) - θ (t, s) < Real.pi := by
  have hs : Real.sin (r - s) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hsr) hr).ne'
  have he (t : ℝ) :
      ρ (t, s) * ρ (t, r) * Real.sin (θ (t, r) - θ (t, s)) = Real.sin (r - s) := by
    have h := harea t ![Real.cos s, Real.sin s] ![Real.cos r, Real.sin r]
    rw [hpolar, hpolar] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [Real.sin_sub, Real.sin_sub]
    nlinarith only [h]
  apply continuous_angle_gap_trapped
    (fun t => θ (t, r) - θ (t, s))
    ((hθ.comp (continuous_id.prodMk continuous_const)).sub
      (hθ.comp (continuous_id.prodMk continuous_const)))
  · simpa [hθ0] using sub_pos.mpr hsr
  · simpa [hθ0] using hr
  · intro t ht
    apply hs
    simpa [ht] using (he t).symm
  · intro t ht
    apply hs
    simpa [ht] using (he t).symm

/-- Linearity gives the pi-shift identity for the normalized angle, hence
pi-periodicity of winding increments. -/
private theorem linear_action_antipodal_angle (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hρ : ∀ x, 0 < ρ x)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (hneg : ∀ t p, A t (-p) = -(A t p)) :
    ∀ t s, θ (t, s + Real.pi) = θ (t, s) + Real.pi := by
  intro t s
  have hvec (u : ℝ) : A u ![Real.cos (s + Real.pi), Real.sin (s + Real.pi)] =
      ![ρ (u, s) * Real.cos (θ (u, s) + Real.pi),
        ρ (u, s) * Real.sin (θ (u, s) + Real.pi)] := by
    have he : (![Real.cos (s + Real.pi), Real.sin (s + Real.pi)] : Plane) =
        -![Real.cos s, Real.sin s] := by ext i; fin_cases i <;> simp
    rw [he, hneg, hpolar]
    ext i
    fin_cases i <;> simp
  have h := BirkhoffGlobalSection.contact_angular_lift_bundle.2.2.2.2.1
    (fun u => A u ![Real.cos (s + Real.pi), Real.sin (s + Real.pi)])
    (fun u => ρ (u, s + Real.pi)) (fun u => ρ (u, s))
    (fun u => θ (u, s + Real.pi)) (fun u => θ (u, s) + Real.pi)
    (hθ.comp (continuous_id.prodMk continuous_const))
    ((hθ.comp (continuous_id.prodMk continuous_const)).add continuous_const)
    (fun u => hρ _) (fun u => hρ _) (fun u => hpolar u _) hvec t
  rw [hθ0, hθ0] at h
  linarith

/-- Sector preservation and antipodal symmetry give a strict half-turn bound
for the difference of any two winding increments. -/
private theorem polar_action_winding_pair_bound (θ : ℝ × ℝ → ℝ)
    (hshift : ∀ t s, θ (t, s + Real.pi) = θ (t, s) + Real.pi)
    (hgap : ∀ s r, s < r → r - s < Real.pi →
      ∀ t, 0 < θ (t, r) - θ (t, s) ∧ θ (t, r) - θ (t, s) < Real.pi)
    (T s r : ℝ) :
    |((θ (T, r) - r) / (2 * Real.pi)) - ((θ (T, s) - s) / (2 * Real.pi))| < 1 / 2 := by
  let n : ℤ := Int.floor ((r - s) / Real.pi)
  let u : ℝ := r - n * Real.pi
  have hu0 : 0 ≤ u - s := by
    have h := Int.sub_floor_div_mul_nonneg (r - s) Real.pi_pos
    dsimp [u, n]
    linarith
  have hupi : u - s < Real.pi := by
    have h := Int.sub_floor_div_mul_lt (r - s) Real.pi_pos
    dsimp [u, n]
    linarith
  have hp : Function.Periodic (fun x => θ (T, x) - x) Real.pi := by
    intro x
    change θ (T, x + Real.pi) - (x + Real.pi) = θ (T, x) - x
    rw [hshift]
    ring
  have he : θ (T, u) - u = θ (T, r) - r := hp.sub_int_mul_eq n
  have hdiff : |(θ (T, u) - u) - (θ (T, s) - s)| < Real.pi := by
    rcases eq_or_lt_of_le hu0 with h | h
    · have hus : u = s := by linarith
      simp [hus, Real.pi_pos]
    · have hg := hgap s u (by linarith) hupi T
      rw [abs_lt]
      constructor <;> linarith
  rw [he] at hdiff
  rw [← sub_div, abs_div, abs_of_pos (show 0 < 2 * Real.pi by positivity),
    div_lt_iff₀ (show 0 < 2 * Real.pi by positivity)]
  nlinarith

/-- Attained extrema convert the pairwise strict half-turn estimate to a
strict width bound for the full closed winding interval. -/
private theorem winding_interval_width_of_pair_bound (d : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b)
    (hbound : ∀ s r, |d r - d s| < 1 / 2) : b - a < 1 / 2 := by
  have ha : a ∈ d '' Icc 0 (2 * Real.pi) := by rw [himage]; exact ⟨le_rfl, hab⟩
  have hb : b ∈ d '' Icc 0 (2 * Real.pi) := by rw [himage]; exact ⟨hab, le_rfl⟩
  obtain ⟨s, _, hs⟩ := ha
  obtain ⟨r, _, hr⟩ := hb
  have h := hbound s r
  rw [hs, hr, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h

/-- Every normalized positive polar lift of a linear area-preserving action
has a winding interval of width strictly below one half. -/
private theorem area_preserving_polar_winding_width (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hρ : ∀ x, 0 < ρ x)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (harea : ∀ t p r, A t p 0 * A t r 1 - A t p 1 * A t r 0 = p 0 * r 1 - p 1 * r 0)
    (hneg : ∀ t p, A t (-p) = -(A t p)) (T a b : ℝ) (hab : a ≤ b)
    (himage : (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b) :
    b - a < 1 / 2 := by
  apply winding_interval_width_of_pair_bound _ a b hab himage
  intro s r
  exact polar_action_winding_pair_bound θ
    (linear_action_antipodal_angle A ρ θ hθ hρ hθ0 hpolar hneg)
    (fun s r hsr hr => area_preserving_polar_angle_gap A ρ θ hθ hθ0 hpolar harea s r hsr hr)
    T s r

set_option linter.unusedVariables false in
private theorem model_area : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p r : Plane),
    convexModelContactVariationPath M q Z t p 0 * convexModelContactVariationPath M q Z t r 1 -
      convexModelContactVariationPath M q Z t p 1 * convexModelContactVariationPath M q Z t r 0 =
      p 0 * r 1 - p 1 * r 0 := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem model_linear : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (t : ℝ) (p r : Plane) (a b : ℝ),
    convexModelContactVariationPath M q Z t (a • p + b • r) =
      a • convexModelContactVariationPath M q Z t p + b • convexModelContactVariationPath M q Z t r := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.1

/-- The actual contact action supplies the narrow winding interval required
by the geometric integer rule, with no extra width hypothesis. -/
private theorem convex_model_contact_variation_narrow_winding_interval {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (T : ℝ) :
    ∃ (ρ θ : ℝ × ℝ → ℝ) (a b : ℝ), Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      (∀ x, convexModelContactVariationPath M q Z x.1 ![Real.cos x.2, Real.sin x.2] =
        ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)]) ∧
      a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      b - a < 1 / 2 ∧
      ((3 : ℤ) ≤ Int.ceil a + Int.ceil b - 1 ↔
        ∀ s ∈ Icc 0 (2 * Real.pi), 2 * Real.pi < θ (T, s) - s) := by
  obtain ⟨ρ, θ, hρ, hθ, hp, h0, hpolar⟩ :=
    convex_model_contact_variation_joint_polar_lift M q Z hs hq hZ hZ0
  obtain ⟨a, b, hab, himage, _, _⟩ := plane_family_winding_interval θ hθ T
  have hneg (t : ℝ) (p : Plane) :
      convexModelContactVariationPath M q Z t (-p) = -(convexModelContactVariationPath M q Z t p) := by
    simpa using model_linear M q Z t p 0 (-1) 0
  have hw := area_preserving_polar_winding_width (convexModelContactVariationPath M q Z)
    ρ θ hθ hp h0 (fun t s => hpolar (t, s)) (model_area M q Z hs hq hZ hZ0)
    hneg T a b hab himage
  refine ⟨ρ, θ, a, b, hρ, hθ, hp, h0, hpolar, hab, himage, hw, ?_⟩
  have hi := winding_image_lower_rule_threshold_iff
    (fun s => (θ (T, s) - s) / (2 * Real.pi)) a b 1 hab (by linarith) himage
  have hpi : 0 < 2 * Real.pi := by positivity
  simpa only [Int.cast_one, show (2 * 1 + 1 : ℤ) = 3 by norm_num,
    lt_div_iff₀ hpi, one_mul] using hi

set_option linter.unusedVariables false in
theorem solution :
(∀ (g : ℝ → ℝ) (hg : Continuous g)
    (h0 : 0 < g 0) (hpi : g 0 < Real.pi)
    (hne0 : ∀ t, g t ≠ 0) (hnepi : ∀ t, g t ≠ Real.pi),
    ∀ t, 0 < g t ∧ g t < Real.pi) ∧
(∀ (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (harea : ∀ t p r, A t p 0 * A t r 1 - A t p 1 * A t r 0 = p 0 * r 1 - p 1 * r 0)
    (s r : ℝ) (hsr : s < r) (hr : r - s < Real.pi),
    ∀ t, 0 < θ (t, r) - θ (t, s) ∧ θ (t, r) - θ (t, s) < Real.pi) ∧
(∀ (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hρ : ∀ x, 0 < ρ x)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (hneg : ∀ t p, A t (-p) = -(A t p)),
    ∀ t s, θ (t, s + Real.pi) = θ (t, s) + Real.pi) ∧
(∀ (θ : ℝ × ℝ → ℝ)
    (hshift : ∀ t s, θ (t, s + Real.pi) = θ (t, s) + Real.pi)
    (hgap : ∀ s r, s < r → r - s < Real.pi →
      ∀ t, 0 < θ (t, r) - θ (t, s) ∧ θ (t, r) - θ (t, s) < Real.pi)
    (T s r : ℝ),
    |((θ (T, r) - r) / (2 * Real.pi)) - ((θ (T, s) - s) / (2 * Real.pi))| < 1 / 2) ∧
(∀ (d : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b)
    (hbound : ∀ s r, |d r - d s| < 1 / 2),
    b - a < 1 / 2) ∧
(∀ (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hρ : ∀ x, 0 < ρ x)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (harea : ∀ t p r, A t p 0 * A t r 1 - A t p 1 * A t r 0 = p 0 * r 1 - p 1 * r 0)
    (hneg : ∀ t p, A t (-p) = -(A t p)) (T a b : ℝ) (hab : a ≤ b)
    (himage : (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b),
    b - a < 1 / 2) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (T : ℝ),
    ∃ (ρ θ : ℝ × ℝ → ℝ) (a b : ℝ), Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      (∀ x, convexModelContactVariationPath M q Z x.1 ![Real.cos x.2, Real.sin x.2] =
        ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)]) ∧
      a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      b - a < 1 / 2 ∧
      ((3 : ℤ) ≤ Int.ceil a + Int.ceil b - 1 ↔
        ∀ s ∈ Icc 0 (2 * Real.pi), 2 * Real.pi < θ (T, s) - s)) := by
  exact ⟨@continuous_angle_gap_trapped, ⟨@area_preserving_polar_angle_gap, ⟨@linear_action_antipodal_angle, ⟨@polar_action_winding_pair_bound, ⟨@winding_interval_width_of_pair_bound, ⟨@area_preserving_polar_winding_width, @convex_model_contact_variation_narrow_winding_interval⟩⟩⟩⟩⟩⟩
