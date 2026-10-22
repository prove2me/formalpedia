-- Prove2me | solution 1 for BirkhoffGlobalSection.contact_winding_interval_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T13:13:34.972997+00:00
-- url     : https://prove2.me/submissions/ddf09fa3-b50b-443c-be29-b5a155214a12

import Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology

set_option maxHeartbeats 800000

private theorem polar_unique (v : Plane) (ρ σ θ ψ : ℝ)
    (hρ : 0 < ρ) (hσ : 0 < σ)
    (hθ : v = ![ρ * Real.cos θ, ρ * Real.sin θ])
    (hψ : v = ![σ * Real.cos ψ, σ * Real.sin ψ]) :
    ρ = σ ∧ Real.cos θ = Real.cos ψ ∧ Real.sin θ = Real.sin ψ :=
  BirkhoffGlobalSection.contact_angular_lift_bundle.2.2.2.1 v ρ σ θ ψ hρ hσ hθ hψ

private theorem angle_increment_unique (θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hcos : ∀ t, Real.cos (θ t) = Real.cos (ψ t))
    (hsin : ∀ t, Real.sin (θ t) = Real.sin (ψ t)) :
    ∀ t, θ t - θ 0 = ψ t - ψ 0 :=
  BirkhoffGlobalSection.contact_angular_lift_bundle.2.2.1 θ ψ hθ hψ hcos hsin

private theorem polar_increment_unique (v : ℝ → Plane) (ρ σ θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ t, 0 < ρ t) (hσ : ∀ t, 0 < σ t)
    (hvθ : ∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)])
    (hvψ : ∀ t, v t = ![σ t * Real.cos (ψ t), σ t * Real.sin (ψ t)]) :
    ∀ t, θ t - θ 0 = ψ t - ψ 0 :=
  BirkhoffGlobalSection.contact_angular_lift_bundle.2.2.2.2.1 v ρ σ θ ψ hθ hψ hρ hσ hvθ hvψ

set_option linter.unusedVariables false in
private theorem model_path_linear : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (t : ℝ) (p r : Plane) (a b : ℝ),
    convexModelContactVariationPath M q Z t (a • p + b • r) =
      a • convexModelContactVariationPath M q Z t p +
        b • convexModelContactVariationPath M q Z t r := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem model_path_initial : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : q 0 ∈ unitThreeSphere)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane),
    convexModelContactVariationPath M q Z 0 p = p := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem model_path_continuous : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : Continuous q) (hZ : Continuous Z) (p : Plane),
    Continuous (fun t => convexModelContactVariationPath M q Z t p) := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem model_path_ne_zero : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p : Plane) (hp : p ≠ 0),
    convexModelContactVariationPath M q Z t p ≠ 0 := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.2.2.2.2.2.2

/-- A nonvanishing complex family over time and an unwrapped direction
parameter admits a jointly continuous logarithm with prescribed base value. -/
private theorem complex_plane_parameter_log_lift (z : ℝ × ℝ → ℂ) (hz : Continuous z)
    (hne : ∀ x, z x ≠ 0) (a : ℂ) (ha : Complex.exp a = z (0, 0)) :
    ∃ f : ℝ × ℝ → ℂ, Continuous f ∧ f (0, 0) = a ∧
      ∀ x, Complex.exp (f x) = z x := by
  let g : C(ℝ × ℝ, {z : ℂ // z ≠ 0}) := ⟨fun x => ⟨z x, hne x⟩, hz.subtype_mk _⟩
  obtain ⟨f, hf, _⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
    g (0, 0) a (Subtype.ext ha)
  refine ⟨f, f.continuous, hf.1, ?_⟩
  intro x
  exact congrArg Subtype.val (congrFun hf.2 x)

/-- Jointly continuous nonzero plane families starting at the direction
parameter have a jointly continuous polar angle normalized at time zero. -/
private theorem plane_family_normalized_polar_lift (v : ℝ × ℝ → Plane)
    (hv : Continuous v) (hne : ∀ x, v x ≠ 0)
    (hzero : ∀ s, v (0, s) = ![Real.cos s, Real.sin s]) :
    ∃ ρ θ : ℝ × ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      ∀ x, v x = ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)] := by
  let z : ℝ × ℝ → ℂ := fun x => ⟨v x 0, v x 1⟩
  have hz : Continuous z := by
    have h0 := Complex.continuous_ofReal.comp ((continuous_apply 0).comp hv)
    have h1 := Complex.continuous_ofReal.comp ((continuous_apply 1).comp hv)
    convert! h0.add (h1.mul_const Complex.I) using 1
    funext x
    apply Complex.ext <;> simp [z]
  have hn (x : ℝ × ℝ) : z x ≠ 0 := by
    intro h
    apply hne x
    ext i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  have hbase : Complex.exp 0 = z (0, 0) := by
    apply Complex.ext <;> simp [z, hzero]
  obtain ⟨f, hf, hf0, he⟩ := complex_plane_parameter_log_lift z hz hn 0 hbase
  let ρ : ℝ × ℝ → ℝ := fun x => Real.exp (f x).re
  let θ : ℝ × ℝ → ℝ := fun x => (f x).im
  have hρ : Continuous ρ := Real.continuous_exp.comp (Complex.continuous_re.comp hf)
  have hθ : Continuous θ := Complex.continuous_im.comp hf
  have hp (x : ℝ × ℝ) : 0 < ρ x := Real.exp_pos _
  have hvp (x : ℝ × ℝ) : v x =
      ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)] := by
    ext i
    fin_cases i
    · simpa [z, ρ, θ, Complex.exp_re] using (congrArg Complex.re (he x)).symm
    · simpa [z, ρ, θ, Complex.exp_im] using (congrArg Complex.im (he x)).symm
  have hdir (s : ℝ) : Real.cos (θ (0, s)) = Real.cos s ∧
      Real.sin (θ (0, s)) = Real.sin s := by
    exact (polar_unique (v (0, s)) (ρ (0, s)) 1 (θ (0, s)) s (hp _) zero_lt_one
      (hvp _) (by simpa using hzero s)).2
  have hinc := angle_increment_unique (fun s => θ (0, s)) (fun s : ℝ => s)
    (hθ.comp (continuous_const.prodMk continuous_id)) continuous_id
    (fun s => (hdir s).1) (fun s => (hdir s).2)
  refine ⟨ρ, θ, hρ, hθ, hp, ?_, hvp⟩
  intro s
  have h00 : θ (0, 0) = 0 := by simp [θ, hf0]
  simpa [h00] using hinc s

/-- The time-zero normalization makes a continuous polar angle unique
simultaneously for all initial directions. -/
private theorem normalized_plane_family_angle_unique (v : ℝ × ℝ → Plane)
    (ρ σ θ ψ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ x, 0 < ρ x) (hσ : ∀ x, 0 < σ x)
    (hθ0 : ∀ s, θ (0, s) = s) (hψ0 : ∀ s, ψ (0, s) = s)
    (hvθ : ∀ x, v x = ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)])
    (hvψ : ∀ x, v x = ![σ x * Real.cos (ψ x), σ x * Real.sin (ψ x)]) : θ = ψ := by
  funext x
  have h := polar_increment_unique (fun t => v (t, x.2))
    (fun t => ρ (t, x.2)) (fun t => σ (t, x.2))
    (fun t => θ (t, x.2)) (fun t => ψ (t, x.2))
    (hθ.comp (continuous_id.prodMk continuous_const))
    (hψ.comp (continuous_id.prodMk continuous_const))
    (fun t => hρ _) (fun t => hσ _) (fun t => hvθ _) (fun t => hvψ _) x.1
  simpa [hθ0, hψ0] using h

/-- Periodicity of the direction family gives periodicity of its winding
increments, with the expected shift of its normalized angle. -/
private theorem normalized_plane_family_angle_shift (v : ℝ × ℝ → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hρ : ∀ x, 0 < ρ x)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ x, v x = ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)])
    (P : ℝ) (hperiod : ∀ t s, v (t, s + P) = v (t, s)) :
    ∀ t s, θ (t, s + P) = θ (t, s) + P := by
  intro t s
  have h := polar_increment_unique (fun t => v (t, s))
    (fun t => ρ (t, s + P)) (fun t => ρ (t, s))
    (fun t => θ (t, s + P)) (fun t => θ (t, s))
    (hθ.comp (continuous_id.prodMk continuous_const))
    (hθ.comp (continuous_id.prodMk continuous_const))
    (fun t => hρ _) (fun t => hρ _)
    (fun t => (hperiod t s).symm.trans (hpolar _)) (fun t => hpolar _) t
  rw [hθ0, hθ0] at h
  linarith

/-- The winding image over one full initial-direction interval is a closed
interval with both endpoints attained. No width estimate is asserted. -/
private theorem plane_family_winding_interval (θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (T : ℝ) :
    ∃ a b : ℝ, a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = a) ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = b) := by
  let d : ℝ → ℝ := fun s => (θ (T, s) - s) / (2 * Real.pi)
  have hd : Continuous d :=
    ((hθ.comp (continuous_const.prodMk continuous_id)).sub continuous_id).div_const _
  have hnon : (d '' Icc 0 (2 * Real.pi)).Nonempty :=
    (nonempty_Icc.mpr (by positivity)).image d
  have hc : IsCompact (d '' Icc 0 (2 * Real.pi)) := isCompact_Icc.image hd
  obtain ⟨a, ha⟩ := hc.exists_isLeast hnon
  obtain ⟨b, hb⟩ := hc.exists_isGreatest hnon
  have hab : a ≤ b := ha.2 hb.1
  refine ⟨a, b, hab, ?_, ha.1, hb.1⟩
  change d '' Icc 0 (2 * Real.pi) = Icc a b
  rw [hd.continuousOn.image_Icc (by positivity), ha.csInf_eq, hb.csSup_eq]

/-- An attained lower endpoint turns strict winding bounds for every direction
into a single strict inequality at that endpoint. -/
private theorem winding_image_strict_lower_bound_iff (d : ℝ → ℝ) (a b c : ℝ)
    (hab : a ≤ b) (himage : d '' Icc 0 (2 * Real.pi) = Icc a b) :
    (∀ s ∈ Icc 0 (2 * Real.pi), c < d s) ↔ c < a := by
  constructor
  · intro h
    have ha : a ∈ d '' Icc 0 (2 * Real.pi) := by rw [himage]; exact ⟨le_rfl, hab⟩
    obtain ⟨s, hs, he⟩ := ha
    simpa [he] using h s hs
  · intro h s hs
    have hm : d s ∈ Icc a b := by rw [← himage]; exact mem_image_of_mem _ hs
    exact h.trans_le hm.1

/-- Linearity and continuity in time for each fixed vector imply joint
continuity of a planar coefficient action. -/
private theorem plane_linear_action_joint_continuous (A : ℝ → Plane → Plane)
    (hlin : ∀ t (p r : Plane) (a b : ℝ), A t (a • p + b • r) = a • A t p + b • A t r)
    (hcont : ∀ p, Continuous (fun t => A t p)) :
    Continuous (fun x : ℝ × Plane => A x.1 x.2) := by
  have he (p : Plane) : p = p 0 • ![1, 0] + p 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp
  have hc : Continuous (fun x : ℝ × Plane =>
      x.2 0 • A x.1 ![1, 0] + x.2 1 • A x.1 ![0, 1]) :=
    (((continuous_apply 0).comp continuous_snd).smul
    ((hcont ![1, 0]).comp continuous_fst)).add
    (((continuous_apply 1).comp continuous_snd).smul
      ((hcont ![0, 1]).comp continuous_fst))
  convert! hc using 1
  funext x
  rw [← hlin, ← he]

/-- The concrete supplied contact variational action admits one polar lift
continuous in both time and every unwrapped initial angle. -/
private theorem convex_model_contact_variation_joint_polar_lift {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) :
    ∃ ρ θ : ℝ × ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      ∀ x, convexModelContactVariationPath M q Z x.1 ![Real.cos x.2, Real.sin x.2] =
        ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)] := by
  apply plane_family_normalized_polar_lift
    (fun x : ℝ × ℝ => convexModelContactVariationPath M q Z x.1
      ![Real.cos x.2, Real.sin x.2])
  · have hc := plane_linear_action_joint_continuous (convexModelContactVariationPath M q Z)
      (model_path_linear M q Z)
      (model_path_continuous
        M q Z hs (continuous_iff_continuousAt.mpr (fun t => (hq t).continuousAt))
        (continuous_iff_continuousAt.mpr (fun t => (hZ t).continuousAt)))
    have hd : Continuous (fun x : ℝ × ℝ =>
        (x.1, (![Real.cos x.2, Real.sin x.2] : Plane))) :=
      continuous_fst.prodMk (continuous_pi (fun i => by
      fin_cases i
      · change Continuous (fun x : ℝ × ℝ => Real.cos x.2)
        exact Real.continuous_cos.comp continuous_snd
      · change Continuous (fun x : ℝ × ℝ => Real.sin x.2)
        exact Real.continuous_sin.comp continuous_snd))
    exact (hc.comp hd).congr (fun x => rfl)
  · intro x
    apply model_path_ne_zero M q Z hs hq hZ hZ0 x.1
    intro h
    have hcos : Real.cos x.2 = 0 := by simpa using congrFun h 0
    have hsin : Real.sin x.2 = 0 := by simpa using congrFun h 1
    have hsq := Real.cos_sq_add_sin_sq x.2
    rw [hcos, hsin] at hsq
    norm_num at hsq
  · intro s
    exact model_path_initial M q Z (hs 0) hZ0 _

/-- A genuine supplied contact action has a closed winding image in the
normalized jointly continuous lift, and its strict one-turn bound is exactly
the lower-endpoint inequality. -/
private theorem convex_model_contact_variation_winding_interval {μ c : ℝ}
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
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = a) ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = b) ∧
      ((∀ s ∈ Icc 0 (2 * Real.pi), 2 * Real.pi < θ (T, s) - s) ↔ 1 < a) := by
  obtain ⟨ρ, θ, hρ, hθ, hp, h0, hpolar⟩ :=
    convex_model_contact_variation_joint_polar_lift M q Z hs hq hZ hZ0
  obtain ⟨a, b, hab, himage, hmin, hmax⟩ := plane_family_winding_interval θ hθ T
  refine ⟨ρ, θ, a, b, hρ, hθ, hp, h0, hpolar, hab, himage, hmin, hmax, ?_⟩
  have hpi : 0 < 2 * Real.pi := by positivity
  have h := winding_image_strict_lower_bound_iff
    (fun s => (θ (T, s) - s) / (2 * Real.pi)) a b 1 hab himage
  simpa only [lt_div_iff₀ hpi, one_mul] using h

/-- The previously published arithmetic rule now applies to an actual
continuous winding image. The width remains an explicit hypothesis, and this
does not identify the integer expression with a Conley--Zehnder index. -/
private theorem winding_image_lower_rule_threshold_iff (d : ℝ → ℝ) (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b) :
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔
      ∀ s ∈ Icc 0 (2 * Real.pi), (k : ℝ) < d s := by
  rw [BirkhoffGlobalSection.winding_arithmetic_bundle.1 a b k hab hwidth]
  exact (winding_image_strict_lower_bound_iff d a b k hab himage).symm

set_option linter.unusedVariables false in
theorem solution :
(∀ (z : ℝ × ℝ → ℂ) (hz : Continuous z)
    (hne : ∀ x, z x ≠ 0) (a : ℂ) (ha : Complex.exp a = z (0, 0)),
    ∃ f : ℝ × ℝ → ℂ, Continuous f ∧ f (0, 0) = a ∧
      ∀ x, Complex.exp (f x) = z x) ∧
(∀ (v : ℝ × ℝ → Plane)
    (hv : Continuous v) (hne : ∀ x, v x ≠ 0)
    (hzero : ∀ s, v (0, s) = ![Real.cos s, Real.sin s]),
    ∃ ρ θ : ℝ × ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      ∀ x, v x = ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)]) ∧
(∀ (v : ℝ × ℝ → Plane)
    (ρ σ θ ψ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ x, 0 < ρ x) (hσ : ∀ x, 0 < σ x)
    (hθ0 : ∀ s, θ (0, s) = s) (hψ0 : ∀ s, ψ (0, s) = s)
    (hvθ : ∀ x, v x = ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)])
    (hvψ : ∀ x, v x = ![σ x * Real.cos (ψ x), σ x * Real.sin (ψ x)]),
    θ = ψ) ∧
(∀ (v : ℝ × ℝ → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hρ : ∀ x, 0 < ρ x)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ x, v x = ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)])
    (P : ℝ) (hperiod : ∀ t s, v (t, s + P) = v (t, s)),
    ∀ t s, θ (t, s + P) = θ (t, s) + P) ∧
(∀ (θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (T : ℝ),
    ∃ a b : ℝ, a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = a) ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = b)) ∧
(∀ (d : ℝ → ℝ) (a b c : ℝ)
    (hab : a ≤ b) (himage : d '' Icc 0 (2 * Real.pi) = Icc a b),
    (∀ s ∈ Icc 0 (2 * Real.pi), c < d s) ↔ c < a) ∧
(∀ (A : ℝ → Plane → Plane)
    (hlin : ∀ t (p r : Plane) (a b : ℝ), A t (a • p + b • r) = a • A t p + b • A t r)
    (hcont : ∀ p, Continuous (fun t => A t p)),
    Continuous (fun x : ℝ × Plane => A x.1 x.2)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase),
    ∃ ρ θ : ℝ × ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      ∀ x, convexModelContactVariationPath M q Z x.1 ![Real.cos x.2, Real.sin x.2] =
        ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)]) ∧
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
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = a) ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = b) ∧
      ((∀ s ∈ Icc 0 (2 * Real.pi), 2 * Real.pi < θ (T, s) - s) ↔ 1 < a)) ∧
(∀ (d : ℝ → ℝ) (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b),
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔
      ∀ s ∈ Icc 0 (2 * Real.pi), (k : ℝ) < d s) := by
  exact ⟨@complex_plane_parameter_log_lift, ⟨@plane_family_normalized_polar_lift, ⟨@normalized_plane_family_angle_unique, ⟨@normalized_plane_family_angle_shift, ⟨@plane_family_winding_interval, ⟨@winding_image_strict_lower_bound_iff, ⟨@plane_linear_action_joint_continuous, ⟨@convex_model_contact_variation_joint_polar_lift, ⟨@convex_model_contact_variation_winding_interval, @winding_image_lower_rule_threshold_iff⟩⟩⟩⟩⟩⟩⟩⟩⟩
