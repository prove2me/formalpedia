-- Prove2me | solution 1 for DoCarmoDG.signedCurvature_eq_deriv_angle
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T19:49:39.587094+00:00
-- url     : https://prove2.me/submissions/2f983c01-5a38-4c21-8712-3b51fb8eccbc

import Mathlib
import Definitions.Def_DoCarmo_plane_curves
import Definitions.Def_DoCarmo_regular_surface
import Definitions.Def_DoCarmo_surface_patch
import Definitions.Def_DoCarmo_local_theory_curves

open DoCarmoDG

/-! ## coordinate helpers -/

theorem W2c_DoCarmoDG_inner3 (x y : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem W2c_DoCarmoDG_inner2 (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem W2c_DoCarmoDG_normsq3 (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]

theorem W2c_DoCarmoDG_cross0 (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 := by simp [cross]

theorem W2c_DoCarmoDG_cross1 (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v 1 = u 2 * v 0 - u 0 * v 2 := by simp [cross]

theorem W2c_DoCarmoDG_cross2 (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v 2 = u 0 * v 1 - u 1 * v 0 := by simp [cross]

/-! ## plane curves -/

theorem W2c_DoCarmoDG_sc_angle (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (theta : ℝ → ℝ)
    (halpha : IsClosedUnitSpeedCurve l alpha)
    (htheta : IsAngleFunction alpha theta) :
    ∀ s, signedCurvature alpha s = deriv theta s := by
  obtain ⟨hθ, hα⟩ := htheta
  have hθd : Differentiable ℝ theta := hθ.differentiable (by simp)
  let E0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  let E1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
  have hvec : ∀ a b : ℝ, (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) = a • E0 + b • E1 := by
    intro a b; ext i; fin_cases i <;> simp [E0, E1]
  have hd : deriv alpha = fun s => Real.cos (theta s) • E0 + Real.sin (theta s) • E1 := by
    funext s; rw [hα s, hvec]
  intro s
  have h2 : HasDerivAt (deriv alpha) ((-Real.sin (theta s) * deriv theta s) • E0 +
      (Real.cos (theta s) * deriv theta s) • E1) s := by
    rw [hd]
    exact (((hθd s).hasDerivAt.cos).smul_const E0).add (((hθd s).hasDerivAt.sin).smul_const E1)
  unfold signedCurvature rot90
  rw [h2.deriv, hα s, W2c_DoCarmoDG_inner2]
  simp [E0, E1]
  linear_combination (deriv theta s) * Real.sin_sq_add_cos_sq (theta s)

theorem W2c_DoCarmoDG_comp_deriv (alpha : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ)
    (hα : DifferentiableAt ℝ alpha t) (i : Fin 2) :
    HasDerivAt (fun s => alpha s i) (deriv alpha t i) t := by
  have := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
    t hα.hasDerivAt
  exact this

theorem W2c_DoCarmoDG_area (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsClosedUnitSpeedCurve l alpha) :
    (∫ t in (0 : ℝ)..l, alpha t 0 * deriv alpha t 1) =
        -∫ t in (0 : ℝ)..l, alpha t 1 * deriv alpha t 0 ∧
      signedArea l alpha = ∫ t in (0 : ℝ)..l, alpha t 0 * deriv alpha t 1 := by
  obtain ⟨hl, hsm, hper, hunit⟩ := halpha
  have hd : Differentiable ℝ alpha := hsm.differentiable (by simp)
  have hcd : Continuous (deriv alpha) := hsm.continuous_deriv (by simp)
  have hc : ∀ i : Fin 2, Continuous fun t => alpha t i := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp hd.continuous
  have hc' : ∀ i : Fin 2, Continuous fun t => deriv alpha t i := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp hcd
  have hprod : ∀ t, HasDerivAt (fun s => alpha s 0 * alpha s 1)
      (deriv alpha t 0 * alpha t 1 + alpha t 0 * deriv alpha t 1) t :=
    fun t => (W2c_DoCarmoDG_comp_deriv alpha t (hd t) 0).mul
      (W2c_DoCarmoDG_comp_deriv alpha t (hd t) 1)
  have i1 : IntervalIntegrable (fun t => deriv alpha t 0 * alpha t 1)
      MeasureTheory.volume 0 l := ((hc' 0).mul (hc 1)).intervalIntegrable 0 l
  have i2 : IntervalIntegrable (fun t => alpha t 0 * deriv alpha t 1)
      MeasureTheory.volume 0 l := ((hc 0).mul (hc' 1)).intervalIntegrable 0 l
  have i3 : IntervalIntegrable (fun t => alpha t 1 * deriv alpha t 0)
      MeasureTheory.volume 0 l := ((hc 1).mul (hc' 0)).intervalIntegrable 0 l
  have hibp := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := l)
    (fun t _ => hprod t) (i1.add i2)
  have hper0 : alpha l = alpha 0 := by simpa using hper 0
  rw [hper0, sub_self, intervalIntegral.integral_add i1 i2] at hibp
  have hcomm : (∫ t in (0 : ℝ)..l, alpha t 1 * deriv alpha t 0) =
      ∫ t in (0 : ℝ)..l, deriv alpha t 0 * alpha t 1 := by
    congr 1; funext t; ring
  have h1 : (∫ t in (0 : ℝ)..l, alpha t 0 * deriv alpha t 1) =
      -∫ t in (0 : ℝ)..l, alpha t 1 * deriv alpha t 0 := by
    rw [hcomm]; linarith
  refine ⟨h1, ?_⟩
  unfold signedArea
  rw [intervalIntegral.integral_sub i2 i3, h1]
  ring

/-! ## space curves -/

theorem W2c_DoCarmoDG_straight (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha) :
    (∀ s ∈ Set.Ioo a b, curvature alpha s = 0) ↔
      ∃ u v : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧
        ∀ s ∈ Set.Ioo a b, alpha s = s • u + v := by
  obtain ⟨hsm, hunit⟩ := halpha
  have hd1 : ContDiffOn ℝ 1 (deriv alpha) (Set.Ioo a b) :=
    hsm.deriv_of_isOpen isOpen_Ioo
    (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp)
  have hdα : ∀ s ∈ Set.Ioo a b, DifferentiableAt ℝ alpha s := fun s hs =>
    (hsm.differentiableOn (by simp) s hs).differentiableAt (isOpen_Ioo.mem_nhds hs)
  have hddα : ∀ s ∈ Set.Ioo a b, DifferentiableAt ℝ (deriv alpha) s := fun s hs =>
    (hd1.differentiableOn (by simp) s hs).differentiableAt (isOpen_Ioo.mem_nhds hs)
  constructor
  · intro hk
    by_cases hab : a < b
    · have hs0 : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
      have hconst : ∀ s ∈ Set.Ioo a b, deriv alpha s = deriv alpha ((a + b) / 2) :=
        fun s hs => isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
          (fun x hx => (hddα x hx).differentiableWithinAt)
          (fun x hx => by
            have := hk x hx
            unfold curvature at this
            simpa using this) hs hs0
      refine ⟨deriv alpha ((a + b) / 2),
        alpha ((a + b) / 2) - ((a + b) / 2) • deriv alpha ((a + b) / 2),
        hunit _ hs0, fun s hs => ?_⟩
      have hc2 : alpha s - s • deriv alpha ((a + b) / 2) =
          alpha ((a + b) / 2) - ((a + b) / 2) • deriv alpha ((a + b) / 2) :=
        isOpen_Ioo.is_const_of_deriv_eq_zero
          (f := fun t => alpha t - t • deriv alpha ((a + b) / 2)) isPreconnected_Ioo
          (fun x hx => ((hdα x hx).sub
            (differentiableAt_id.smul_const _)).differentiableWithinAt)
          (fun x hx => by
            have h : HasDerivAt (fun t => alpha t - t • deriv alpha ((a + b) / 2))
                (deriv alpha x - (1:ℝ) • deriv alpha ((a + b) / 2)) x :=
              (hdα x hx).hasDerivAt.sub
              ((hasDerivAt_id' x).smul_const (deriv alpha ((a + b) / 2)))
            rw [Pi.zero_apply, h.deriv, hconst x hx, one_smul, sub_self]) hs hs0
      rw [← hc2]
      abel
    · refine ⟨EuclideanSpace.single 0 1, 0, by simp, fun s hs => ?_⟩
      exact absurd (hs.1.trans hs.2) hab
  · rintro ⟨u, v, hu, hα⟩ s hs
    have hev : ∀ t ∈ Set.Ioo a b, deriv alpha t = u := by
      intro t ht
      have h1 : alpha =ᶠ[nhds t] fun r => r • u + v := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr using hα r hr
      rw [h1.deriv_eq, (((hasDerivAt_id' t).smul_const u).add_const v).deriv, one_smul]
    have h2 : deriv alpha =ᶠ[nhds s] fun _ => u := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr using hev r hr
    unfold curvature
    rw [h2.deriv_eq]
    simp

theorem W2c_DoCarmoDG_orth (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha) :
    ∀ s ∈ Set.Ioo a b, inner ℝ (deriv alpha s) (deriv (deriv alpha) s) = 0 := by
  obtain ⟨hsm, hunit⟩ := halpha
  have hd1 : ContDiffOn ℝ 1 (deriv alpha) (Set.Ioo a b) :=
    hsm.deriv_of_isOpen isOpen_Ioo
    (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp)
  intro s hs
  have h1 := ((hd1.differentiableOn (by simp) s hs).differentiableAt
    (isOpen_Ioo.mem_nhds hs)).hasDerivAt
  have h2 := HasDerivAt.inner ℝ h1 h1
  have hev : (fun t => inner ℝ (deriv alpha t) (deriv alpha t)) =ᶠ[nhds s] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    rw [real_inner_self_eq_norm_sq, hunit t ht, one_pow]
  have h3 := h2.deriv
  rw [hev.deriv_eq, deriv_const, real_inner_comm (deriv alpha s)] at h3
  linarith

theorem W2c_DoCarmoDG_trihedron (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    ∀ s ∈ Set.Ioo a b,
      ‖tangent alpha s‖ = 1 ∧ ‖normal alpha s‖ = 1 ∧ ‖binormal alpha s‖ = 1 ∧
      inner ℝ (tangent alpha s) (normal alpha s) = 0 ∧
      inner ℝ (normal alpha s) (binormal alpha s) = 0 ∧
      inner ℝ (binormal alpha s) (tangent alpha s) = 0 := by
  intro s hs
  have horth := W2c_DoCarmoDG_orth a b alpha halpha s hs
  have ht : ‖tangent alpha s‖ = 1 := halpha.2 s hs
  have hks := hk s hs
  have hkpos : 0 < curvature alpha s := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hks)
  have hn : ‖normal alpha s‖ = 1 := by
    unfold normal
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hkpos.le]
    unfold curvature at hks ⊢
    exact inv_mul_cancel₀ hks
  have htn : inner ℝ (tangent alpha s) (normal alpha s) = 0 := by
    unfold normal tangent
    rw [real_inner_smul_right, horth, mul_zero]
  set T := tangent alpha s with hT
  set N := normal alpha s with hN
  have hb : binormal alpha s = cross T N := rfl
  have ht2 : T 0 ^ 2 + T 1 ^ 2 + T 2 ^ 2 = 1 := by rw [← W2c_DoCarmoDG_normsq3, ht]; norm_num
  have hn2 : N 0 ^ 2 + N 1 ^ 2 + N 2 ^ 2 = 1 := by rw [← W2c_DoCarmoDG_normsq3, hn]; norm_num
  have htn' : T 0 * N 0 + T 1 * N 1 + T 2 * N 2 = 0 := by rw [← W2c_DoCarmoDG_inner3]; exact htn
  have hb2 : ‖binormal alpha s‖ ^ 2 = 1 := by
    rw [hb, W2c_DoCarmoDG_normsq3, W2c_DoCarmoDG_cross0, W2c_DoCarmoDG_cross1,
      W2c_DoCarmoDG_cross2]
    have : (T 1 * N 2 - T 2 * N 1) ^ 2 + (T 2 * N 0 - T 0 * N 2) ^ 2 +
        (T 0 * N 1 - T 1 * N 0) ^ 2 =
        (T 0 ^ 2 + T 1 ^ 2 + T 2 ^ 2) * (N 0 ^ 2 + N 1 ^ 2 + N 2 ^ 2) -
          (T 0 * N 0 + T 1 * N 1 + T 2 * N 2) ^ 2 := by ring
    rw [this, ht2, hn2, htn']
    norm_num
  refine ⟨ht, hn, ?_, htn, ?_, ?_⟩
  · have := norm_nonneg (binormal alpha s)
    nlinarith
  · rw [hb, W2c_DoCarmoDG_inner3, W2c_DoCarmoDG_cross0, W2c_DoCarmoDG_cross1,
      W2c_DoCarmoDG_cross2]
    ring
  · rw [hb, W2c_DoCarmoDG_inner3, W2c_DoCarmoDG_cross0, W2c_DoCarmoDG_cross1,
      W2c_DoCarmoDG_cross2]
    ring

/-! ## Christoffel decomposition -/

theorem W2c_DoCarmoDG_indep (u v : EuclideanSpace ℝ (Fin 3)) (hc : cross u v ≠ 0)
    (a b : ℝ) (h : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  have h1 : cross (a • u + b • v) v = a • cross u v := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  have h2 : cross u (a • u + b • v) = b • cross u v := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  rw [h] at h1 h2
  have e1 : cross (0 : EuclideanSpace ℝ (Fin 3)) v = 0 := by ext i; fin_cases i <;> simp [cross]
  have e2 : cross u (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by ext i; fin_cases i <;> simp [cross]
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨(smul_eq_zero.1 h1.symm).resolve_right hc, (smul_eq_zero.1 h2.symm).resolve_right hc⟩

theorem W2c_DoCarmoDG_decomp (u v w : EuclideanSpace ℝ (Fin 3)) (hc : cross u v ≠ 0) :
    w = ((inner ℝ w u * inner ℝ v v - inner ℝ w v * inner ℝ u v) /
          (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2)) • u +
        ((inner ℝ w v * inner ℝ u u - inner ℝ w u * inner ℝ u v) /
          (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2)) • v +
        inner ℝ (‖cross u v‖⁻¹ • cross u v) w • (‖cross u v‖⁻¹ • cross u v) := by
  have hcn : ‖cross u v‖ ≠ 0 := norm_ne_zero_iff.2 hc
  have hW : ‖cross u v‖ ^ 2 = inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 := by
    rw [W2c_DoCarmoDG_normsq3, W2c_DoCarmoDG_cross0, W2c_DoCarmoDG_cross1,
      W2c_DoCarmoDG_cross2, W2c_DoCarmoDG_inner3, W2c_DoCarmoDG_inner3, W2c_DoCarmoDG_inner3]
    ring
  have hN : inner ℝ (‖cross u v‖⁻¹ • cross u v) w • (‖cross u v‖⁻¹ • cross u v) =
      (inner ℝ (cross u v) w / ‖cross u v‖ ^ 2) • cross u v := by
    rw [real_inner_smul_left, smul_smul]
    congr 1
    field_simp
  rw [hN, hW]
  have hW0 : inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 ≠ 0 := by
    rw [← hW]; exact pow_ne_zero 2 hcn
  have key : (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) • w =
      (inner ℝ w u * inner ℝ v v - inner ℝ w v * inner ℝ u v) • u +
      (inner ℝ w v * inner ℝ u u - inner ℝ w u * inner ℝ u v) • v +
      inner ℝ (cross u v) w • cross u v := by
    simp only [W2c_DoCarmoDG_inner3]
    ext i
    fin_cases i <;> simp [W2c_DoCarmoDG_cross0, W2c_DoCarmoDG_cross1, W2c_DoCarmoDG_cross2] <;>
      ring
  calc w = (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2)⁻¹ •
        ((inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) • w) := by
          rw [smul_smul, inv_mul_cancel₀ hW0, one_smul]
    _ = _ := by
          rw [key, smul_add, smul_add, smul_smul, smul_smul, smul_smul, div_eq_inv_mul,
            div_eq_inv_mul, div_eq_inv_mul]

theorem W2c_DoCarmoDG_christoffel_decomposition
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x) :
    ∃ G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ,
      IsChristoffel U x G111 G211 G112 G212 G122 G222 ∧
      ∀ H111 H211 H112 H212 H122 H222 : ℝ → ℝ → ℝ,
        IsChristoffel U x H111 H211 H112 H212 H122 H222 →
        ∀ p ∈ U,
          H111 p.1 p.2 = G111 p.1 p.2 ∧ H211 p.1 p.2 = G211 p.1 p.2 ∧
          H112 p.1 p.2 = G112 p.1 p.2 ∧ H212 p.1 p.2 = G212 p.1 p.2 ∧
          H122 p.1 p.2 = G122 p.1 p.2 ∧ H222 p.1 p.2 = G222 p.1 p.2 := by
  let A : EuclideanSpace ℝ (Fin 3) → ℝ → ℝ → ℝ := fun w u v =>
    (inner ℝ w (partialU x u v) * inner ℝ (partialV x u v) (partialV x u v) -
      inner ℝ w (partialV x u v) * inner ℝ (partialU x u v) (partialV x u v)) /
    (inner ℝ (partialU x u v) (partialU x u v) * inner ℝ (partialV x u v) (partialV x u v) -
      inner ℝ (partialU x u v) (partialV x u v) ^ 2)
  let B : EuclideanSpace ℝ (Fin 3) → ℝ → ℝ → ℝ := fun w u v =>
    (inner ℝ w (partialV x u v) * inner ℝ (partialU x u v) (partialU x u v) -
      inner ℝ w (partialU x u v) * inner ℝ (partialU x u v) (partialV x u v)) /
    (inner ℝ (partialU x u v) (partialU x u v) * inner ℝ (partialV x u v) (partialV x u v) -
      inner ℝ (partialU x u v) (partialV x u v) ^ 2)
  have hdec : ∀ p ∈ U, ∀ w : EuclideanSpace ℝ (Fin 3),
      w = A w p.1 p.2 • partialU x p.1 p.2 + B w p.1 p.2 • partialV x p.1 p.2 +
        inner ℝ (unitNormal x p.1 p.2) w • unitNormal x p.1 p.2 := by
    intro p hp w
    exact W2c_DoCarmoDG_decomp _ _ w (hx.2 p hp)
  have huniq : ∀ p ∈ U, ∀ a₁ b₁ a₂ b₂ c : ℝ,
      a₁ • partialU x p.1 p.2 + b₁ • partialV x p.1 p.2 + c • unitNormal x p.1 p.2 =
      a₂ • partialU x p.1 p.2 + b₂ • partialV x p.1 p.2 + c • unitNormal x p.1 p.2 →
      a₁ = a₂ ∧ b₁ = b₂ := by
    intro p hp a₁ b₁ a₂ b₂ c h
    have h3 : (a₁ - a₂) • partialU x p.1 p.2 + (b₁ - b₂) • partialV x p.1 p.2 = 0 := by
      have := sub_eq_zero.2 h
      rw [← this]
      simp only [sub_smul]
      abel
    obtain ⟨h4, h5⟩ := W2c_DoCarmoDG_indep _ _ (hx.2 p hp) _ _ h3
    exact ⟨sub_eq_zero.1 h4, sub_eq_zero.1 h5⟩
  have hcoef : ∀ p ∈ U, ∀ w : EuclideanSpace ℝ (Fin 3),
      inner ℝ (unitNormal x p.1 p.2) w = inner ℝ (unitNormal x p.1 p.2) w := fun _ _ _ => rfl
  refine ⟨fun u v => A (partialU (partialU x) u v) u v, fun u v => B (partialU (partialU x) u v) u v,
    fun u v => A (partialV (partialU x) u v) u v, fun u v => B (partialV (partialU x) u v) u v,
    fun u v => A (partialV (partialV x) u v) u v, fun u v => B (partialV (partialV x) u v) u v,
    fun p hp => ⟨hdec p hp _, hdec p hp _, hdec p hp _⟩, ?_⟩
  intro H111 H211 H112 H212 H122 H222 hH p hp
  obtain ⟨e1, e2, e3⟩ := hH p hp
  have f1 := huniq p hp _ _ _ _ _ (e1.symm.trans (hdec p hp _))
  have f2 := huniq p hp _ _ _ _ _ (e2.symm.trans (hdec p hp _))
  have f3 := huniq p hp _ _ _ _ _ (e3.symm.trans (hdec p hp _))
  exact ⟨f1.1, f1.2, f2.1, f2.2, f3.1, f3.2⟩

/-! ## graphs -/

theorem W2c_DoCarmoDG_graph (U : Set (ℝ × ℝ)) (hU : IsOpen U) (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    IsRegularSurface (graphOf U f) := by
  let E0 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
  let E1 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 1
  let E2 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 2 1
  let X : ℝ × ℝ → EuclideanSpace ℝ (Fin 3) := fun q => q.1 • E0 + q.2 • E1 + f q • E2
  have hX0 : ∀ q, X q 0 = q.1 := fun q => by simp [X, E0, E1, E2]
  have hX1 : ∀ q, X q 1 = q.2 := fun q => by simp [X, E0, E1, E2]
  have hX2 : ∀ q, X q 2 = f q := fun q => by simp [X, E0, E1, E2]
  let π : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).prod
      (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
  have hπX : ∀ q, π (X q) = q := fun q => by
    simp only [π, ContinuousLinearMap.prod_apply]
    ext <;> simp [hX0, hX1]
  have hXsm : ContDiffOn ℝ (⊤ : ℕ∞) X U :=
    ((contDiffOn_fst.smul contDiffOn_const).add (contDiffOn_snd.smul contDiffOn_const)).add
      (hf.smul contDiffOn_const)
  intro p hp
  refine ⟨{p | (p 0, p 1) ∈ U}, U, X, ?_, hp.1, ?_, ?_⟩
  · exact hU.preimage (((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous).prodMk
      (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous)
  · refine ⟨hU, hXsm, ?_, ?_, ⟨fun p => (p 0, p 1), ?_, ?_⟩, ?_⟩
    · intro q₁ _ q₂ _ h
      have := congrArg π h
      rwa [hπX, hπX] at this
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hX0, hX1]; exact hq
      · rw [hX0, hX1, hX2]
    · exact (((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous).prodMk
        (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous).continuousOn
    · intro q _; show (X q 0, X q 1) = q; rw [hX0, hX1]
    · intro q hq
      have hdiff : DifferentiableAt ℝ X q :=
        (hXsm.differentiableOn (by simp) q hq).differentiableAt (hU.mem_nhds hq)
      have h1 : HasFDerivAt (fun q => π (X q)) (π.comp (fderiv ℝ X q)) q :=
        π.hasFDerivAt.comp q hdiff.hasFDerivAt
      have hid : (fun q => π (X q)) = id := funext hπX
      rw [hid] at h1
      have h2 := h1.unique (hasFDerivAt_id q)
      intro v w hvw
      have := congrArg π hvw
      have e1 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => L v) h2
      have e2 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => L w) h2
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at e1 e2
      rw [← e1, ← e2, this]
  · ext p'
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · show (X q 0, X q 1) ∈ U
        rw [hX0, hX1]; exact hq
      · show (X q 0, X q 1) ∈ U
        rw [hX0, hX1]; exact hq
      · show X q 2 = f (X q 0, X q 1)
        rw [hX0, hX1, hX2]
    · rintro ⟨hp1, _, hp2⟩
      refine ⟨(p' 0, p' 1), hp1, ?_⟩
      ext i
      fin_cases i
      · exact hX0 _
      · exact hX1 _
      · show X (p' 0, p' 1) 2 = p' 2
        rw [hX2]; exact hp2.symm

/-! ## four vertex lemma and angle function -/

theorem W2c_DoCarmoDG_normsq2 (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]

theorem W2c_DoCarmoDG_plane_setup (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsClosedUnitSpeedCurve l alpha) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv alpha) ∧ ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv alpha)) ∧
    (∀ t, deriv alpha t 0 ^ 2 + deriv alpha t 1 ^ 2 = 1) ∧
    (∀ t, deriv alpha t 0 * deriv (deriv alpha) t 0 +
      deriv alpha t 1 * deriv (deriv alpha) t 1 = 0) ∧
    (∀ t, signedCurvature alpha t = deriv (deriv alpha) t 0 * -(deriv alpha t 1) +
      deriv (deriv alpha) t 1 * deriv alpha t 0) := by
  obtain ⟨hl, hsm, hper, hunit⟩ := halpha
  have hsm1 : ContDiff ℝ (⊤ : ℕ∞) (deriv alpha) := by
    simpa using hsm.iterate_deriv 1
  have hsm2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv alpha)) := by
    simpa using hsm.iterate_deriv 2
  have hu : ∀ t, deriv alpha t 0 ^ 2 + deriv alpha t 1 ^ 2 = 1 := by
    intro t; rw [← W2c_DoCarmoDG_normsq2, hunit t]; norm_num
  have hd1 : Differentiable ℝ (deriv alpha) := hsm1.differentiable (by simp)
  refine ⟨hsm1, hsm2, hu, fun t => ?_, fun t => ?_⟩
  · have h0 := W2c_DoCarmoDG_comp_deriv (deriv alpha) t (hd1 t) 0
    have h1 := W2c_DoCarmoDG_comp_deriv (deriv alpha) t (hd1 t) 1
    have h : HasDerivAt (fun s => deriv alpha s 0 * deriv alpha s 0 +
        deriv alpha s 1 * deriv alpha s 1)
        (deriv (deriv alpha) t 0 * deriv alpha t 0 + deriv alpha t 0 * deriv (deriv alpha) t 0 +
          (deriv (deriv alpha) t 1 * deriv alpha t 1 + deriv alpha t 1 * deriv (deriv alpha) t 1))
        t := (h0.mul h0).add (h1.mul h1)
    have hc : (fun s => deriv alpha s 0 * deriv alpha s 0 + deriv alpha s 1 * deriv alpha s 1) =
        fun _ => (1 : ℝ) := by
      funext s; have := hu s; nlinarith
    rw [hc] at h
    have := h.unique (hasDerivAt_const t (1 : ℝ))
    linarith
  · unfold signedCurvature rot90
    rw [W2c_DoCarmoDG_inner2]
    simp

theorem W2c_DoCarmoDG_four_vertex_lemma (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsClosedUnitSpeedCurve l alpha) (A B C : ℝ) :
    (∫ s in (0 : ℝ)..l,
        (A * alpha s 0 + B * alpha s 1 + C) * deriv (signedCurvature alpha) s) = 0 := by
  obtain ⟨hsm1, hsm2, hu, horth, hk⟩ := W2c_DoCarmoDG_plane_setup l alpha halpha
  obtain ⟨hl, hsm, hper, hunit⟩ := halpha
  have hd : Differentiable ℝ alpha := hsm.differentiable (by simp)
  have hd1 : Differentiable ℝ (deriv alpha) := hsm1.differentiable (by simp)
  have hp : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun t => deriv alpha t i) := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hsm1
  have hq : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun t => deriv (deriv alpha) t i) := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hsm2
  have hkfun : signedCurvature alpha = fun t => deriv (deriv alpha) t 0 * -(deriv alpha t 1) +
      deriv (deriv alpha) t 1 * deriv alpha t 0 := funext hk
  have hkc : ContDiff ℝ (⊤ : ℕ∞) (signedCurvature alpha) := by
    rw [hkfun]; exact ((hq 0).mul (hp 1).neg).add ((hq 1).mul (hp 0))
  have hkd : Differentiable ℝ (signedCurvature alpha) := hkc.differentiable (by simp)
  have hkd' : Continuous (deriv (signedCurvature alpha)) := hkc.continuous_deriv (by simp)
  have hper1 : ∀ t, deriv alpha (t + l) = deriv alpha t := by
    intro t
    have h1 : (fun s => alpha (s + l)) = alpha := funext hper
    have h2 := congrArg (fun f => deriv f t) h1
    simpa [deriv_comp_add_const] using h2
  have hper2 : ∀ t, deriv (deriv alpha) (t + l) = deriv (deriv alpha) t := by
    intro t
    have h1 : (fun s => deriv alpha (s + l)) = deriv alpha := funext hper1
    have h2 := congrArg (fun f => deriv f t) h1
    simpa [deriv_comp_add_const] using h2
  have hkper : signedCurvature alpha l = signedCurvature alpha 0 := by
    rw [hk, hk]
    have e1 := hper1 0
    have e2 := hper2 0
    simp only [zero_add] at e1 e2
    rw [e1, e2]
  have hαper : alpha l = alpha 0 := by simpa using hper 0
  have hPd : ∀ t, HasDerivAt (fun s => A * alpha s 0 + B * alpha s 1 + C)
      (A * deriv alpha t 0 + B * deriv alpha t 1) t := by
    intro t
    have := (((W2c_DoCarmoDG_comp_deriv alpha t (hd t) 0).const_mul A).add
      ((W2c_DoCarmoDG_comp_deriv alpha t (hd t) 1).const_mul B)).add_const C
    exact this
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := l)
    (fun t _ => hPd t) (fun t _ => (hkd t).hasDerivAt)
    (((continuous_const.mul (hp 0).continuous).add
      (continuous_const.mul (hp 1).continuous)).intervalIntegrable 0 l)
    (hkd'.intervalIntegrable 0 l)
  rw [hibp, hαper, hkper, sub_self, zero_sub, neg_eq_zero]
  have hpt : ∀ t, (A * deriv alpha t 0 + B * deriv alpha t 1) * signedCurvature alpha t =
      A * deriv (deriv alpha) t 1 - B * deriv (deriv alpha) t 0 := by
    intro t
    rw [hk]
    have e1 := hu t
    have e2 := horth t
    linear_combination (A * deriv (deriv alpha) t 1 - B * deriv (deriv alpha) t 0) * e1 +
      (-(A * deriv alpha t 1) + B * deriv alpha t 0) * e2
  simp_rw [hpt]
  have i1 : IntervalIntegrable (fun x => A * deriv (deriv alpha) x 1)
      MeasureTheory.volume 0 l := (continuous_const.mul (hq 1).continuous).intervalIntegrable 0 l
  have i2 : IntervalIntegrable (fun x => B * deriv (deriv alpha) x 0)
      MeasureTheory.volume 0 l := (continuous_const.mul (hq 0).continuous).intervalIntegrable 0 l
  rw [intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => W2c_DoCarmoDG_comp_deriv (deriv alpha) t (hd1 t) 1)
      ((hq 1).continuous.intervalIntegrable 0 l),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => W2c_DoCarmoDG_comp_deriv (deriv alpha) t (hd1 t) 0)
      ((hq 0).continuous.intervalIntegrable 0 l)]
  have e := hper1 0
  simp only [zero_add] at e
  rw [e]
  ring

theorem W2c_DoCarmoDG_angle_exists (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsClosedUnitSpeedCurve l alpha) :
    ∃ theta : ℝ → ℝ, IsAngleFunction alpha theta := by
  obtain ⟨hsm1, hsm2, hu, horth, hk⟩ := W2c_DoCarmoDG_plane_setup l alpha halpha
  have hd1 : Differentiable ℝ (deriv alpha) := hsm1.differentiable (by simp)
  have hp : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun t => deriv alpha t i) := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hsm1
  have hq : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun t => deriv (deriv alpha) t i) := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hsm2
  have hkfun : signedCurvature alpha = fun t => deriv (deriv alpha) t 0 * -(deriv alpha t 1) +
      deriv (deriv alpha) t 1 * deriv alpha t 0 := funext hk
  have hkc : ContDiff ℝ (⊤ : ℕ∞) (signedCurvature alpha) := by
    rw [hkfun]; exact ((hq 0).mul (hp 1).neg).add ((hq 1).mul (hp 0))
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ⟨deriv alpha 0 0, deriv alpha 0 1⟩ := ⟨_, rfl⟩
  have hzn : ‖z‖ = 1 := by
    rw [hz, Complex.norm_def, Complex.normSq_mk]
    have := hu 0
    rw [show deriv alpha 0 0 * deriv alpha 0 0 + deriv alpha 0 1 * deriv alpha 0 1 = 1 by
      nlinarith, Real.sqrt_one]
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; exact zero_ne_one hzn
  let θ : ℝ → ℝ := fun s => Complex.arg z + ∫ t in (0 : ℝ)..s, signedCurvature alpha t
  have hθd : ∀ s, HasDerivAt θ (signedCurvature alpha s) s := fun s =>
    ((hkc.continuous.integral_hasStrictDerivAt 0 s).hasDerivAt).const_add _
  have hθdiff : Differentiable ℝ θ := fun s => (hθd s).differentiableAt
  have hθderiv : deriv θ = signedCurvature alpha := funext fun s => (hθd s).deriv
  have hθc : ContDiff ℝ (⊤ : ℕ∞) θ := contDiff_infty_iff_deriv.2 ⟨hθdiff, by rw [hθderiv]; exact hkc⟩
  refine ⟨θ, hθc, fun s => ?_⟩
  -- D(s) = ⟨α', w⟩ is constant 1
  have hc0 : Real.cos (θ 0) = deriv alpha 0 0 := by
    simp only [θ, intervalIntegral.integral_same, add_zero]
    rw [Complex.cos_arg hz0, hzn, div_one, hz]
  have hs0 : Real.sin (θ 0) = deriv alpha 0 1 := by
    simp only [θ, intervalIntegral.integral_same, add_zero]
    rw [Complex.sin_arg, hzn, div_one, hz]
  have hD : ∀ t, HasDerivAt (fun r => deriv alpha r 0 * Real.cos (θ r) +
      deriv alpha r 1 * Real.sin (θ r))
      (deriv (deriv alpha) t 0 * Real.cos (θ t) +
        deriv alpha t 0 * (-Real.sin (θ t) * signedCurvature alpha t) +
        (deriv (deriv alpha) t 1 * Real.sin (θ t) +
          deriv alpha t 1 * (Real.cos (θ t) * signedCurvature alpha t))) t := fun t =>
    ((W2c_DoCarmoDG_comp_deriv (deriv alpha) t (hd1 t) 0).mul (hθd t).cos).add
      ((W2c_DoCarmoDG_comp_deriv (deriv alpha) t (hd1 t) 1).mul (hθd t).sin)
  have hD0 : ∀ t, deriv (deriv alpha) t 0 * Real.cos (θ t) +
        deriv alpha t 0 * (-Real.sin (θ t) * signedCurvature alpha t) +
        (deriv (deriv alpha) t 1 * Real.sin (θ t) +
          deriv alpha t 1 * (Real.cos (θ t) * signedCurvature alpha t)) = 0 := by
    intro t
    rw [hk t]
    have e1 := hu t
    have e2 := horth t
    linear_combination (-(deriv (deriv alpha) t 0 * Real.cos (θ t) +
      deriv (deriv alpha) t 1 * Real.sin (θ t))) * e1 +
      (deriv alpha t 0 * Real.cos (θ t) + deriv alpha t 1 * Real.sin (θ t)) * e2
  have hDc := is_const_of_deriv_eq_zero (fun t => (hD t).differentiableAt)
    (fun t => (hD t).deriv.trans (hD0 t)) s 0
  beta_reduce at hDc
  rw [hc0, hs0] at hDc
  have h1 : deriv alpha s 0 * Real.cos (θ s) + deriv alpha s 1 * Real.sin (θ s) = 1 := by
    rw [hDc]; nlinarith [hu 0]
  have h2 := hu s
  have h3 := Real.sin_sq_add_cos_sq (θ s)
  have e0 : deriv alpha s 0 = Real.cos (θ s) := by
    nlinarith [sq_nonneg (deriv alpha s 0 - Real.cos (θ s)),
      sq_nonneg (deriv alpha s 1 - Real.sin (θ s))]
  have e1 : deriv alpha s 1 = Real.sin (θ s) := by
    nlinarith [sq_nonneg (deriv alpha s 0 - Real.cos (θ s)),
      sq_nonneg (deriv alpha s 1 - Real.sin (θ s))]
  ext i
  fin_cases i
  · simpa using e0
  · simpa using e1

theorem solution
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2)) (theta : ℝ → ℝ)
    (halpha : IsClosedUnitSpeedCurve l alpha)
    (htheta : IsAngleFunction alpha theta) :
    ∀ s, signedCurvature alpha s = deriv theta s := by
  apply W2c_DoCarmoDG_sc_angle <;> assumption
