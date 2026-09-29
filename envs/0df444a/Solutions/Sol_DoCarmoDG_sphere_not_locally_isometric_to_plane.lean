-- Prove2me | solution 1 for DoCarmoDG.sphere_not_locally_isometric_to_plane
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:09:01.753162+00:00
-- url     : https://prove2.me/submissions/84d8e885-7660-47bb-877b-17b051bbd8a0

import Mathlib
import Definitions.Def_DoCarmo_surface_patch

/-! 7cd9ac71 DoCarmoDG.sphere_not_locally_isometric_to_plane (do Carmo §4-3).
Reuses the Theorema Egregium development of 17a9a4b7 (Brioschi-style, Clairaut via
`ContDiffAt.isSymmSndFDerivAt`). On the sphere patch, `n = x_u ∧ x_v` is parallel to `x`
and `⟨x_uu,x⟩ = -E`, `⟨x_uv,x⟩ = -F`, `⟨x_vv,x⟩ = -G`, so `K = 1`; on the plane patch
`x_u, x_v, x_uu, x_uv ⊥ N`, so `e = f = 0` and `K = 0`. Equal `E, F, G` on `U` would force
equal `K` at a point of `U`, i.e. `1 = 0`. -/

set_option autoImplicit false

namespace SpherePlane7cd

open DoCarmoDG Filter Topology

/-! ## Pointwise algebra in ℝ³ -/

theorem eg_inner3 (a b : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem eg_cross0 (a b : EuclideanSpace ℝ (Fin 3)) :
    cross a b 0 = a 1 * b 2 - a 2 * b 1 := by simp [cross]

theorem eg_cross1 (a b : EuclideanSpace ℝ (Fin 3)) :
    cross a b 1 = a 2 * b 0 - a 0 * b 2 := by simp [cross]

theorem eg_cross2 (a b : EuclideanSpace ℝ (Fin 3)) :
    cross a b 2 = a 0 * b 1 - a 1 * b 0 := by simp [cross]

/-- Lagrange's identity `|a ∧ b|² = EG - F²`. -/
theorem eg_lagrange (a b : EuclideanSpace ℝ (Fin 3)) :
    ‖cross a b‖ ^ 2 = inner ℝ a a * inner ℝ b b - inner ℝ a b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [eg_inner3, eg_cross0, eg_cross1, eg_cross2]
  ring

/-- `det(a,b,A) det(a,b,C) - det(a,b,B)²` as a Gram-determinant expression (Cauchy–Binet). -/
theorem eg_gram (a b A B C : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (cross a b) A * inner ℝ (cross a b) C - inner ℝ (cross a b) B ^ 2 =
      (inner ℝ A C - inner ℝ B B) * (inner ℝ a a * inner ℝ b b - inner ℝ a b ^ 2)
      - inner ℝ a a * (inner ℝ C b * inner ℝ A b - inner ℝ B b ^ 2)
      + inner ℝ a b * (inner ℝ C b * inner ℝ A a + inner ℝ C a * inner ℝ A b
          - 2 * inner ℝ B a * inner ℝ B b)
      - inner ℝ b b * (inner ℝ C a * inner ℝ A a - inner ℝ B a ^ 2) := by
  simp only [eg_inner3, eg_cross0, eg_cross1, eg_cross2]
  ring

/-- Brioschi-type expression of `K` through inner products of first and second partials. -/
noncomputable def egPhi (E F G r s pB qB pC qC w : ℝ) : ℝ :=
  (w * (E * G - F ^ 2) - E * (qC * s - qB ^ 2) + F * (qC * r + pC * s - 2 * pB * qB)
    - G * (pC * r - pB ^ 2)) / (E * G - F ^ 2) ^ 2

theorem eg_K_formula (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) :
    gaussCurvature x u v =
      egPhi (coeffE x u v) (coeffF x u v) (coeffG x u v)
        (inner ℝ (partialU (partialU x) u v) (partialU x u v))
        (inner ℝ (partialU (partialU x) u v) (partialV x u v))
        (inner ℝ (partialV (partialU x) u v) (partialU x u v))
        (inner ℝ (partialV (partialU x) u v) (partialV x u v))
        (inner ℝ (partialV (partialV x) u v) (partialU x u v))
        (inner ℝ (partialV (partialV x) u v) (partialV x u v))
        (inner ℝ (partialU (partialU x) u v) (partialV (partialV x) u v) -
          inner ℝ (partialV (partialU x) u v) (partialV (partialU x) u v)) := by
  have hg := eg_gram (partialU x u v) (partialV x u v) (partialU (partialU x) u v)
    (partialV (partialU x) u v) (partialV (partialV x) u v)
  have hl := eg_lagrange (partialU x u v) (partialV x u v)
  simp only [gaussCurvature, coeffe, coefff, coeffg, unitNormal, coeffE, coeffF, coeffG,
    real_inner_smul_left, egPhi]
  rw [← hg]
  generalize inner ℝ (partialU x u v) (partialU x u v) * inner ℝ (partialV x u v) (partialV x u v)
    - inner ℝ (partialU x u v) (partialV x u v) ^ 2 = D at hl ⊢
  generalize ‖cross (partialU x u v) (partialV x u v)‖ = m at hl ⊢
  generalize inner ℝ (cross (partialU x u v) (partialV x u v)) (partialU (partialU x) u v) = X
  generalize inner ℝ (cross (partialU x u v) (partialV x u v)) (partialV (partialU x) u v) = Y
  generalize inner ℝ (cross (partialU x u v) (partialV x u v)) (partialV (partialV x) u v) = Z
  have hinv : m⁻¹ ^ 2 = D⁻¹ := by rw [inv_pow, hl]
  calc (m⁻¹ * X * (m⁻¹ * Z) - (m⁻¹ * Y) ^ 2) / D = m⁻¹ ^ 2 * (X * Z - Y ^ 2) / D := by ring
    _ = D⁻¹ * (X * Z - Y ^ 2) / D := by rw [hinv]
    _ = (X * Z - Y ^ 2) / D ^ 2 := by ring

/-! ## Curried partial derivatives of a smooth map on an open set -/

theorem eg_evU {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u v : ℝ} (hp : (u, v) ∈ U) :
    ∀ᶠ t in 𝓝 u, (t, v) ∈ U :=
  (Continuous.prodMk_left v).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)

theorem eg_evV {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u v : ℝ} (hp : (u, v) ∈ U) :
    ∀ᶠ t in 𝓝 v, (u, t) ∈ U :=
  (Continuous.prodMk_right u).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)

theorem eg_lineU (u v : ℝ) : HasDerivAt (fun t : ℝ => (t, v)) ((1 : ℝ), (0 : ℝ)) u :=
  (hasDerivAt_id u).prodMk (hasDerivAt_const u v)

theorem eg_lineV (u v : ℝ) : HasDerivAt (fun t : ℝ => (u, t)) ((0 : ℝ), (1 : ℝ)) v :=
  (hasDerivAt_const v u).prodMk (hasDerivAt_id v)

theorem eg_hasDerivAt_u {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f t v) (fderiv ℝ (Function.uncurry f) (u, v) ((1 : ℝ), (0 : ℝ))) u := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (u, v) :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt u (eg_lineU u v)

theorem eg_hasDerivAt_v {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f u t) (fderiv ℝ (Function.uncurry f) (u, v) ((0 : ℝ), (1 : ℝ))) v := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (u, v) :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt v (eg_lineV u v)

theorem eg_pU {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f t v) (partialU f u v) u := by
  have h := eg_hasDerivAt_u hU hf hp
  rw [partialU, h.deriv]; exact h

theorem eg_pV {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f u t) (partialV f u v) v := by
  have h := eg_hasDerivAt_v hU hf hp
  rw [partialV, h.deriv]; exact h

theorem eg_smoothU {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (partialU f)) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (Function.uncurry f) q ((1 : ℝ), (0 : ℝ))) U :=
    h1.clm_apply contDiffOn_const
  refine h2.congr ?_
  rintro ⟨u, v⟩ hp
  exact (eg_hasDerivAt_u hU hf hp).deriv

theorem eg_smoothV {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (partialV f)) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (Function.uncurry f) q ((0 : ℝ), (1 : ℝ))) U :=
    h1.clm_apply contDiffOn_const
  refine h2.congr ?_
  rintro ⟨u, v⟩ hp
  exact (eg_hasDerivAt_v hU hf hp).deriv

/-- Clairaut: `f_vu = f_uv` on `U`. -/
theorem eg_symm {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    partialU (partialV f) u v = partialV (partialU f) u v := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have hDd : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (u, v) :=
    (hD.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have e1 : (fun t => partialV f t v) =ᶠ[𝓝 u]
      (fun t => fderiv ℝ (Function.uncurry f) (t, v) ((0 : ℝ), (1 : ℝ))) := by
    filter_upwards [eg_evU hU hp] with t ht
    exact (eg_hasDerivAt_v hU hf ht).deriv
  have e2 : (fun t => partialU f u t) =ᶠ[𝓝 v]
      (fun t => fderiv ℝ (Function.uncurry f) (u, t) ((1 : ℝ), (0 : ℝ))) := by
    filter_upwards [eg_evV hU hp] with t ht
    exact (eg_hasDerivAt_u hU hf ht).deriv
  have d1 : HasDerivAt (fun t => fderiv ℝ (Function.uncurry f) (t, v) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (u, v) ((1 : ℝ), (0 : ℝ))
        ((0 : ℝ), (1 : ℝ))) u := by
    have h := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3))
      ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt u
      (hDd.hasFDerivAt.comp_hasDerivAt u (eg_lineU u v))
    simpa [Function.comp_def] using h
  have d2 : HasDerivAt (fun t => fderiv ℝ (Function.uncurry f) (u, t) ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (u, v) ((0 : ℝ), (1 : ℝ))
        ((1 : ℝ), (0 : ℝ))) v := by
    have h := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3))
      ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp_hasDerivAt v
      (hDd.hasFDerivAt.comp_hasDerivAt v (eg_lineV u v))
    simpa [Function.comp_def] using h
  have hsymm := (hf.contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  show deriv (fun t => partialV f t v) u = deriv (fun t => partialU f u t) v
  rw [e1.deriv_eq, e2.deriv_eq, d1.deriv, d2.deriv]
  exact hsymm _ _

/-- Real functions that agree on the open set `U` have equal partial derivatives there. -/
theorem eg_congrU {U : Set (ℝ × ℝ)} (hU : IsOpen U) {g h : ℝ → ℝ → ℝ}
    (hgh : ∀ p ∈ U, g p.1 p.2 = h p.1 p.2) {u v : ℝ} (hp : (u, v) ∈ U) :
    deriv (fun t => g t v) u = deriv (fun t => h t v) u := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eg_evU hU hp] with t ht
  exact hgh _ ht

theorem eg_congrV {U : Set (ℝ × ℝ)} (hU : IsOpen U) {g h : ℝ → ℝ → ℝ}
    (hgh : ∀ p ∈ U, g p.1 p.2 = h p.1 p.2) {u v : ℝ} (hp : (u, v) ∈ U) :
    deriv (fun t => g u t) v = deriv (fun t => h u t) v := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eg_evV hU hp] with t ht
  exact hgh _ ht

/-! ## Derivatives of the first fundamental form -/

theorem eg_first_order {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry x) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    deriv (fun t => coeffE x t v) u =
        2 * inner ℝ (partialU (partialU x) u v) (partialU x u v) ∧
      deriv (fun t => coeffE x u t) v =
        2 * inner ℝ (partialV (partialU x) u v) (partialU x u v) ∧
      deriv (fun t => coeffG x t v) u =
        2 * inner ℝ (partialV (partialU x) u v) (partialV x u v) ∧
      deriv (fun t => coeffG x u t) v =
        2 * inner ℝ (partialV (partialV x) u v) (partialV x u v) ∧
      deriv (fun t => coeffF x t v) u =
        inner ℝ (partialU (partialU x) u v) (partialV x u v) +
          inner ℝ (partialV (partialU x) u v) (partialU x u v) ∧
      deriv (fun t => coeffF x u t) v =
        inner ℝ (partialV (partialU x) u v) (partialV x u v) +
          inner ℝ (partialV (partialV x) u v) (partialU x u v) := by
  have hxu := eg_smoothU hU hx
  have hxv := eg_smoothV hU hx
  have haU := eg_pU hU hxu hp
  have haV := eg_pV hU hxu hp
  have hbU := eg_pU hU hxv hp
  have hbV := eg_pV hU hxv hp
  rw [eg_symm hU hx hp] at hbU
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (fun t => coeffE x t v) = fun t => inner ℝ (partialU x t v) (partialU x t v) from rfl,
      (haU.inner ℝ haU).deriv, real_inner_comm]; ring
  · rw [show (fun t => coeffE x u t) = fun t => inner ℝ (partialU x u t) (partialU x u t) from rfl,
      (haV.inner ℝ haV).deriv, real_inner_comm]; ring
  · rw [show (fun t => coeffG x t v) = fun t => inner ℝ (partialV x t v) (partialV x t v) from rfl,
      (hbU.inner ℝ hbU).deriv, real_inner_comm]; ring
  · rw [show (fun t => coeffG x u t) = fun t => inner ℝ (partialV x u t) (partialV x u t) from rfl,
      (hbV.inner ℝ hbV).deriv, real_inner_comm]; ring
  · rw [show (fun t => coeffF x t v) = fun t => inner ℝ (partialU x t v) (partialV x t v) from rfl,
      (haU.inner ℝ hbU).deriv, real_inner_comm (partialU x u v)]; ring
  · rw [show (fun t => coeffF x u t) = fun t => inner ℝ (partialU x u t) (partialV x u t) from rfl,
      (haV.inner ℝ hbV).deriv, real_inner_comm (partialU x u v)]; ring

/-- `⟨x_uu, x_vv⟩ - |x_uv|² = (⟨x_uu, x_v⟩)_v - (⟨x_uv, x_v⟩)_u`, using `x_uuv = x_uvu`. -/
theorem eg_second_order {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry x) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    deriv (fun t => inner ℝ (partialU (partialU x) u t) (partialV x u t)) v -
        deriv (fun t => inner ℝ (partialV (partialU x) t v) (partialV x t v)) u =
      inner ℝ (partialU (partialU x) u v) (partialV (partialV x) u v) -
        inner ℝ (partialV (partialU x) u v) (partialV (partialU x) u v) := by
  have hxu := eg_smoothU hU hx
  have hxv := eg_smoothV hU hx
  have hxuu := eg_smoothU hU hxu
  have hxuv := eg_smoothV hU hxu
  have hAV := eg_pV hU hxuu hp
  have hBU := eg_pU hU hxuv hp
  have hbU := eg_pU hU hxv hp
  have hbV := eg_pV hU hxv hp
  rw [eg_symm hU hx hp] at hbU
  rw [eg_symm hU hxu hp] at hBU
  rw [(hAV.inner ℝ hbV).deriv, (hBU.inner ℝ hbU).deriv]
  ring

/-! ## Theorema Egregium -/

theorem egregium (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (x y : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x) (hy : IsRegularPatch U y)
    (hE : ∀ p ∈ U, coeffE x p.1 p.2 = coeffE y p.1 p.2)
    (hF : ∀ p ∈ U, coeffF x p.1 p.2 = coeffF y p.1 p.2)
    (hG : ∀ p ∈ U, coeffG x p.1 p.2 = coeffG y p.1 p.2) :
    ∀ p ∈ U, gaussCurvature x p.1 p.2 = gaussCurvature y p.1 p.2 := by
  have hxs := hx.1
  have hys := hy.1
  -- the six first-order inner products agree on `U`
  have key : ∀ p ∈ U,
      inner ℝ (partialU (partialU x) p.1 p.2) (partialU x p.1 p.2) =
          inner ℝ (partialU (partialU y) p.1 p.2) (partialU y p.1 p.2) ∧
        inner ℝ (partialV (partialU x) p.1 p.2) (partialU x p.1 p.2) =
          inner ℝ (partialV (partialU y) p.1 p.2) (partialU y p.1 p.2) ∧
        inner ℝ (partialV (partialU x) p.1 p.2) (partialV x p.1 p.2) =
          inner ℝ (partialV (partialU y) p.1 p.2) (partialV y p.1 p.2) ∧
        inner ℝ (partialV (partialV x) p.1 p.2) (partialV x p.1 p.2) =
          inner ℝ (partialV (partialV y) p.1 p.2) (partialV y p.1 p.2) ∧
        inner ℝ (partialU (partialU x) p.1 p.2) (partialV x p.1 p.2) =
          inner ℝ (partialU (partialU y) p.1 p.2) (partialV y p.1 p.2) ∧
        inner ℝ (partialV (partialV x) p.1 p.2) (partialU x p.1 p.2) =
          inner ℝ (partialV (partialV y) p.1 p.2) (partialU y p.1 p.2) := by
    rintro ⟨u, v⟩ hp
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := eg_first_order hU hxs hp
    obtain ⟨y1, y2, y3, y4, y5, y6⟩ := eg_first_order hU hys hp
    have eEu := eg_congrU hU hE hp
    have eEv := eg_congrV hU hE hp
    have eGu := eg_congrU hU hG hp
    have eGv := eg_congrV hU hG hp
    have eFu := eg_congrU hU hF hp
    have eFv := eg_congrV hU hF hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith
  rintro ⟨u, v⟩ hp
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := key (u, v) hp
  dsimp only at k1 k2 k3 k4 k5 k6 ⊢
  have hw : inner ℝ (partialU (partialU x) u v) (partialV (partialV x) u v) -
        inner ℝ (partialV (partialU x) u v) (partialV (partialU x) u v) =
      inner ℝ (partialU (partialU y) u v) (partialV (partialV y) u v) -
        inner ℝ (partialV (partialU y) u v) (partialV (partialU y) u v) := by
    rw [← eg_second_order hU hxs hp, ← eg_second_order hU hys hp]
    have h5 := eg_congrV hU
      (g := fun a b => inner ℝ (partialU (partialU x) a b) (partialV x a b))
      (h := fun a b => inner ℝ (partialU (partialU y) a b) (partialV y a b))
      (fun p hq => (key p hq).2.2.2.2.1) hp
    have h3 := eg_congrU hU
      (g := fun a b => inner ℝ (partialV (partialU x) a b) (partialV x a b))
      (h := fun a b => inner ℝ (partialV (partialU y) a b) (partialV y a b))
      (fun p hq => (key p hq).2.2.1) hp
    rw [h5, h3]
  rw [eg_K_formula x u v, eg_K_formula y u v, hE (u, v) hp, hF (u, v) hp, hG (u, v) hp,
    k1, k2, k3, k4, k5, k6, hw]


/-! ## Sphere is not locally isometric to a plane -/

/-- If `⟪φ, ψ⟫` is constant on `U`, both its partial derivatives vanish there. -/
theorem sp_inner_const {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {φ ψ : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ) U)
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry ψ) U) {c : ℝ}
    (hc : ∀ p ∈ U, inner ℝ (φ p.1 p.2) (ψ p.1 p.2) = c) {u v : ℝ} (hp : (u, v) ∈ U) :
    inner ℝ (partialU φ u v) (ψ u v) + inner ℝ (φ u v) (partialU ψ u v) = 0 ∧
      inner ℝ (partialV φ u v) (ψ u v) + inner ℝ (φ u v) (partialV ψ u v) = 0 := by
  constructor
  · have h := (eg_pU hU hφ hp).inner ℝ (eg_pU hU hψ hp)
    have e : (fun t => inner ℝ (φ t v) (ψ t v)) =ᶠ[𝓝 u] fun _ => c := by
      filter_upwards [eg_evU hU hp] with t ht
      exact hc (t, v) ht
    have h2 := h.deriv
    rw [e.deriv_eq, deriv_const] at h2
    linarith
  · have h := (eg_pV hU hφ hp).inner ℝ (eg_pV hU hψ hp)
    have e : (fun t => inner ℝ (φ u t) (ψ u t)) =ᶠ[𝓝 v] fun _ => c := by
      filter_upwards [eg_evV hU hp] with t ht
      exact hc (u, t) ht
    have h2 := h.deriv
    rw [e.deriv_eq, deriv_const] at h2
    linarith

/-- `det(a,b,A) |w|² = ⟨a,w⟩ det(b,A,w) + ⟨b,w⟩ det(A,a,w) + ⟨A,w⟩ det(a,b,w)`. -/
theorem sp_triple (a b A w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (cross a b) A * inner ℝ w w =
      inner ℝ a w * inner ℝ (cross b A) w + inner ℝ b w * inner ℝ (cross A a) w +
        inner ℝ A w * inner ℝ (cross a b) w := by
  simp only [eg_inner3, eg_cross0, eg_cross1, eg_cross2]
  ring

/-- `|n|²|w|² - ⟨n,w⟩² = |w ∧ n|²` with `w ∧ (a ∧ b) = ⟨w,b⟩a - ⟨w,a⟩b`. -/
theorem sp_lam (a b w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (cross a b) (cross a b) * inner ℝ w w - inner ℝ (cross a b) w ^ 2 =
      inner ℝ b w ^ 2 * inner ℝ a a - 2 * inner ℝ a w * inner ℝ b w * inner ℝ a b +
        inner ℝ a w ^ 2 * inner ℝ b b := by
  simp only [eg_inner3, eg_cross0, eg_cross1, eg_cross2]
  ring

theorem sp_sphere_K (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ)
    (h1 : inner ℝ (x u v) (x u v) = 1)
    (ha : inner ℝ (partialU x u v) (x u v) = 0)
    (hb : inner ℝ (partialV x u v) (x u v) = 0)
    (hA : inner ℝ (partialU (partialU x) u v) (x u v) = -coeffE x u v)
    (hB : inner ℝ (partialV (partialU x) u v) (x u v) = -coeffF x u v)
    (hC : inner ℝ (partialV (partialV x) u v) (x u v) = -coeffG x u v)
    (hn : cross (partialU x u v) (partialV x u v) ≠ 0) :
    gaussCurvature x u v = 1 := by
  have tA := sp_triple (partialU x u v) (partialV x u v) (partialU (partialU x) u v) (x u v)
  have tB := sp_triple (partialU x u v) (partialV x u v) (partialV (partialU x) u v) (x u v)
  have tC := sp_triple (partialU x u v) (partialV x u v) (partialV (partialV x) u v) (x u v)
  have hl := sp_lam (partialU x u v) (partialV x u v) (x u v)
  have hm : ‖cross (partialU x u v) (partialV x u v)‖ ^ 2 =
      coeffE x u v * coeffG x u v - coeffF x u v ^ 2 := eg_lagrange _ _
  have hnn : inner ℝ (cross (partialU x u v) (partialV x u v))
      (cross (partialU x u v) (partialV x u v)) =
      ‖cross (partialU x u v) (partialV x u v)‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [h1, ha, hb, hA] at tA
  rw [h1, ha, hb, hB] at tB
  rw [h1, ha, hb, hC] at tC
  rw [h1, ha, hb, hnn] at hl
  have hm0 : ‖cross (partialU x u v) (partialV x u v)‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  simp only [gaussCurvature, coeffe, coefff, coeffg, unitNormal, real_inner_smul_left]
  generalize ‖cross (partialU x u v) (partialV x u v)‖ = m at hm hm0 hl ⊢
  generalize inner ℝ (cross (partialU x u v) (partialV x u v)) (x u v) = L at tA tB tC hl
  generalize inner ℝ (cross (partialU x u v) (partialV x u v)) (partialU (partialU x) u v) = X
    at tA ⊢
  generalize inner ℝ (cross (partialU x u v) (partialV x u v)) (partialV (partialU x) u v) = Y
    at tB ⊢
  generalize inner ℝ (cross (partialU x u v) (partialV x u v)) (partialV (partialV x) u v) = Z
    at tC ⊢
  generalize coeffE x u v = E at hm tA ⊢
  generalize coeffF x u v = F at hm tB ⊢
  generalize coeffG x u v = G at hm tC ⊢
  have hL : L ^ 2 = m ^ 2 := by linarith
  have hD : E * G - F ^ 2 ≠ 0 := by rw [← hm]; exact pow_ne_zero 2 hm0
  rw [div_eq_one_iff_eq hD]
  have hX : X = -E * L := by linarith
  have hY : Y = -F * L := by linarith
  have hZ : Z = -G * L := by linarith
  rw [hX, hY, hZ]
  have hmi : m⁻¹ ^ 2 * m ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hm0, one_pow]
  calc m⁻¹ * (-E * L) * (m⁻¹ * (-G * L)) - (m⁻¹ * (-F * L)) ^ 2
      = m⁻¹ ^ 2 * L ^ 2 * (E * G - F ^ 2) := by ring
    _ = E * G - F ^ 2 := by rw [hL, hmi, one_mul]

theorem sp_plane_K (y : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ)
    (N : EuclideanSpace ℝ (Fin 3)) (hN : N ≠ 0)
    (ha : inner ℝ (partialU y u v) N = 0)
    (hb : inner ℝ (partialV y u v) N = 0)
    (hA : inner ℝ (partialU (partialU y) u v) N = 0)
    (hB : inner ℝ (partialV (partialU y) u v) N = 0) :
    gaussCurvature y u v = 0 := by
  have tA := sp_triple (partialU y u v) (partialV y u v) (partialU (partialU y) u v) N
  have tB := sp_triple (partialU y u v) (partialV y u v) (partialV (partialU y) u v) N
  rw [ha, hb, hA] at tA
  rw [ha, hb, hB] at tB
  have hNN : inner ℝ N N ≠ 0 := inner_self_ne_zero.mpr hN
  have eA : inner ℝ (cross (partialU y u v) (partialV y u v)) (partialU (partialU y) u v) = 0 := by
    have : inner ℝ (cross (partialU y u v) (partialV y u v)) (partialU (partialU y) u v) *
        inner ℝ N N = 0 := by rw [tA]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hNN
  have eB : inner ℝ (cross (partialU y u v) (partialV y u v)) (partialV (partialU y) u v) = 0 := by
    have : inner ℝ (cross (partialU y u v) (partialV y u v)) (partialV (partialU y) u v) *
        inner ℝ N N = 0 := by rw [tB]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hNN
  simp only [gaussCurvature, coeffe, coefff, unitNormal, real_inner_smul_left, eA, eB]
  ring

theorem sphere_plane (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (x y : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x) (hy : IsRegularPatch U y)
    (hsphere : ∀ p ∈ U, ‖x p.1 p.2‖ = 1)
    (q N : EuclideanSpace ℝ (Fin 3)) (hN : N ≠ 0)
    (hplane : ∀ p ∈ U, inner ℝ (y p.1 p.2 - q) N = 0) :
    ¬ (∀ p ∈ U,
        coeffE x p.1 p.2 = coeffE y p.1 p.2 ∧
        coeffF x p.1 p.2 = coeffF y p.1 p.2 ∧
        coeffG x p.1 p.2 = coeffG y p.1 p.2) := by
  intro h
  obtain ⟨⟨u, v⟩, hp⟩ := hne
  have hK := egregium U hU x y hx hy (fun p hq => (h p hq).1) (fun p hq => (h p hq).2.1)
    (fun p hq => (h p hq).2.2) (u, v) hp
  have hxs := hx.1
  have hys := hy.1
  -- sphere side
  have h1 : ∀ p ∈ U, inner ℝ (x p.1 p.2) (x p.1 p.2) = 1 := by
    intro p hq
    rw [real_inner_self_eq_norm_sq, hsphere p hq]
    norm_num
  have ha' : ∀ p ∈ U, inner ℝ (partialU x p.1 p.2) (x p.1 p.2) = 0 := by
    rintro ⟨a, b⟩ hq
    have := (sp_inner_const hU hxs hxs h1 hq).1
    rw [real_inner_comm (partialU x a b) (x a b)] at this
    dsimp only
    linarith
  have hb' : ∀ p ∈ U, inner ℝ (partialV x p.1 p.2) (x p.1 p.2) = 0 := by
    rintro ⟨a, b⟩ hq
    have := (sp_inner_const hU hxs hxs h1 hq).2
    rw [real_inner_comm (partialV x a b) (x a b)] at this
    dsimp only
    linarith
  have sU := sp_inner_const hU (eg_smoothU hU hxs) hxs ha' hp
  have sV := sp_inner_const hU (eg_smoothV hU hxs) hxs hb' hp
  have hKx : gaussCurvature x u v = 1 := by
    apply sp_sphere_K x u v (h1 (u, v) hp) (ha' (u, v) hp) (hb' (u, v) hp)
    · have := sU.1; unfold coeffE; linarith
    · have := sU.2; unfold coeffF; linarith
    · have := sV.2; unfold coeffG; linarith
    · exact hx.2 (u, v) hp
  -- plane side
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (fun _ _ : ℝ => N)) U := contDiffOn_const
  have hpU : ∀ a b : ℝ, partialU (fun _ _ : ℝ => N) a b = 0 := by
    intro a b; simp [partialU]
  have hpV : ∀ a b : ℝ, partialV (fun _ _ : ℝ => N) a b = 0 := by
    intro a b; simp [partialV]
  have hq : ∀ p ∈ U, inner ℝ (y p.1 p.2) ((fun _ _ : ℝ => N) p.1 p.2) = inner ℝ q N := by
    intro p hq
    have := hplane p hq
    rw [inner_sub_left] at this
    dsimp only
    linarith
  have pa : ∀ p ∈ U, inner ℝ (partialU y p.1 p.2) ((fun _ _ : ℝ => N) p.1 p.2) = 0 := by
    rintro ⟨a, b⟩ hq'
    have := (sp_inner_const hU hys hc hq hq').1
    rw [hpU, inner_zero_right, add_zero] at this
    exact this
  have pb : ∀ p ∈ U, inner ℝ (partialV y p.1 p.2) ((fun _ _ : ℝ => N) p.1 p.2) = 0 := by
    rintro ⟨a, b⟩ hq'
    have := (sp_inner_const hU hys hc hq hq').2
    rw [hpV, inner_zero_right, add_zero] at this
    exact this
  have pAB := sp_inner_const hU (eg_smoothU hU hys) hc pa hp
  simp only [hpU, hpV, inner_zero_right, add_zero] at pAB
  have hKy : gaussCurvature y u v = 0 :=
    sp_plane_K y u v N hN (pa (u, v) hp) (pb (u, v) hp) pAB.1 pAB.2
  rw [hKx, hKy] at hK
  norm_num at hK

end SpherePlane7cd

set_option maxHeartbeats 4000000 in
open DoCarmoDG in
theorem solution
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (x y : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x) (hy : IsRegularPatch U y)
    (hsphere : ∀ p ∈ U, ‖x p.1 p.2‖ = 1)
    (q N : EuclideanSpace ℝ (Fin 3)) (hN : N ≠ 0)
    (hplane : ∀ p ∈ U, inner ℝ (y p.1 p.2 - q) N = 0) :
    ¬ (∀ p ∈ U,
        coeffE x p.1 p.2 = coeffE y p.1 p.2 ∧
        coeffF x p.1 p.2 = coeffF y p.1 p.2 ∧
        coeffG x p.1 p.2 = coeffG y p.1 p.2) := by
  exact SpherePlane7cd.sphere_plane U hU hne x y hx hy hsphere q N hN hplane
