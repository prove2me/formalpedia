-- Prove2me | solution 1 for DoCarmoDG.gauss_curvature_orthogonal_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T16:12:33.870432+00:00
-- url     : https://prove2.me/submissions/865b316e-147b-46d0-b38a-b17c52ba28a5

import Mathlib
import Definitions.Def_DoCarmo_surface_patch

/-! e880c1f4 DoCarmoDG.gauss_curvature_orthogonal_parametrization (do Carmo §4-3, Ex. 1).
Brioschi route reused from our theorema_egregium proof (17a9a4b7): K = egPhi(E,F,G,...) with
the six first-order products and ⟨x_uu,x_vv⟩-|x_uv|² expressed through derivatives of E,F,G.
With F ≡ 0 on U, the products become ±E_u/2, ±E_v/2, ±G_u/2, ±G_v/2 and
⟨x_uu,x_vv⟩-|x_uv|² = -(E_vv+G_uu)/2; the right-hand side is expanded with the quotient and
square-root rules (EG > 0 by Lagrange's identity and regularity), and both sides agree by field_simp/ring. -/

set_option autoImplicit false

namespace OrthoKBuild

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


/-! ## Generic curried partials of a smooth (real or vector) function -/

section Gen
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem gen_hasDerivAt_u {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f t v) (fderiv ℝ (Function.uncurry f) (u, v) ((1 : ℝ), (0 : ℝ))) u := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (u, v) :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt u (eg_lineU u v)

theorem gen_hasDerivAt_v {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f u t) (fderiv ℝ (Function.uncurry f) (u, v) ((0 : ℝ), (1 : ℝ))) v := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (u, v) :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt v (eg_lineV u v)

theorem gen_pU {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f t v) (deriv (fun t => f t v) u) u := by
  have h := gen_hasDerivAt_u hU hf hp
  rw [h.deriv]; exact h

theorem gen_pV {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f u t) (deriv (fun t => f u t) v) v := by
  have h := gen_hasDerivAt_v hU hf hp
  rw [h.deriv]; exact h

theorem gen_smoothU {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (fun a b => deriv (fun t => f t b) a)) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (Function.uncurry f) q ((1 : ℝ), (0 : ℝ))) U :=
    h1.clm_apply contDiffOn_const
  refine h2.congr ?_
  rintro ⟨u, v⟩ hp
  exact (gen_hasDerivAt_u hU hf hp).deriv

theorem gen_smoothV {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (fun a b => deriv (fun t => f a t) b)) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (Function.uncurry f) q ((0 : ℝ), (1 : ℝ))) U :=
    h1.clm_apply contDiffOn_const
  refine h2.congr ?_
  rintro ⟨u, v⟩ hp
  exact (gen_hasDerivAt_v hU hf hp).deriv

end Gen

theorem ok_smoothE {U : Set (ℝ × ℝ)} (hU : IsOpen U) {x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry x) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (coeffE x)) U := by
  have h := eg_smoothU hU hx
  have : Function.uncurry (coeffE x) =
      fun q => inner ℝ (Function.uncurry (partialU x) q) (Function.uncurry (partialU x) q) := by
    funext q; rfl
  rw [this]; exact h.inner ℝ h

theorem ok_smoothG {U : Set (ℝ × ℝ)} (hU : IsOpen U) {x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry x) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (coeffG x)) U := by
  have h := eg_smoothV hU hx
  have : Function.uncurry (coeffG x) =
      fun q => inner ℝ (Function.uncurry (partialV x) q) (Function.uncurry (partialV x) q) := by
    funext q; rfl
  rw [this]; exact h.inner ℝ h

theorem orthoK (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (hF : ∀ p ∈ U, coeffF x p.1 p.2 = 0) :
    ∀ p ∈ U,
      gaussCurvature x p.1 p.2 =
        -(1 / (2 * Real.sqrt (coeffE x p.1 p.2 * coeffG x p.1 p.2))) *
          (deriv (fun t =>
              deriv (fun r => coeffE x p.1 r) t /
                Real.sqrt (coeffE x p.1 t * coeffG x p.1 t)) p.2 +
            deriv (fun t =>
              deriv (fun r => coeffG x r p.2) t /
                Real.sqrt (coeffE x t p.2 * coeffG x t p.2)) p.1) := by
  have hxs := hx.1
  rintro ⟨u, v⟩ hp
  dsimp only
  -- first-order identities at every point of U
  have fo := fun (q : ℝ × ℝ) (hq : q ∈ U) => eg_first_order (u := q.1) (v := q.2) hU hxs hq
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := fo (u, v) hp
  have hFu : deriv (fun t => coeffF x t v) u = 0 := by
    rw [eg_congrU hU (h := fun _ _ => (0 : ℝ)) hF hp]; simp
  have hFv : deriv (fun t => coeffF x u t) v = 0 := by
    rw [eg_congrV hU (h := fun _ _ => (0 : ℝ)) hF hp]; simp
  -- ⟨x_uu, x_v⟩ = -E_v/2 and ⟨x_uv, x_v⟩ = G_u/2 on U
  have hs : ∀ q ∈ U, inner ℝ (partialU (partialU x) q.1 q.2) (partialV x q.1 q.2) =
      (-(1 / 2 : ℝ)) * deriv (fun r => coeffE x q.1 r) q.2 := by
    intro q hq
    obtain ⟨_, k2, _, _, k5, _⟩ := fo q hq
    have : deriv (fun t => coeffF x t q.2) q.1 = 0 := by
      rw [eg_congrU hU (h := fun _ _ => (0 : ℝ)) hF hq]; simp
    linarith
  have hq' : ∀ q ∈ U, inner ℝ (partialV (partialU x) q.1 q.2) (partialV x q.1 q.2) =
      (1 / 2 : ℝ) * deriv (fun r => coeffG x r q.2) q.1 := by
    intro q hq
    obtain ⟨_, _, k3, _, _, _⟩ := fo q hq
    linarith
  have hw := eg_second_order hU hxs hp
  rw [eg_congrV hU (g := fun a b => inner ℝ (partialU (partialU x) a b) (partialV x a b))
      (h := fun a b => (-(1 / 2 : ℝ)) * deriv (fun r => coeffE x a r) b) hs hp,
    eg_congrU hU (g := fun a b => inner ℝ (partialV (partialU x) a b) (partialV x a b))
      (h := fun a b => (1 / 2 : ℝ) * deriv (fun r => coeffG x r b) a) hq' hp,
    deriv_const_mul_field', deriv_const_mul_field'] at hw
  -- positivity of EG
  have hEG : 0 < coeffE x u v * coeffG x u v := by
    have hl := eg_lagrange (partialU x u v) (partialV x u v)
    have hc := hx.2 (u, v) hp
    have hn : 0 < ‖cross (partialU x u v) (partialV x u v)‖ := norm_pos_iff.2 hc
    have hF0 := hF (u, v) hp
    simp only [coeffE, coeffF, coeffG] at hF0 ⊢
    rw [hF0] at hl
    nlinarith
  -- derivatives of E, G and their first partials
  have sE := ok_smoothE hU hxs
  have sG := ok_smoothG hU hxs
  have dEv := gen_pV hU sE hp
  have dGv := gen_pV hU sG hp
  have dEu := gen_pU hU sE hp
  have dGu := gen_pU hU sG hp
  have dEvv := gen_pV hU (gen_smoothV hU sE) hp
  have dGuu := gen_pU hU (gen_smoothU hU sG) hp
  have hsq : Real.sqrt (coeffE x u v * coeffG x u v) ^ 2 = coeffE x u v * coeffG x u v :=
    Real.sq_sqrt hEG.le
  have hsqpos : 0 < Real.sqrt (coeffE x u v * coeffG x u v) := Real.sqrt_pos.2 hEG
  have DV : HasDerivAt
      (fun t => deriv (fun r => coeffE x u r) t / Real.sqrt (coeffE x u t * coeffG x u t))
      ((deriv (fun t => deriv (fun r => coeffE x u r) t) v * Real.sqrt (coeffE x u v * coeffG x u v) -
        deriv (fun r => coeffE x u r) v *
          ((deriv (fun r => coeffE x u r) v * coeffG x u v +
              coeffE x u v * deriv (fun r => coeffG x u r) v) /
            (2 * Real.sqrt (coeffE x u v * coeffG x u v)))) /
        Real.sqrt (coeffE x u v * coeffG x u v) ^ 2) v :=
    dEvv.div ((dEv.mul dGv).sqrt hEG.ne') hsqpos.ne'
  have DU : HasDerivAt
      (fun t => deriv (fun r => coeffG x r v) t / Real.sqrt (coeffE x t v * coeffG x t v))
      ((deriv (fun t => deriv (fun r => coeffG x r v) t) u * Real.sqrt (coeffE x u v * coeffG x u v) -
        deriv (fun r => coeffG x r v) u *
          ((deriv (fun r => coeffE x r v) u * coeffG x u v +
              coeffE x u v * deriv (fun r => coeffG x r v) u) /
            (2 * Real.sqrt (coeffE x u v * coeffG x u v)))) /
        Real.sqrt (coeffE x u v * coeffG x u v) ^ 2) u :=
    dGuu.div ((dEu.mul dGu).sqrt hEG.ne') hsqpos.ne'
  dsimp only at h1 h2 h3 h4 h5 h6
  have hw' : inner ℝ (partialU (partialU x) u v) (partialV (partialV x) u v) -
      inner ℝ (partialV (partialU x) u v) (partialV (partialU x) u v) =
      -(1 / 2) * deriv (fun t => deriv (fun r => coeffE x u r) t) v -
        1 / 2 * deriv (fun t => deriv (fun r => coeffG x r v) t) u := by
    rw [← hw]
  have hs0 : inner ℝ (partialU (partialU x) u v) (partialV x u v) =
      -(1 / 2) * deriv (fun r => coeffE x u r) v := hs (u, v) hp
  have hpC : inner ℝ (partialV (partialV x) u v) (partialU x u v) =
      -(1 / 2) * deriv (fun r => coeffG x r v) u := by linarith
  have hr : inner ℝ (partialU (partialU x) u v) (partialU x u v) =
      (1 / 2) * deriv (fun r => coeffE x r v) u := by linarith
  have hpB : inner ℝ (partialV (partialU x) u v) (partialU x u v) =
      (1 / 2) * deriv (fun r => coeffE x u r) v := by linarith
  have hqB : inner ℝ (partialV (partialU x) u v) (partialV x u v) =
      (1 / 2) * deriv (fun r => coeffG x r v) u := by linarith
  have hqC : inner ℝ (partialV (partialV x) u v) (partialV x u v) =
      (1 / 2) * deriv (fun r => coeffG x u r) v := by linarith
  have hE0 : 0 ≤ coeffE x u v := real_inner_self_nonneg
  rw [DV.deriv, DU.deriv, eg_K_formula x u v, hF (u, v) hp, hw', hs0, hpC, hr, hpB, hqB, hqC]
  generalize deriv (fun t => deriv (fun r => coeffE x u r) t) v = Evv at *
  generalize deriv (fun t => deriv (fun r => coeffG x r v) t) u = Guu at *
  generalize deriv (fun r => coeffE x u r) v = Ev at *
  generalize deriv (fun r => coeffE x r v) u = Eu at *
  generalize deriv (fun r => coeffG x u r) v = Gv at *
  generalize deriv (fun r => coeffG x r v) u = Gu at *
  generalize Real.sqrt (coeffE x u v * coeffG x u v) = W at *
  generalize coeffE x u v = E at *
  generalize coeffG x u v = G at *
  have hEne : E ≠ 0 := by
    rintro rfl; simp at hEG
  have hGW : G = W ^ 2 / E := by field_simp; linarith
  subst hGW
  have hWne : W ≠ 0 := hsqpos.ne'
  unfold egPhi
  field_simp
  ring

end OrthoKBuild

open DoCarmoDG in
theorem solution
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (hF : ∀ p ∈ U, coeffF x p.1 p.2 = 0) :
    ∀ p ∈ U,
      gaussCurvature x p.1 p.2 =
        -(1 / (2 * Real.sqrt (coeffE x p.1 p.2 * coeffG x p.1 p.2))) *
          (deriv (fun t =>
              deriv (fun r => coeffE x p.1 r) t /
                Real.sqrt (coeffE x p.1 t * coeffG x p.1 t)) p.2 +
            deriv (fun t =>
              deriv (fun r => coeffG x r p.2) t /
                Real.sqrt (coeffE x t p.2 * coeffG x t p.2)) p.1) := by
  exact OrthoKBuild.orthoK U hU x hx hF

