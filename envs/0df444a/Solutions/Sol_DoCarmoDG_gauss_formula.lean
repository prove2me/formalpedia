-- Prove2me | solution 1 for DoCarmoDG.gauss_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:23:38.294371+00:00
-- url     : https://prove2.me/submissions/6eb7749c-f6f7-4718-94d8-82d4026cdeb4

import Mathlib
import Definitions.Def_DoCarmo_surface_patch

/-! 4790fe05 DoCarmoDG.gauss_formula (do Carmo §4-3, equation (5)).
Route: on the open set `U` the Christoffel symbols are forced by the linear systems
  ⟨x_ij, x_u⟩ = Γ¹ᵢⱼ E + Γ²ᵢⱼ F,  ⟨x_ij, x_v⟩ = Γ¹ᵢⱼ F + Γ²ᵢⱼ G   (⟨N, x_u⟩ = ⟨N, x_v⟩ = 0),
so Γ²₁₁ and Γ²₁₂ agree on `U` with explicit quotients of inner products of partials of `x`.
Their partial derivatives are computed by the product/quotient rules (curried partials,
Clairaut `x_uuv = x_uvu`), the third-order terms cancel, and what remains is a rational
identity which, together with the Brioschi-type formula for `K` (Cauchy–Binet, reused from
the accepted Theorema Egregium proof 17a9a4b7), closes by `field_simp; ring`. -/

set_option autoImplicit false

namespace GaussFormulaBuild

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


/-! ## The Christoffel symbols on `U` -/

theorem gf_cross_left (a b : EuclideanSpace ℝ (Fin 3)) : inner ℝ (cross a b) a = 0 := by
  simp only [eg_inner3, eg_cross0, eg_cross1, eg_cross2]
  ring

theorem gf_cross_right (a b : EuclideanSpace ℝ (Fin 3)) : inner ℝ (cross a b) b = 0 := by
  simp only [eg_inner3, eg_cross0, eg_cross1, eg_cross2]
  ring

theorem gf_normal_u (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) :
    inner ℝ (unitNormal x u v) (partialU x u v) = 0 := by
  rw [unitNormal, real_inner_smul_left, gf_cross_left, mul_zero]

theorem gf_normal_v (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) :
    inner ℝ (unitNormal x u v) (partialV x u v) = 0 := by
  rw [unitNormal, real_inner_smul_left, gf_cross_right, mul_zero]

theorem gf_coeffs (a b n A : EuclideanSpace ℝ (Fin 3)) (g1 g2 e : ℝ)
    (hA : A = g1 • a + g2 • b + e • n) (hna : inner ℝ n a = 0) (hnb : inner ℝ n b = 0)
    (hD : inner ℝ a a * inner ℝ b b - inner ℝ a b * inner ℝ a b ≠ 0) :
    g1 = (inner ℝ b b * inner ℝ A a - inner ℝ a b * inner ℝ A b) /
        (inner ℝ a a * inner ℝ b b - inner ℝ a b * inner ℝ a b) ∧
      g2 = (inner ℝ a a * inner ℝ A b - inner ℝ a b * inner ℝ A a) /
        (inner ℝ a a * inner ℝ b b - inner ℝ a b * inner ℝ a b) := by
  have h1 : inner ℝ A a = g1 * inner ℝ a a + g2 * inner ℝ a b := by
    rw [hA, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, hna, real_inner_comm a b]
    ring
  have h2 : inner ℝ A b = g1 * inner ℝ a b + g2 * inner ℝ b b := by
    rw [hA, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, hnb]
    ring
  constructor
  · rw [eq_div_iff hD]
    linear_combination (-(inner ℝ b b)) * h1 + inner ℝ a b * h2
  · rw [eq_div_iff hD]
    linear_combination (-(inner ℝ a a)) * h2 + inner ℝ a b * h1

theorem gf_D_ne {U : Set (ℝ × ℝ)} {x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hx : IsRegularPatch U x) {u v : ℝ} (hp : (u, v) ∈ U) :
    coeffE x u v * coeffG x u v - coeffF x u v * coeffF x u v ≠ 0 := by
  have hc : cross (partialU x u v) (partialV x u v) ≠ 0 := hx.2 (u, v) hp
  have hl := eg_lagrange (partialU x u v) (partialV x u v)
  have hn : ‖cross (partialU x u v) (partialV x u v)‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.2 hc)
  intro h
  apply hn
  rw [hl]
  simp only [coeffE, coeffF, coeffG] at h
  linear_combination h

theorem gf_gamma {U : Set (ℝ × ℝ)} {x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hx : IsRegularPatch U x) {G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ}
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) {u v : ℝ} (hp : (u, v) ∈ U) :
    G111 u v = (coeffG x u v * inner ℝ (partialU (partialU x) u v) (partialU x u v) -
          coeffF x u v * inner ℝ (partialU (partialU x) u v) (partialV x u v)) /
        (coeffE x u v * coeffG x u v - coeffF x u v * coeffF x u v) ∧
      G211 u v = (coeffE x u v * inner ℝ (partialU (partialU x) u v) (partialV x u v) -
          coeffF x u v * inner ℝ (partialU (partialU x) u v) (partialU x u v)) /
        (coeffE x u v * coeffG x u v - coeffF x u v * coeffF x u v) ∧
      G112 u v = (coeffG x u v * inner ℝ (partialV (partialU x) u v) (partialU x u v) -
          coeffF x u v * inner ℝ (partialV (partialU x) u v) (partialV x u v)) /
        (coeffE x u v * coeffG x u v - coeffF x u v * coeffF x u v) ∧
      G212 u v = (coeffE x u v * inner ℝ (partialV (partialU x) u v) (partialV x u v) -
          coeffF x u v * inner ℝ (partialV (partialU x) u v) (partialU x u v)) /
        (coeffE x u v * coeffG x u v - coeffF x u v * coeffF x u v) ∧
      G122 u v = (coeffG x u v * inner ℝ (partialV (partialV x) u v) (partialU x u v) -
          coeffF x u v * inner ℝ (partialV (partialV x) u v) (partialV x u v)) /
        (coeffE x u v * coeffG x u v - coeffF x u v * coeffF x u v) ∧
      G222 u v = (coeffE x u v * inner ℝ (partialV (partialV x) u v) (partialV x u v) -
          coeffF x u v * inner ℝ (partialV (partialV x) u v) (partialU x u v)) /
        (coeffE x u v * coeffG x u v - coeffF x u v * coeffF x u v) := by
  obtain ⟨h1, h2, h3⟩ := hG (u, v) hp
  have hD := gf_D_ne hx hp
  have c1 := gf_coeffs _ _ _ _ _ _ _ h1 (gf_normal_u x u v) (gf_normal_v x u v) hD
  have c2 := gf_coeffs _ _ _ _ _ _ _ h2 (gf_normal_u x u v) (gf_normal_v x u v) hD
  have c3 := gf_coeffs _ _ _ _ _ _ _ h3 (gf_normal_u x u v) (gf_normal_v x u v) hD
  exact ⟨c1.1, c1.2, c2.1, c2.2, c3.1, c3.2⟩

/-! ## The Gauss formula -/

/-- The explicit value of `Γ²₁₁` on `U`. -/
noncomputable def gfG211 (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (s t : ℝ) : ℝ :=
  (coeffE x s t * inner ℝ (partialU (partialU x) s t) (partialV x s t) -
      coeffF x s t * inner ℝ (partialU (partialU x) s t) (partialU x s t)) /
    (coeffE x s t * coeffG x s t - coeffF x s t * coeffF x s t)

/-- The explicit value of `Γ²₁₂` on `U`. -/
noncomputable def gfG212 (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (s t : ℝ) : ℝ :=
  (coeffE x s t * inner ℝ (partialV (partialU x) s t) (partialV x s t) -
      coeffF x s t * inner ℝ (partialV (partialU x) s t) (partialU x s t)) /
    (coeffE x s t * coeffG x s t - coeffF x s t * coeffF x s t)

theorem gauss (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      deriv (fun t => G212 t p.2) p.1 - deriv (fun t => G211 p.1 t) p.2 +
          G112 p.1 p.2 * G211 p.1 p.2 + G212 p.1 p.2 * G212 p.1 p.2 -
          G211 p.1 p.2 * G222 p.1 p.2 - G111 p.1 p.2 * G212 p.1 p.2 =
        -(coeffE x p.1 p.2) * gaussCurvature x p.1 p.2 := by
  rintro ⟨u, v⟩ hp
  dsimp only
  have hxs := hx.1
  have hxu := eg_smoothU hU hxs
  have hxv := eg_smoothV hU hxs
  have hxuu := eg_smoothU hU hxu
  have hxuv := eg_smoothV hU hxu
  -- vector derivatives
  have ha_u : HasDerivAt (fun t => partialU x t v) (partialU (partialU x) u v) u :=
    eg_pU hU hxu hp
  have hb_u : HasDerivAt (fun t => partialV x t v) (partialV (partialU x) u v) u := by
    have h := eg_pU hU hxv hp
    rwa [eg_symm hU hxs hp] at h
  have hB_u : HasDerivAt (fun t => partialV (partialU x) t v)
      (partialV (partialU (partialU x)) u v) u := by
    have h := eg_pU hU hxuv hp
    rwa [eg_symm hU hxu hp] at h
  have ha_v : HasDerivAt (fun t => partialU x u t) (partialV (partialU x) u v) v :=
    eg_pV hU hxu hp
  have hb_v : HasDerivAt (fun t => partialV x u t) (partialV (partialV x) u v) v :=
    eg_pV hU hxv hp
  have hA_v : HasDerivAt (fun t => partialU (partialU x) u t)
      (partialV (partialU (partialU x)) u v) v :=
    eg_pV hU hxuu hp
  -- scalar derivatives along `u`
  have hE_u : HasDerivAt (fun t => coeffE x t v)
      (2 * inner ℝ (partialU (partialU x) u v) (partialU x u v)) u :=
    (ha_u.inner ℝ ha_u).congr_deriv (by
      rw [real_inner_comm (partialU (partialU x) u v) (partialU x u v)]; ring)
  have hF_u : HasDerivAt (fun t => coeffF x t v)
      (inner ℝ (partialU (partialU x) u v) (partialV x u v) +
        inner ℝ (partialV (partialU x) u v) (partialU x u v)) u :=
    (ha_u.inner ℝ hb_u).congr_deriv (by
      rw [real_inner_comm (partialV (partialU x) u v) (partialU x u v)]; ring)
  have hG_u : HasDerivAt (fun t => coeffG x t v)
      (2 * inner ℝ (partialV (partialU x) u v) (partialV x u v)) u :=
    (hb_u.inner ℝ hb_u).congr_deriv (by
      rw [real_inner_comm (partialV (partialU x) u v) (partialV x u v)]; ring)
  have hBb_u : HasDerivAt (fun t => inner ℝ (partialV (partialU x) t v) (partialV x t v))
      (inner ℝ (partialV (partialU (partialU x)) u v) (partialV x u v) +
        inner ℝ (partialV (partialU x) u v) (partialV (partialU x) u v)) u :=
    (hB_u.inner ℝ hb_u).congr_deriv (by ring)
  have hBa_u : HasDerivAt (fun t => inner ℝ (partialV (partialU x) t v) (partialU x t v))
      (inner ℝ (partialV (partialU (partialU x)) u v) (partialU x u v) +
        inner ℝ (partialU (partialU x) u v) (partialV (partialU x) u v)) u :=
    (hB_u.inner ℝ ha_u).congr_deriv (by
      rw [real_inner_comm (partialU (partialU x) u v) (partialV (partialU x) u v)]; ring)
  -- scalar derivatives along `v`
  have hE_v : HasDerivAt (fun t => coeffE x u t)
      (2 * inner ℝ (partialV (partialU x) u v) (partialU x u v)) v :=
    (ha_v.inner ℝ ha_v).congr_deriv (by
      rw [real_inner_comm (partialV (partialU x) u v) (partialU x u v)]; ring)
  have hF_v : HasDerivAt (fun t => coeffF x u t)
      (inner ℝ (partialV (partialU x) u v) (partialV x u v) +
        inner ℝ (partialV (partialV x) u v) (partialU x u v)) v :=
    (ha_v.inner ℝ hb_v).congr_deriv (by
      rw [real_inner_comm (partialV (partialV x) u v) (partialU x u v)]; ring)
  have hG_v : HasDerivAt (fun t => coeffG x u t)
      (2 * inner ℝ (partialV (partialV x) u v) (partialV x u v)) v :=
    (hb_v.inner ℝ hb_v).congr_deriv (by
      rw [real_inner_comm (partialV (partialV x) u v) (partialV x u v)]; ring)
  have hAb_v : HasDerivAt (fun t => inner ℝ (partialU (partialU x) u t) (partialV x u t))
      (inner ℝ (partialV (partialU (partialU x)) u v) (partialV x u v) +
        inner ℝ (partialU (partialU x) u v) (partialV (partialV x) u v)) v :=
    (hA_v.inner ℝ hb_v).congr_deriv (by ring)
  have hAa_v : HasDerivAt (fun t => inner ℝ (partialU (partialU x) u t) (partialU x u t))
      (inner ℝ (partialV (partialU (partialU x)) u v) (partialU x u v) +
        inner ℝ (partialU (partialU x) u v) (partialV (partialU x) u v)) v :=
    (hA_v.inner ℝ ha_v).congr_deriv (by ring)
  have hD := gf_D_ne hx hp
  have hq212 := ((hE_u.mul hBb_u).sub (hF_u.mul hBa_u)).div
    ((hE_u.mul hG_u).sub (hF_u.mul hF_u)) hD
  have hq211 := ((hE_v.mul hAb_v).sub (hF_v.mul hAa_v)).div
    ((hE_v.mul hG_v).sub (hF_v.mul hF_v)) hD
  have hG212 : ∀ q ∈ U, G212 q.1 q.2 = gfG212 x q.1 q.2 := by
    rintro ⟨s, t⟩ hq
    exact (gf_gamma hx hG hq).2.2.2.1
  have hG211 : ∀ q ∈ U, G211 q.1 q.2 = gfG211 x q.1 q.2 := by
    rintro ⟨s, t⟩ hq
    exact (gf_gamma hx hG hq).2.1
  have e212 := (eg_congrU hU (h := gfG212 x) hG212 hp).trans hq212.deriv
  have e211 := (eg_congrV hU (h := gfG211 x) hG211 hp).trans hq211.deriv
  rw [e212, e211]
  simp only [Pi.mul_apply, Pi.sub_apply]
  obtain ⟨g111, g211, g112, g212, -, g222⟩ := gf_gamma hx hG hp
  rw [g111, g211, g112, g212, g222, eg_K_formula x u v]
  simp only [egPhi]
  generalize inner ℝ (partialV (partialU (partialU x)) u v) (partialU x u v) = Ta
  generalize inner ℝ (partialV (partialU (partialU x)) u v) (partialV x u v) = Tb
  generalize inner ℝ (partialU (partialU x) u v) (partialV (partialU x) u v) = AB
  generalize inner ℝ (partialU (partialU x) u v) (partialV (partialV x) u v) = AC
  generalize inner ℝ (partialV (partialU x) u v) (partialV (partialU x) u v) = BB
  generalize inner ℝ (partialU (partialU x) u v) (partialU x u v) = Aa
  generalize inner ℝ (partialU (partialU x) u v) (partialV x u v) = Ab
  generalize inner ℝ (partialV (partialU x) u v) (partialU x u v) = Ba
  generalize inner ℝ (partialV (partialU x) u v) (partialV x u v) = Bb
  generalize inner ℝ (partialV (partialV x) u v) (partialU x u v) = Ca
  generalize inner ℝ (partialV (partialV x) u v) (partialV x u v) = Cb
  generalize coeffE x u v = E at hD ⊢
  generalize coeffF x u v = F at hD ⊢
  generalize coeffG x u v = G at hD ⊢
  have hD2 : E * G - F ^ 2 ≠ 0 := by rw [sq]; exact hD
  field_simp
  ring

end GaussFormulaBuild

open DoCarmoDG in
theorem solution
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      deriv (fun t => G212 t p.2) p.1 - deriv (fun t => G211 p.1 t) p.2 +
          G112 p.1 p.2 * G211 p.1 p.2 + G212 p.1 p.2 * G212 p.1 p.2 -
          G211 p.1 p.2 * G222 p.1 p.2 - G111 p.1 p.2 * G212 p.1 p.2 =
        -(coeffE x p.1 p.2) * gaussCurvature x p.1 p.2 := by
  exact GaussFormulaBuild.gauss U hU x hx G111 G211 G112 G212 G122 G222 hG
