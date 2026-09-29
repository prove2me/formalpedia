-- Prove2me | solution 1 for DoCarmoDG.gauss_curvature_reparametrization_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:22:04.358054+00:00
-- url     : https://prove2.me/submissions/4894f73a-bbe1-4a3f-97be-6673a06d499e

import Mathlib
import Definitions.Def_DoCarmo_surface_patch

/-! 878e3afd DoCarmoDG.gauss_curvature_reparametrization_invariant (do Carmo §2-3, §3-3).
Route: pointwise `K = (⟨n,x_uu⟩⟨n,x_vv⟩ - ⟨n,x_uv⟩²)/|n|⁴` with `n = x_u ∧ x_v`
(Lagrange: `EG - F² = |n|²`). For `x = y ∘ ψ` on the open set `U`, the curried chain rule
gives `x_u = a y_u + c y_v`, `x_v = b y_u + d y_v` and second partials of the form
`(Jacobian quadratic form in y_uu, y_uv, y_vv) + (tangential terms)`, using Clairaut
`y_vu = y_uv`. Then `n_x = (ad - bc) n_y`, the tangential terms die against `n_y`, and the
numerator and denominator of `K` both scale by `(ad - bc)⁴`, which is nonzero because
`n_x ≠ 0` (regularity of `x`). The inverse map `phi` is not needed. -/

set_option autoImplicit false

namespace RepInvBuild

open DoCarmoDG Filter Topology

/-! ## Pointwise algebra in ℝ³ -/

theorem ri_inner3 (a b : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem ri_cross0 (a b : EuclideanSpace ℝ (Fin 3)) :
    cross a b 0 = a 1 * b 2 - a 2 * b 1 := by simp [cross]

theorem ri_cross1 (a b : EuclideanSpace ℝ (Fin 3)) :
    cross a b 1 = a 2 * b 0 - a 0 * b 2 := by simp [cross]

theorem ri_cross2 (a b : EuclideanSpace ℝ (Fin 3)) :
    cross a b 2 = a 0 * b 1 - a 1 * b 0 := by simp [cross]

theorem ri_lagrange (a b : EuclideanSpace ℝ (Fin 3)) :
    ‖cross a b‖ ^ 2 = inner ℝ a a * inner ℝ b b - inner ℝ a b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [ri_inner3, ri_cross0, ri_cross1, ri_cross2]
  ring

theorem ri_nP (P Q : EuclideanSpace ℝ (Fin 3)) : inner ℝ (cross P Q) P = 0 := by
  simp only [ri_inner3, ri_cross0, ri_cross1, ri_cross2]
  ring

theorem ri_nQ (P Q : EuclideanSpace ℝ (Fin 3)) : inner ℝ (cross P Q) Q = 0 := by
  simp only [ri_inner3, ri_cross0, ri_cross1, ri_cross2]
  ring

theorem ri_cross_lin (P Q : EuclideanSpace ℝ (Fin 3)) (a b c d : ℝ) :
    cross (a • P + c • Q) (b • P + d • Q) = (a * d - b * c) • cross P Q := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- The curvature as a function of the first and second partials. -/
noncomputable def Kf (a b A B C : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (inner ℝ (cross a b) A * inner ℝ (cross a b) C - inner ℝ (cross a b) B ^ 2) /
    (‖cross a b‖ ^ 2) ^ 2

theorem ri_K_formula (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) :
    gaussCurvature x u v =
      Kf (partialU x u v) (partialV x u v) (partialU (partialU x) u v)
        (partialV (partialU x) u v) (partialV (partialV x) u v) := by
  have hl := ri_lagrange (partialU x u v) (partialV x u v)
  simp only [gaussCurvature, coeffe, coefff, coeffg, unitNormal, coeffE, coeffF, coeffG,
    real_inner_smul_left, Kf]
  rw [← hl]
  generalize ‖cross (partialU x u v) (partialV x u v)‖ = m
  generalize inner ℝ (cross (partialU x u v) (partialV x u v)) (partialU (partialU x) u v) = X
  generalize inner ℝ (cross (partialU x u v) (partialV x u v)) (partialV (partialU x) u v) = Y
  generalize inner ℝ (cross (partialU x u v) (partialV x u v)) (partialV (partialV x) u v) = Z
  ring

theorem ri_Kf_invariant (P Q A B C : EuclideanSpace ℝ (Fin 3))
    (a b c d a1 c1 m1 m2 n1 n2 : ℝ) (hδ : a * d - b * c ≠ 0) :
    Kf (a • P + c • Q) (b • P + d • Q)
      (a • (a • A + c • B) + a1 • P + (c • (a • B + c • C) + c1 • Q))
      (a • (b • A + d • B) + m1 • P + (c • (b • B + d • C) + m2 • Q))
      (b • (b • A + d • B) + n1 • P + (d • (b • B + d • C) + n2 • Q)) = Kf P Q A B C := by
  have hP : inner ℝ (cross P Q) P = 0 := ri_nP P Q
  have hQ : inner ℝ (cross P Q) Q = 0 := ri_nQ P Q
  have hn : ‖(a * d - b * c) • cross P Q‖ ^ 2 = (a * d - b * c) ^ 2 * ‖cross P Q‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [Kf, ri_cross_lin, hn, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hP, hQ, mul_zero, add_zero]
  generalize ‖cross P Q‖ = m
  generalize inner ℝ (cross P Q) A = X
  generalize inner ℝ (cross P Q) B = Y
  generalize inner ℝ (cross P Q) C = Z
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    simp
  · rw [div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (pow_ne_zero 2 hδ) (pow_ne_zero 2 hm)))
      (pow_ne_zero 2 (pow_ne_zero 2 hm))]
    ring

/-! ## Curried partial derivatives, valued in any real normed space -/

section Calc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def PU (f : ℝ → ℝ → F) (u v : ℝ) : F := deriv (fun t => f t v) u

noncomputable def PV (f : ℝ → ℝ → F) (u v : ℝ) : F := deriv (fun t => f u t) v

theorem ri_evU {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u v : ℝ} (hp : (u, v) ∈ U) :
    ∀ᶠ t in 𝓝 u, (t, v) ∈ U :=
  (Continuous.prodMk_left v).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)

theorem ri_evV {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u v : ℝ} (hp : (u, v) ∈ U) :
    ∀ᶠ t in 𝓝 v, (u, t) ∈ U :=
  (Continuous.prodMk_right u).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)

theorem ri_lineU (u v : ℝ) : HasDerivAt (fun t : ℝ => (t, v)) ((1 : ℝ), (0 : ℝ)) u :=
  (hasDerivAt_id u).prodMk (hasDerivAt_const u v)

theorem ri_lineV (u v : ℝ) : HasDerivAt (fun t : ℝ => (u, t)) ((0 : ℝ), (1 : ℝ)) v :=
  (hasDerivAt_const v u).prodMk (hasDerivAt_id v)

theorem ri_fdU {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f t v) (fderiv ℝ (Function.uncurry f) (u, v) ((1 : ℝ), (0 : ℝ))) u := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (u, v) :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt u (ri_lineU u v)

theorem ri_fdV {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f u t) (fderiv ℝ (Function.uncurry f) (u, v) ((0 : ℝ), (1 : ℝ))) v := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (u, v) :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt v (ri_lineV u v)

theorem ri_pU {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f t v) (PU f u v) u := by
  have h := ri_fdU hU hf hp
  rw [PU, h.deriv]; exact h

theorem ri_pV {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f u t) (PV f u v) v := by
  have h := ri_fdV hU hf hp
  rw [PV, h.deriv]; exact h

theorem ri_smoothU {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (PU f)) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (Function.uncurry f) q ((1 : ℝ), (0 : ℝ))) U :=
    h1.clm_apply contDiffOn_const
  refine h2.congr ?_
  rintro ⟨u, v⟩ hp
  exact (ri_fdU hU hf hp).deriv

theorem ri_smoothV {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (PV f)) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (Function.uncurry f) q ((0 : ℝ), (1 : ℝ))) U :=
    h1.clm_apply contDiffOn_const
  refine h2.congr ?_
  rintro ⟨u, v⟩ hp
  exact (ri_fdV hU hf hp).deriv

/-- Clairaut: `f_vu = f_uv` on `U`. -/
theorem ri_symm {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    PU (PV f) u v = PV (PU f) u v := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have hDd : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (u, v) :=
    (hD.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have e1 : (fun t => PV f t v) =ᶠ[𝓝 u]
      (fun t => fderiv ℝ (Function.uncurry f) (t, v) ((0 : ℝ), (1 : ℝ))) := by
    filter_upwards [ri_evU hU hp] with t ht
    exact (ri_fdV hU hf ht).deriv
  have e2 : (fun t => PU f u t) =ᶠ[𝓝 v]
      (fun t => fderiv ℝ (Function.uncurry f) (u, t) ((1 : ℝ), (0 : ℝ))) := by
    filter_upwards [ri_evV hU hp] with t ht
    exact (ri_fdU hU hf ht).deriv
  have d1 : HasDerivAt (fun t => fderiv ℝ (Function.uncurry f) (t, v) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (u, v) ((1 : ℝ), (0 : ℝ))
        ((0 : ℝ), (1 : ℝ))) u := by
    have h := (ContinuousLinearMap.apply ℝ F
      ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt u
      (hDd.hasFDerivAt.comp_hasDerivAt u (ri_lineU u v))
    simpa [Function.comp_def] using h
  have d2 : HasDerivAt (fun t => fderiv ℝ (Function.uncurry f) (u, t) ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (u, v) ((0 : ℝ), (1 : ℝ))
        ((1 : ℝ), (0 : ℝ))) v := by
    have h := (ContinuousLinearMap.apply ℝ F
      ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp_hasDerivAt v
      (hDd.hasFDerivAt.comp_hasDerivAt v (ri_lineV u v))
    simpa [Function.comp_def] using h
  have hsymm := (hf.contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  show deriv (fun t => PV f t v) u = deriv (fun t => PU f u t) v
  rw [e1.deriv_eq, e2.deriv_eq, d1.deriv, d2.deriv]
  exact hsymm _ _

/-- Chain rule along a curve through the domain of a curried smooth map. -/
theorem ri_chain {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) V) {γ : ℝ → ℝ × ℝ} {γ' : ℝ × ℝ}
    {t : ℝ} (hγ : HasDerivAt γ γ' t) (hmem : γ t ∈ V) :
    HasDerivAt (fun s => f (γ s).1 (γ s).2)
      (γ'.1 • PU f (γ t).1 (γ t).2 + γ'.2 • PV f (γ t).1 (γ t).2) t := by
  have hmem' : ((γ t).1, (γ t).2) ∈ V := hmem
  have hd : DifferentiableAt ℝ (Function.uncurry f) (γ t) :=
    (hf.contDiffAt (hV.mem_nhds hmem)).differentiableAt (by simp)
  have h := hd.hasFDerivAt.comp_hasDerivAt t hγ
  have hu := (ri_fdU hV hf hmem').deriv
  have hv := (ri_fdV hV hf hmem').deriv
  rw [Prod.mk.eta] at hu hv
  have e : fderiv ℝ (Function.uncurry f) (γ t) γ' =
      γ'.1 • PU f (γ t).1 (γ t).2 + γ'.2 • PV f (γ t).1 (γ t).2 := by
    have hγ' : γ' = γ'.1 • ((1 : ℝ), (0 : ℝ)) + γ'.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [PU, PV, hu, hv]
    conv_lhs => rw [hγ']
    rw [map_add, map_smul, map_smul]
  rw [e] at h
  exact h

theorem ri_fst {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).1) f'.1 t :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h

theorem ri_snd {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).2) f'.2 t :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h

end Calc

theorem ri_partialU (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) : partialU x = PU x := rfl

theorem ri_partialV (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) : partialV x = PV x := rfl

/-! ## The invariance theorem -/

theorem main (U V : Set (ℝ × ℝ)) (hU : IsOpen U) (hV : IsOpen V)
    (x y : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x) (hy : IsRegularPatch V y)
    (ψ : ℝ → ℝ → ℝ × ℝ) (hψ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry ψ) U)
    (hmaps : ∀ a b, (a, b) ∈ U → ψ a b ∈ V)
    (hcomp : ∀ a b, (a, b) ∈ U → x a b = y (ψ a b).1 (ψ a b).2) :
    ∀ u v, (u, v) ∈ U → gaussCurvature x u v = gaussCurvature y (ψ u v).1 (ψ u v).2 := by
  have hys := hy.1
  have hyu := ri_smoothU hV hys
  have hyv := ri_smoothV hV hys
  have hψu := ri_smoothU hU hψ
  have hψv := ri_smoothV hU hψ
  -- first-order chain rule on `U`
  have foU : ∀ a b, (a, b) ∈ U → PU x a b =
      (PU ψ a b).1 • PU y (ψ a b).1 (ψ a b).2 + (PU ψ a b).2 • PV y (ψ a b).1 (ψ a b).2 := by
    intro a b hq
    have hc := ri_chain hV hys (ri_pU hU hψ hq) (hmaps a b hq)
    have hev : (fun t => x t b) =ᶠ[𝓝 a] (fun t => y (ψ t b).1 (ψ t b).2) := by
      filter_upwards [ri_evU hU hq] with t ht
      exact hcomp t b ht
    exact (hc.congr_of_eventuallyEq hev).deriv
  have foV : ∀ a b, (a, b) ∈ U → PV x a b =
      (PV ψ a b).1 • PU y (ψ a b).1 (ψ a b).2 + (PV ψ a b).2 • PV y (ψ a b).1 (ψ a b).2 := by
    intro a b hq
    have hc := ri_chain hV hys (ri_pV hU hψ hq) (hmaps a b hq)
    have hev : (fun t => x a t) =ᶠ[𝓝 b] (fun t => y (ψ a t).1 (ψ a t).2) := by
      filter_upwards [ri_evV hU hq] with t ht
      exact hcomp a t ht
    exact (hc.congr_of_eventuallyEq hev).deriv
  intro u v hp
  have hq := hmaps u v hp
  have hq' : ((ψ u v).1, (ψ u v).2) ∈ V := hq
  have hsym := ri_symm hV hys hq'
  -- second-order chain rule at `(u, v)`
  have huu : PU (PU x) u v =
      (PU ψ u v).1 • ((PU ψ u v).1 • PU (PU y) (ψ u v).1 (ψ u v).2 +
          (PU ψ u v).2 • PV (PU y) (ψ u v).1 (ψ u v).2) +
        (PU (PU ψ) u v).1 • PU y (ψ u v).1 (ψ u v).2 +
      ((PU ψ u v).2 • ((PU ψ u v).1 • PU (PV y) (ψ u v).1 (ψ u v).2 +
          (PU ψ u v).2 • PV (PV y) (ψ u v).1 (ψ u v).2) +
        (PU (PU ψ) u v).2 • PV y (ψ u v).1 (ψ u v).2) := by
    have h1 := ri_fst (ri_pU hU hψu hp)
    have h2 := ri_chain hV hyu (ri_pU hU hψ hp) hq
    have h3 := ri_snd (ri_pU hU hψu hp)
    have h4 := ri_chain hV hyv (ri_pU hU hψ hp) hq
    have hd := (h1.smul h2).add (h3.smul h4)
    have hev : (fun t => PU x t v) =ᶠ[𝓝 u] (fun t =>
        (PU ψ t v).1 • PU y (ψ t v).1 (ψ t v).2 + (PU ψ t v).2 • PV y (ψ t v).1 (ψ t v).2) := by
      filter_upwards [ri_evU hU hp] with t ht
      exact foU t v ht
    exact (hd.congr_of_eventuallyEq hev).deriv
  have huv : PV (PU x) u v =
      (PU ψ u v).1 • ((PV ψ u v).1 • PU (PU y) (ψ u v).1 (ψ u v).2 +
          (PV ψ u v).2 • PV (PU y) (ψ u v).1 (ψ u v).2) +
        (PV (PU ψ) u v).1 • PU y (ψ u v).1 (ψ u v).2 +
      ((PU ψ u v).2 • ((PV ψ u v).1 • PU (PV y) (ψ u v).1 (ψ u v).2 +
          (PV ψ u v).2 • PV (PV y) (ψ u v).1 (ψ u v).2) +
        (PV (PU ψ) u v).2 • PV y (ψ u v).1 (ψ u v).2) := by
    have h1 := ri_fst (ri_pV hU hψu hp)
    have h2 := ri_chain hV hyu (ri_pV hU hψ hp) hq
    have h3 := ri_snd (ri_pV hU hψu hp)
    have h4 := ri_chain hV hyv (ri_pV hU hψ hp) hq
    have hd := (h1.smul h2).add (h3.smul h4)
    have hev : (fun t => PU x u t) =ᶠ[𝓝 v] (fun t =>
        (PU ψ u t).1 • PU y (ψ u t).1 (ψ u t).2 + (PU ψ u t).2 • PV y (ψ u t).1 (ψ u t).2) := by
      filter_upwards [ri_evV hU hp] with t ht
      exact foU u t ht
    exact (hd.congr_of_eventuallyEq hev).deriv
  have hvv : PV (PV x) u v =
      (PV ψ u v).1 • ((PV ψ u v).1 • PU (PU y) (ψ u v).1 (ψ u v).2 +
          (PV ψ u v).2 • PV (PU y) (ψ u v).1 (ψ u v).2) +
        (PV (PV ψ) u v).1 • PU y (ψ u v).1 (ψ u v).2 +
      ((PV ψ u v).2 • ((PV ψ u v).1 • PU (PV y) (ψ u v).1 (ψ u v).2 +
          (PV ψ u v).2 • PV (PV y) (ψ u v).1 (ψ u v).2) +
        (PV (PV ψ) u v).2 • PV y (ψ u v).1 (ψ u v).2) := by
    have h1 := ri_fst (ri_pV hU hψv hp)
    have h2 := ri_chain hV hyu (ri_pV hU hψ hp) hq
    have h3 := ri_snd (ri_pV hU hψv hp)
    have h4 := ri_chain hV hyv (ri_pV hU hψ hp) hq
    have hd := (h1.smul h2).add (h3.smul h4)
    have hev : (fun t => PV x u t) =ᶠ[𝓝 v] (fun t =>
        (PV ψ u t).1 • PU y (ψ u t).1 (ψ u t).2 + (PV ψ u t).2 • PV y (ψ u t).1 (ψ u t).2) := by
      filter_upwards [ri_evV hU hp] with t ht
      exact foV u t ht
    exact (hd.congr_of_eventuallyEq hev).deriv
  have hu1 := foU u v hp
  have hv1 := foV u v hp
  -- the Jacobian determinant is nonzero by regularity of `x`
  have hδ : (PU ψ u v).1 * (PV ψ u v).2 - (PV ψ u v).1 * (PU ψ u v).2 ≠ 0 := by
    intro h0
    apply hx.2 (u, v) hp
    show cross (PU x u v) (PV x u v) = 0
    rw [hu1, hv1, ri_cross_lin, h0, zero_smul]
  rw [ri_K_formula x u v, ri_K_formula y (ψ u v).1 (ψ u v).2]
  simp only [ri_partialU, ri_partialV]
  rw [hu1, hv1, huu, huv, hvv, hsym]
  exact ri_Kf_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hδ

end RepInvBuild

open DoCarmoDG in
theorem solution
    (U V : Set (ℝ × ℝ)) (hU : IsOpen U) (hV : IsOpen V)
    (x y : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x) (hy : IsRegularPatch V y)
    (psi phi : ℝ × ℝ → ℝ × ℝ)
    (hpsi : ContDiffOn ℝ (⊤ : ℕ∞) psi U) (hphi : ContDiffOn ℝ (⊤ : ℕ∞) phi V)
    (hmaps : Set.MapsTo psi U V) (hmaps' : Set.MapsTo phi V U)
    (hleft : ∀ p ∈ U, phi (psi p) = p) (hright : ∀ q ∈ V, psi (phi q) = q)
    (hcomp : ∀ p ∈ U, x p.1 p.2 = y (psi p).1 (psi p).2) :
    ∀ p ∈ U, gaussCurvature x p.1 p.2 = gaussCurvature y (psi p).1 (psi p).2 := by
  rintro ⟨u, v⟩ hp
  have huc : Function.uncurry (fun a b => psi (a, b)) = psi := by
    funext q
    rfl
  exact RepInvBuild.main U V hU hV x y hx hy (fun a b => psi (a, b)) (huc ▸ hpsi)
    (fun a b h => hmaps h) (fun a b h => hcomp (a, b) h) u v hp
