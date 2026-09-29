-- Prove2me | solution 1 for DoCarmoDG.fundamental_theorem_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T14:19:18.506015+00:00
-- url     : https://prove2.me/submissions/0be8fd4c-d489-4202-a9db-3b83d761c63b

import Mathlib
import Definitions.Def_DoCarmo_local_theory_curves

/-! 7df30779 DoCarmoDG.fundamental_theorem_uniqueness (do Carmo 1-5, fundamental theorem of the local theory of curves).
Uniqueness: for an arc-length curve with curvature k > 0 the Frenet formulas are re-derived
(derivatives of the constant inner products + expansion in the orthonormal basis (t,n,b)).  rho maps
frame(alpha)(s0) to frame(beta)(s0) (OrthonormalBasis.equiv, det 1 via Basis.det_comp and the triple
product), the energy <rho t1,t2>+<rho n1,n2>+<rho b1,b2> is constant = 3, so rho t1 = t2 and
beta - rho alpha is constant.
No `Theorems.*` module is imported: every DoCarmoDG fact used is re-proved here. -/

set_option autoImplicit false

namespace FrenetBuild


open Set Filter Topology DoCarmoDG
open scoped NNReal

abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem norm_one_of_inner (v : E3) (h : inner ℝ v v = 1) : ‖v‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg v) two_ne_zero).1 (by rw [← real_inner_self_eq_norm_sq]; exact h)

theorem contDiff_cross : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 × E3 => cross p.1 p.2) := by
  unfold cross
  refine PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

theorem const_of_hasDerivAt_zero {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : ℝ → G} {p q : ℝ} (h : ∀ t ∈ Ioo p q, HasDerivAt g 0 t) {x y : ℝ}
    (hx : x ∈ Ioo p q) (hy : y ∈ Ioo p q) : g x = g y :=
  isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (h t ht).differentiableAt.differentiableWithinAt) (fun t ht => (h t ht).deriv) hx hy

theorem cross_apply (u v : E3) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 ∧ cross u v 1 = u 2 * v 0 - u 0 * v 2 ∧
      cross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  simp [cross]

theorem inner_eq3 (u v : E3) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem inner_cross_left (u v : E3) : inner ℝ u (cross u v) = 0 := by
  rw [inner_eq3]; obtain ⟨h0, h1, h2⟩ := cross_apply u v; rw [h0, h1, h2]; ring

theorem inner_cross_right (u v : E3) : inner ℝ v (cross u v) = 0 := by
  rw [inner_eq3]; obtain ⟨h0, h1, h2⟩ := cross_apply u v; rw [h0, h1, h2]; ring

theorem inner_cross_cross (u v : E3) :
    inner ℝ (cross u v) (cross u v) = inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 := by
  rw [inner_eq3, inner_eq3 u u, inner_eq3 v v, inner_eq3 u v]
  obtain ⟨h0, h1, h2⟩ := cross_apply u v; rw [h0, h1, h2]; ring

/-- Orthonormal basis from an orthonormal triple. -/
noncomputable def onb3 (T N B : E3) (h : Orthonormal ℝ ![T, N, B]) : OrthonormalBasis (Fin 3) ℝ E3 :=
  (basisOfOrthonormalOfCardEqFinrank h (by simp)).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact h)

theorem onb3_apply (T N B : E3) (h : Orthonormal ℝ ![T, N, B]) : ⇑(onb3 T N B h) = ![T, N, B] := by
  unfold onb3
  rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]

theorem orthonormal3 (T N B : E3) (h1 : inner ℝ T T = 1) (h2 : inner ℝ N N = 1)
    (h3 : inner ℝ B B = 1) (h4 : inner ℝ T N = 0) (h5 : inner ℝ T B = 0) (h6 : inner ℝ N B = 0) :
    Orthonormal ℝ ![T, N, B] := by
  have n1 := norm_one_of_inner T h1
  have n2 := norm_one_of_inner N h2
  have n3 := norm_one_of_inner B h3
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [n1, n2, n3, h4, h5, h6, real_inner_comm T N, real_inner_comm T B, real_inner_comm N B]

theorem expand3 (T N B : E3) (h : Orthonormal ℝ ![T, N, B]) (v : E3) :
    v = inner ℝ T v • T + inner ℝ N v • N + inner ℝ B v • B := by
  have := (onb3 T N B h).sum_repr' v
  rw [onb3_apply, Fin.sum_univ_three] at this
  simpa using this.symm

noncomputable def stdB : Module.Basis (Fin 3) ℝ E3 := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

theorem stdB_det (v : Fin 3 → E3) : stdB.det v = inner ℝ (cross (v 0) (v 1)) (v 2) := by
  rw [Module.Basis.det_apply, Matrix.det_fin_three, inner_eq3]
  obtain ⟨h0, h1, h2⟩ := cross_apply (v 0) (v 1)
  rw [h0, h1, h2]
  simp only [Module.Basis.toMatrix_apply, stdB, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]
  ring

theorem deriv_zero_of_const {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : ℝ → G}
    {g' : G} {a b s : ℝ} {c : G} (hg : HasDerivAt g g' s) (hs : s ∈ Ioo a b)
    (hc : ∀ u ∈ Ioo a b, g u = c) : g' = 0 :=
  hg.unique ((hasDerivAt_const s c).congr_of_eventuallyEq
    (show g =ᶠ[𝓝 s] fun _ => c from Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) hc))

theorem curve_frenet (a b : ℝ) (k τ : ℝ → ℝ) (hk : ContDiffOn ℝ (⊤ : ℕ∞) k (Ioo a b))
    (hkpos : ∀ s ∈ Ioo a b, 0 < k s) (α : ℝ → E3) (hα : IsArcLengthCurve (Ioo a b) α)
    (hkt : ∀ s ∈ Ioo a b, curvature α s = k s ∧ torsion α s = τ s) (s : ℝ) (hs : s ∈ Ioo a b) :
    HasDerivAt α (deriv α s) s ∧ HasDerivAt (deriv α) (k s • normal α s) s ∧
    HasDerivAt (normal α) (-(k s • deriv α s) - τ s • binormal α s) s ∧
    HasDerivAt (binormal α) (τ s • normal α s) s ∧
    inner ℝ (deriv α s) (deriv α s) = 1 ∧ inner ℝ (normal α s) (normal α s) = 1 ∧
    inner ℝ (binormal α s) (binormal α s) = 1 ∧ inner ℝ (deriv α s) (normal α s) = 0 ∧
    inner ℝ (deriv α s) (binormal α s) = 0 ∧ inner ℝ (normal α s) (binormal α s) = 0 := by
  obtain ⟨hα1, hα2⟩ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).1 hα.1
  obtain ⟨hα3, hα4⟩ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).1 hα2
  have hα5 : DifferentiableOn ℝ (deriv (deriv α)) (Ioo a b) := hα4.differentiableOn (by simp)
  have hkd : ∀ u ∈ Ioo a b, DifferentiableAt ℝ k u := fun u hu =>
    (hk.differentiableOn (by simp)).differentiableAt (Ioo_mem_nhds hu.1 hu.2)
  have hA2 : ∀ u ∈ Ioo a b, deriv (deriv α) u = k u • normal α u := by
    intro u hu
    rw [normal, (hkt u hu).1, smul_smul, mul_inv_cancel₀ (hkpos u hu).ne', one_smul]
  have hT : ∀ u ∈ Ioo a b, HasDerivAt (deriv α) (k u • normal α u) u := fun u hu => by
    rw [← hA2 u hu]
    exact (hα3.differentiableAt (Ioo_mem_nhds hu.1 hu.2)).hasDerivAt
  have hN : ∀ u ∈ Ioo a b, HasDerivAt (normal α) (deriv (normal α) u) u := by
    intro u hu
    have hev : normal α =ᶠ[𝓝 u] fun v => (k v)⁻¹ • deriv (deriv α) v :=
      Filter.eventually_of_mem (Ioo_mem_nhds hu.1 hu.2) fun v hv => by rw [normal, (hkt v hv).1]
    have hd : DifferentiableAt ℝ (fun v => (k v)⁻¹ • deriv (deriv α) v) u :=
      ((hkd u hu).inv (hkpos u hu).ne').smul (hα5.differentiableAt (Ioo_mem_nhds hu.1 hu.2))
    exact (hd.congr_of_eventuallyEq hev).hasDerivAt
  have hB : HasDerivAt (binormal α) (deriv (binormal α) s) s := by
    have h1 : DifferentiableAt ℝ (fun p : E3 × E3 => cross p.1 p.2) (deriv α s, normal α s) :=
      (contDiff_cross.differentiable (by simp)).differentiableAt
    exact (h1.comp s ((hα3.differentiableAt (Ioo_mem_nhds hs.1 hs.2)).prodMk
      (hN s hs).differentiableAt)).hasDerivAt
  have oTT : ∀ u ∈ Ioo a b, inner ℝ (deriv α u) (deriv α u) = 1 := fun u hu => by
    rw [real_inner_self_eq_norm_sq, hα.2 u hu]; norm_num
  have oNN : ∀ u ∈ Ioo a b, inner ℝ (normal α u) (normal α u) = 1 := by
    intro u hu
    have h1 : ‖deriv (deriv α) u‖ = k u := (hkt u hu).1
    have hk0 := (hkpos u hu).ne'
    rw [normal, (hkt u hu).1, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, h1]
    field_simp
  have oTN : ∀ u ∈ Ioo a b, inner ℝ (deriv α u) (normal α u) = 0 := by
    intro u hu
    have h := deriv_zero_of_const ((hT u hu).inner ℝ (hT u hu)) hu oTT
    rw [real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (deriv α u) (normal α u)] at h
    have h2 : k u * (2 * inner ℝ (deriv α u) (normal α u)) = 0 := by linarith
    have := (mul_eq_zero.1 h2).resolve_left (hkpos u hu).ne'
    linarith
  have oBB : ∀ u ∈ Ioo a b, inner ℝ (binormal α u) (binormal α u) = 1 := fun u hu => by
    rw [binormal, tangent, inner_cross_cross, oTT u hu, oNN u hu, oTN u hu]; norm_num
  have oTB : ∀ u ∈ Ioo a b, inner ℝ (deriv α u) (binormal α u) = 0 := fun u _ => by
    rw [binormal, tangent, inner_cross_left]
  have oNB : ∀ u ∈ Ioo a b, inner ℝ (normal α u) (binormal α u) = 0 := fun u _ => by
    rw [binormal, tangent, inner_cross_right]
  have hon := orthonormal3 _ _ _ (oTT s hs) (oNN s hs) (oBB s hs) (oTN s hs) (oTB s hs) (oNB s hs)
  have d1 := deriv_zero_of_const ((hN s hs).inner ℝ (hN s hs)) hs oNN
  have d2 := deriv_zero_of_const ((hT s hs).inner ℝ (hN s hs)) hs oTN
  have d3 := deriv_zero_of_const ((hN s hs).inner ℝ hB) hs oNB
  have d4 := deriv_zero_of_const ((hT s hs).inner ℝ hB) hs oTB
  have d5 := deriv_zero_of_const (hB.inner ℝ hB) hs oBB
  have htor : inner ℝ (deriv (binormal α) s) (normal α s) = τ s := (hkt s hs).2
  rw [real_inner_comm (normal α s) (deriv (normal α) s)] at d1
  rw [real_inner_smul_left, oNN s hs] at d2
  rw [real_inner_comm (deriv (binormal α) s) (normal α s), htor] at d3
  rw [real_inner_smul_left, oNB s hs] at d4
  rw [real_inner_comm (binormal α s) (deriv (binormal α) s)] at d5
  have eN := expand3 _ _ _ hon (deriv (normal α) s)
  have eB := expand3 _ _ _ hon (deriv (binormal α) s)
  refine ⟨(hα1.differentiableAt (Ioo_mem_nhds hs.1 hs.2)).hasDerivAt, hT s hs, ?_, ?_, oTT s hs,
    oNN s hs, oBB s hs, oTN s hs, oTB s hs, oNB s hs⟩
  · have h1 : inner ℝ (deriv α s) (deriv (normal α) s) = -k s := by linarith
    have h2 : inner ℝ (normal α s) (deriv (normal α) s) = 0 := by linarith
    have h3 : inner ℝ (binormal α s) (deriv (normal α) s) = -τ s := by
      rw [real_inner_comm]; linarith
    rw [h1, h2, h3] at eN
    convert hN s hs using 1
    rw [eN]; simp only [neg_smul, zero_smul, add_zero]; abel
  · have h1 : inner ℝ (deriv α s) (deriv (binormal α) s) = 0 := by linarith
    have h2 : inner ℝ (normal α s) (deriv (binormal α) s) = τ s := by
      rw [real_inner_comm]; exact htor
    have h3 : inner ℝ (binormal α s) (deriv (binormal α) s) = 0 := by linarith
    rw [h1, h2, h3] at eB
    convert hB using 1
    rw [eB]; simp only [zero_smul, zero_add, add_zero]

theorem inner_le_one_eq (u v : E3) (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1) :
    inner ℝ u v ≤ 1 ∧ (inner ℝ u v = 1 → u = v) := by
  have h := real_inner_self_nonneg (x := u - v)
  have e : inner ℝ (u - v) (u - v) = 2 - 2 * inner ℝ u v := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hu, hv, real_inner_comm u v]; ring
  refine ⟨by linarith, fun h1 => ?_⟩
  rw [h1] at e
  have e2 : inner ℝ (u - v) (u - v) = 0 := by linarith
  exact sub_eq_zero.1 (inner_self_eq_zero.1 e2)

theorem uniqueness (a b : ℝ) (k τ : ℝ → ℝ) (hk : ContDiffOn ℝ (⊤ : ℕ∞) k (Ioo a b))
    (hkpos : ∀ s ∈ Ioo a b, 0 < k s) (α β : ℝ → E3) (hα : IsArcLengthCurve (Ioo a b) α)
    (hβ : IsArcLengthCurve (Ioo a b) β)
    (hαk : ∀ s ∈ Ioo a b, curvature α s = k s ∧ torsion α s = τ s)
    (hβk : ∀ s ∈ Ioo a b, curvature β s = k s ∧ torsion β s = τ s) :
    ∃ M : E3 → E3, IsRigidMotion M ∧ ∀ s ∈ Ioo a b, β s = M (α s) := by
  rcases (Ioo a b).eq_empty_or_nonempty with he | ⟨s0, hs0⟩
  · exact ⟨id, ⟨LinearIsometryEquiv.refl ℝ E3, 0, by simp, fun x => by simp⟩, by simp [he]⟩
  have F1 := curve_frenet a b k τ hk hkpos α hα hαk
  have F2 := curve_frenet a b k τ hk hkpos β hβ hβk
  obtain ⟨-, -, -, -, a1, a2, a3, a4, a5, a6⟩ := F1 s0 hs0
  obtain ⟨-, -, -, -, b1, b2, b3, b4, b5, b6⟩ := F2 s0 hs0
  have ho1 := orthonormal3 _ _ _ a1 a2 a3 a4 a5 a6
  have ho2 := orthonormal3 _ _ _ b1 b2 b3 b4 b5 b6
  let ρ := (onb3 _ _ _ ho1).equiv (onb3 _ _ _ ho2) (Equiv.refl (Fin 3))
  have hρ : ∀ i, ρ (![deriv α s0, normal α s0, binormal α s0] i) =
      ![deriv β s0, normal β s0, binormal β s0] i := fun i => by
    have := (onb3 _ _ _ ho1).equiv_apply_basis (onb3 _ _ _ ho2) (Equiv.refl (Fin 3)) i
    rw [onb3_apply, onb3_apply] at this
    exact this
  have hρT : ρ (deriv α s0) = deriv β s0 := hρ 0
  have hρN : ρ (normal α s0) = normal β s0 := hρ 1
  have hρB : ρ (binormal α s0) = binormal β s0 := hρ 2
  have hdet : LinearMap.det (ρ.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 := by
    have h := Module.Basis.det_comp stdB (ρ.toLinearEquiv : E3 →ₗ[ℝ] E3)
      ![deriv α s0, normal α s0, binormal α s0]
    have hc : ((ρ.toLinearEquiv : E3 →ₗ[ℝ] E3) ∘ ![deriv α s0, normal α s0, binormal α s0]) =
        ![deriv β s0, normal β s0, binormal β s0] := funext hρ
    rw [hc, stdB_det, stdB_det] at h
    have e1 : inner ℝ (cross (![deriv α s0, normal α s0, binormal α s0] 0)
        (![deriv α s0, normal α s0, binormal α s0] 1))
        (![deriv α s0, normal α s0, binormal α s0] 2) = 1 := a3
    have e2 : inner ℝ (cross (![deriv β s0, normal β s0, binormal β s0] 0)
        (![deriv β s0, normal β s0, binormal β s0] 1))
        (![deriv β s0, normal β s0, binormal β s0] 2) = 1 := b3
    rw [e1, e2, mul_one] at h
    exact h.symm
  have hr : ∀ {f : ℝ → E3} {f' : E3} {s : ℝ}, HasDerivAt f f' s →
      HasDerivAt (fun u => ρ (f u)) (ρ f') s := fun h =>
    (ρ.toContinuousLinearEquiv.hasFDerivAt).comp_hasDerivAt _ h
  have hEg : ∀ s ∈ Ioo a b, HasDerivAt (fun u => inner ℝ (ρ (deriv α u)) (deriv β u) +
      inner ℝ (ρ (normal α u)) (normal β u) + inner ℝ (ρ (binormal α u)) (binormal β u)) 0 s := by
    intro s hs
    obtain ⟨-, t1, n1, c1, -⟩ := F1 s hs
    obtain ⟨-, t2, n2, c2, -⟩ := F2 s hs
    refine ((((hr t1).inner ℝ t2).add ((hr n1).inner ℝ n2)).add ((hr c1).inner ℝ c2)).congr_deriv ?_
    simp only [map_smul, map_sub, map_neg, inner_sub_left, inner_sub_right, inner_neg_left,
      inner_neg_right, real_inner_smul_left, real_inner_smul_right]
    ring
  have hTT : ∀ s ∈ Ioo a b, ρ (deriv α s) = deriv β s := by
    intro s hs
    obtain ⟨-, -, -, -, x1, x2, x3, -⟩ := F1 s hs
    obtain ⟨-, -, -, -, y1, y2, y3, -⟩ := F2 s hs
    have q1 := inner_le_one_eq (ρ (deriv α s)) (deriv β s)
      (by rw [LinearIsometryEquiv.inner_map_map]; exact x1) y1
    have q2 := inner_le_one_eq (ρ (normal α s)) (normal β s)
      (by rw [LinearIsometryEquiv.inner_map_map]; exact x2) y2
    have q3 := inner_le_one_eq (ρ (binormal α s)) (binormal β s)
      (by rw [LinearIsometryEquiv.inner_map_map]; exact x3) y3
    have hc := const_of_hasDerivAt_zero hEg hs hs0
    simp only [hρT, hρN, hρB] at hc
    rw [b1, b2, b3] at hc
    exact q1.2 (by linarith [q2.1, q3.1])
  have hD : ∀ s ∈ Ioo a b, HasDerivAt (fun u => β u - ρ (α u)) 0 s := by
    intro s hs
    have := (F2 s hs).1.sub (hr (F1 s hs).1)
    rw [hTT s hs, sub_self] at this
    exact this
  refine ⟨fun x => ρ x + (β s0 - ρ (α s0)), ⟨ρ, β s0 - ρ (α s0), by rw [hdet]; norm_num,
    fun x => rfl⟩, fun s hs => ?_⟩
  have := const_of_hasDerivAt_zero hD hs hs0
  simp only at this ⊢
  rw [← this]
  abel

/-- Uniqueness with the curvature of `α` itself as `k`: `‖α''‖` is smooth where it is nonzero. -/
theorem uniqueness_of_eq (a b : ℝ) (α β : ℝ → E3) (hα : IsArcLengthCurve (Ioo a b) α)
    (hβ : IsArcLengthCurve (Ioo a b) β) (hk : ∀ s ∈ Ioo a b, 0 < curvature α s)
    (hcurv : ∀ s ∈ Ioo a b, curvature β s = curvature α s)
    (htors : ∀ s ∈ Ioo a b, torsion β s = torsion α s) :
    ∃ M : E3 → E3, IsRigidMotion M ∧ ∀ s ∈ Ioo a b, β s = M (α s) := by
  have hks : ContDiffOn ℝ (⊤ : ℕ∞) (curvature α) (Ioo a b) := by
    obtain ⟨-, h2⟩ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).1 hα.1
    obtain ⟨-, h4⟩ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).1 h2
    refine h4.norm ℝ fun s hs h0 => ?_
    have := hk s hs
    rw [curvature, h0, norm_zero] at this
    exact lt_irrefl _ this
  exact uniqueness a b (curvature α) (torsion α) hks hk α β hα hβ (fun _ _ => ⟨rfl, rfl⟩)
    (fun s hs => ⟨hcurv s hs, htors s hs⟩)

end FrenetBuild

set_option maxHeartbeats 4000000 in
open DoCarmoDG in
theorem solution
    (a b : ℝ) (alpha beta : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hbeta : IsArcLengthCurve (Set.Ioo a b) beta)
    (hk : ∀ s ∈ Set.Ioo a b, 0 < curvature alpha s)
    (hcurv : ∀ s ∈ Set.Ioo a b, curvature beta s = curvature alpha s)
    (htors : ∀ s ∈ Set.Ioo a b, torsion beta s = torsion alpha s) :
    ∃ M : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsRigidMotion M ∧ ∀ s ∈ Set.Ioo a b, beta s = M (alpha s) := by
  exact FrenetBuild.uniqueness_of_eq a b alpha beta halpha hbeta hk hcurv htors
