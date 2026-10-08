-- Prove2me | solution 1 for FirstOrderOpt.FiniteSum.variance_reduced_estimator_bound_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:01:30.163394+00:00
-- url     : https://prove2.me/submissions/8fa35016-51cc-425e-8634-da62dce99040

import Mathlib

set_option autoImplicit false

namespace VRCexF4928

/-- The plane with the sup norm (Mathlib's default norm on `Fin 2 → ℝ`). -/
abbrev E2 := Fin 2 → ℝ

noncomputable def φ0 : E2 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
noncomputable def φ1 : E2 →L[ℝ] ℝ := ContinuousLinearMap.proj 1
noncomputable def φ2 : E2 →L[ℝ] ℝ := (1 / 2 : ℝ) • (φ0 - φ1)

noncomputable def a : Fin 3 → E2 →L[ℝ] ℝ := ![φ0, φ1, φ2]

lemma a0 (v : E2) : a 0 v = v 0 := rfl
lemma a1 (v : E2) : a 1 v = v 1 := rfl
lemma a2 (v : E2) : a 2 v = (v 0 - v 1) / 2 := by
  show φ2 v = _
  simp [φ2, φ0, φ1]; ring

lemma coord_le (v : E2) (j : Fin 2) : |v j| ≤ ‖v‖ := by
  have := norm_le_pi_norm v j
  rwa [Real.norm_eq_abs] at this

lemma a_le (i : Fin 3) (v : E2) : |a i v| ≤ ‖v‖ := by
  have h0 := coord_le v 0
  have h1 := coord_le v 1
  fin_cases i
  · simpa [a0] using h0
  · simpa [a1] using h1
  · show |a 2 v| ≤ ‖v‖
    rw [a2, abs_le]
    constructor <;> cases abs_le.mp h0 <;> cases abs_le.mp h1 <;> linarith

lemma a_norm (i : Fin 3) : ‖a i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
    rw [one_mul, Real.norm_eq_abs]; exact a_le i v)

noncomputable def fi (i : Fin 3) (x : E2) : ℝ := (a i x) ^ 2 / 2

noncomputable def gradf (i : Fin 3) (x : E2) : E2 →L[ℝ] ℝ := (a i x) • a i

lemma hgrad (i : Fin 3) (x : E2) : HasFDerivAt (fi i) (gradf i x) x := by
  have h := ((a i).hasFDerivAt (x := x)).mul ((a i).hasFDerivAt (x := x))
  have h2 := h.const_mul (1 / 2 : ℝ)
  have e1 : fi i = fun y => 1 / 2 * (⇑(a i) * ⇑(a i)) y := by
    funext y; simp only [fi, Pi.mul_apply]; ring
  rw [e1]
  refine h2.congr_fderiv ?_
  ext v; simp [gradf]; ring

lemma hconv (i : Fin 3) : ConvexOn ℝ Set.univ (fi i) := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  simp only [fi, smul_eq_mul, map_add, map_smul]
  have : t = 1 - s := by linarith
  subst this
  nlinarith [mul_nonneg hs ht, sq_nonneg (a i x - a i y)]

lemma hsmooth (i : Fin 3) (x y : E2) : ‖gradf i x - gradf i y‖ ≤ 1 * ‖x - y‖ := by
  have : gradf i x - gradf i y = (a i (x - y)) • a i := by
    ext v
    simp only [gradf, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      map_sub]
    ring
  rw [this, norm_smul, Real.norm_eq_abs]
  have := a_le i (x - y)
  have := a_norm i
  have := norm_nonneg (a i)
  nlinarith [abs_nonneg (a i (x - y))]

lemma vec_le (v : E2) (hv : ∀ j, |v j| ≤ 1) : ‖v‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j; rw [Real.norm_eq_abs]; exact hv j

lemma lower (φ : E2 →L[ℝ] ℝ) (v : E2) (hv : ∀ j, |v j| ≤ 1) : |φ v| ≤ ‖φ‖ := by
  have h := φ.le_opNorm v
  rw [Real.norm_eq_abs] at h
  have := vec_le v hv
  have := norm_nonneg φ
  nlinarith

end VRCexF4928

open VRCexF4928 in
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x) (hhconv : ConvexOn ℝ X h)
    (fi : Fin m → E → ℝ) (hf : ∀ x, f x = (1 / (m : ℝ)) * ∑ i, fi i x)
    (hfi_conv : ∀ i, ConvexOn ℝ Set.univ (fi i))
    (gradf : Fin m → E → E →L[ℝ] ℝ)
    (hgrad : ∀ i x, HasFDerivAt (fi i) (gradf i x) x)
    (gradf_full : E → E →L[ℝ] ℝ)
    (hgradf_avg : ∀ x, gradf_full x = (1 / (m : ℝ)) • ∑ i, gradf i x)
    (L : Fin m → ℝ) (hL : ∀ i, 0 < L i)
    (hsmooth : ∀ i x y, ‖gradf i x - gradf i y‖ ≤ L i * ‖x - y‖)
    (q : Fin m → ℝ) (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1)
    (LQ : ℝ) (hLQ : LQ = (1 / (m : ℝ)) * Finset.univ.sup' hne (fun i => L i / q i))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y)
    (xt xtilde : E) (hxt : xt ∈ X) (hxtilde : xtilde ∈ X)
    (G : Fin m → E →L[ℝ] ℝ)
    (hG : ∀ i, G i = (1 / (q i * (m : ℝ))) • (gradf i xt - gradf i xtilde) + gradf_full xtilde)
    (δ : Fin m → E →L[ℝ] ℝ) (hδ : ∀ i, δ i = G i - gradf_full xt),
    (∑ i, q i • δ i = 0) ∧
    (∑ i, q i * ‖δ i‖ ^ 2 ≤ 2 * LQ * (f xtilde - f xt - (gradf_full xt) (xtilde - xt))) ∧
    (∑ i, q i * ‖δ i‖ ^ 2 ≤ 4 * LQ * (Ψ xt - Ψ xstar + Ψ xtilde - Ψ xstar))) := by
  intro H
  let F : E2 → ℝ := fun x => (1 / ((3 : ℕ) : ℝ)) * ∑ i, fi i x
  let GF : E2 → E2 →L[ℝ] ℝ := fun x => (1 / ((3 : ℕ) : ℝ)) • ∑ i, gradf i x
  let xt : E2 := ![1, 1]
  let q : Fin 3 → ℝ := fun _ => 1 / 3
  let G : Fin 3 → E2 →L[ℝ] ℝ := fun i =>
    (1 / (q i * ((3 : ℕ) : ℝ))) • (gradf i xt - gradf i 0) + GF 0
  have hFnn : ∀ y, 0 ≤ F y := fun y => by
    simp only [F, fi]
    have : 0 ≤ ∑ i, (a i y) ^ 2 / 2 := Finset.sum_nonneg (fun i _ => by positivity)
    positivity
  have hF0 : F 0 = 0 := by simp [F, fi]
  have key := (H (E := E2) (m := 3) Finset.univ_nonempty Set.univ convex_univ isClosed_univ
    F 0 F (fun x => by simp) (convexOn_const 0 convex_univ) fi (fun x => rfl) hconv gradf hgrad
    GF (fun x => rfl) (fun _ => 1) (fun _ => one_pos) hsmooth q (fun _ => by norm_num [q])
    (by simp [q]) _ rfl 0 (Set.mem_univ _)
    (fun y _ => by rw [hF0]; exact hFnn y) xt 0 (Set.mem_univ _) (Set.mem_univ _)
    G (fun i => rfl) (fun i => G i - GF xt) (fun i => rfl)).2.1
  -- the evaluation of each error functional
  have hδ : ∀ i v, (G i - GF xt) v = a i xt * a i v - (1 / 3) * ∑ j, a j xt * a j v := by
    intro i v
    simp [G, GF, gradf, q]
  have hxt0 : a 0 xt = 1 := by simp [a0, xt]
  have hxt1 : a 1 xt = 1 := by simp [a1, xt]
  have hxt2 : a 2 xt = 0 := by simp [a2, xt]
  have b0 : 1 ≤ ‖G 0 - GF xt‖ := by
    have := lower (G 0 - GF xt) ![1, -1] (fun j => by fin_cases j <;> simp)
    rw [hδ, Fin.sum_univ_three, hxt0, hxt1, hxt2, a0, a1, a2] at this
    norm_num at this; linarith
  have b1 : 1 ≤ ‖G 1 - GF xt‖ := by
    have := lower (G 1 - GF xt) ![-1, 1] (fun j => by fin_cases j <;> simp)
    rw [hδ, Fin.sum_univ_three, hxt0, hxt1, hxt2, a0, a1, a2] at this
    norm_num at this; linarith
  have b2 : 2 / 3 ≤ ‖G 2 - GF xt‖ := by
    have := lower (G 2 - GF xt) ![-1, -1] (fun j => by fin_cases j <;> simp)
    rw [hδ, Fin.sum_univ_three, hxt0, hxt1, hxt2, a0, a1, a2] at this
    norm_num at this; linarith
  have hLQ : (1 / ((3 : ℕ) : ℝ)) * Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin 3 => (fun _ => (1 : ℝ)) i / q i) = 1 := by
    simp [q, Finset.sup'_const]
  rw [hLQ, Fin.sum_univ_three] at key
  have hFxt : F xt = 1 / 3 := by
    simp [F, fi, Fin.sum_univ_three, hxt0, hxt1, hxt2]; norm_num
  have hGxt : GF xt (0 - xt) = -(2 / 3) := by
    simp [GF, gradf, Fin.sum_univ_three, hxt0, hxt1, hxt2]
    norm_num
  rw [hFxt, hF0, hGxt] at key
  simp only [q] at key
  nlinarith [b0, b1, b2]
