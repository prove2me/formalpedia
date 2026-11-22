-- Prove2me | solution 1 for CubicSurface27.residual_two_lines
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T10:10:31.955934+00:00
-- url     : https://prove2.me/submissions/04930aab-52ff-4cbb-9db9-705d8d2d9886

import Mathlib
import Definitions.Def_cubic_surface_27_layer

open MvPolynomial

namespace RLAux

open CubicSurface27

/-! ### Degree-3 monomials are products of three variables -/

lemma exists_single_add {n : ℕ} (m : Fin 4 →₀ ℕ) (hm : m.degree = n + 1) :
    ∃ i m', m = m' + Finsupp.single i 1 ∧ m'.degree = n := by
  have hne : m ≠ 0 := by
    rintro rfl; simp at hm
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  have hle : Finsupp.single i 1 ≤ m := by
    rw [Finsupp.single_le_iff]; simp at hi; omega
  refine ⟨i, m - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm, ?_⟩
  have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
  rw [map_add, Finsupp.degree_single, hm] at h
  omega

lemma monomial_deg3 (m : Fin 4 →₀ ℕ) (hm : m.degree = 3) :
    ∃ a b c : Fin 4, monomial m (1 : ℂ) = X a * X b * X c := by
  obtain ⟨c, m1, rfl, h1⟩ := exists_single_add (n := 2) m hm
  obtain ⟨b, m2, rfl, h2⟩ := exists_single_add (n := 1) m1 h1
  obtain ⟨a, m3, rfl, h3⟩ := exists_single_add (n := 0) m2 h2
  rw [Finsupp.degree_eq_zero_iff] at h3
  subst h3
  refine ⟨a, b, c, ?_⟩
  simp [X, monomial_mul]

/-- Induction principle for homogeneous cubics. -/
lemma cubic_induction (P : MvPolynomial (Fin 4) ℂ → Prop)
    (h0 : P 0) (hadd : ∀ F G, P F → P G → P (F + G))
    (hsmul : ∀ (r : ℂ) F, P F → P (r • F))
    (hX : ∀ a b c : Fin 4, P (X a * X b * X c))
    (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) : P F := by
  rw [F.as_sum]
  refine Finset.sum_induction _ P hadd h0 ?_
  intro m hm
  have hdeg : m.degree = 3 := by
    have := hF (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  obtain ⟨a, b, c, habc⟩ := monomial_deg3 m hdeg
  have : monomial m (coeff m F) = coeff m F • monomial m (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, habc]
  exact hsmul _ _ (hX a b c)

/-! ### First-order Taylor expansion of a cubic along a direction -/

lemma taylor3 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x w : Fin 4 → ℂ) :
    ∃ q : ℂ, ∀ t : ℂ, eval (x + t • w) F =
      eval x F + t * (∑ i, w i * eval x (pderiv i F)) + t ^ 2 * q + t ^ 3 * eval w F := by
  refine cubic_induction (fun F => ∃ q : ℂ, ∀ t : ℂ, eval (x + t • w) F =
      eval x F + t * (∑ i, w i * eval x (pderiv i F)) + t ^ 2 * q + t ^ 3 * eval w F)
    ?_ ?_ ?_ ?_ F hF
  · exact ⟨0, fun t => by simp⟩
  · rintro F G ⟨q1, h1⟩ ⟨q2, h2⟩
    refine ⟨q1 + q2, fun t => ?_⟩
    simp only [map_add, h1 t, h2 t, mul_add, Finset.sum_add_distrib]
    ring
  · rintro r F ⟨q, h⟩
    refine ⟨r * q, fun t => ?_⟩
    simp only [smul_eval, Derivation.map_smul, h t]
    have : ∑ i, w i * (r * eval x (pderiv i F)) = r * ∑ i, w i * eval x (pderiv i F) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]; ring
  · intro a b c
    refine ⟨x a * w b * w c + w a * x b * w c + w a * w b * x c, fun t => ?_⟩
    simp [Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, add_mul,
      Finset.sum_add_distrib, apply_ite (eval x), mul_ite, Finset.sum_ite_eq]
    ring

/-! ### Directional derivative -/

/-- The derivative of `F` at `x` in direction `w`. -/
noncomputable def D (F : MvPolynomial (Fin 4) ℂ) (x w : Fin 4 → ℂ) : ℂ :=
  ∑ i, w i * eval x (pderiv i F)

lemma D_formula (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x w : Fin 4 → ℂ) :
    D F x w = (eval (x + w) F - eval (x - w) F) / 2 - eval w F := by
  obtain ⟨q, hq⟩ := taylor3 F hF x w
  have e1 := hq 1
  have e2 := hq (-1)
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at e1 e2
  unfold D
  linear_combination (e2 - e1) / 2

/-! ### A cubic form restricted to a 3-dimensional span -/

lemma expand3 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (p q r : Fin 4 → ℂ) :
    ∃ k : Fin 10 → ℂ, ∀ a b c : ℂ, eval (a • p + b • q + c • r) F =
      k 0 * a ^ 3 + k 1 * a ^ 2 * b + k 2 * a ^ 2 * c + k 3 * a * b ^ 2 + k 4 * a * b * c +
      k 5 * a * c ^ 2 + k 6 * b ^ 3 + k 7 * b ^ 2 * c + k 8 * b * c ^ 2 + k 9 * c ^ 3 := by
  refine cubic_induction (fun F => ∃ k : Fin 10 → ℂ, ∀ a b c : ℂ, eval (a • p + b • q + c • r) F =
      k 0 * a ^ 3 + k 1 * a ^ 2 * b + k 2 * a ^ 2 * c + k 3 * a * b ^ 2 + k 4 * a * b * c +
      k 5 * a * c ^ 2 + k 6 * b ^ 3 + k 7 * b ^ 2 * c + k 8 * b * c ^ 2 + k 9 * c ^ 3)
    ?_ ?_ ?_ ?_ F hF
  · exact ⟨0, fun a b c => by simp⟩
  · rintro F G ⟨k1, h1⟩ ⟨k2, h2⟩
    refine ⟨k1 + k2, fun a b c => ?_⟩
    simp only [map_add, h1, h2, Pi.add_apply]
    ring
  · rintro s F ⟨k, h⟩
    refine ⟨s • k, fun a b c => ?_⟩
    simp only [smul_eval, h, Pi.smul_apply, smul_eq_mul]
    ring
  · intro i j l
    refine ⟨![p i * p j * p l,
      q i * p j * p l + p i * q j * p l + p i * p j * q l,
      r i * p j * p l + p i * r j * p l + p i * p j * r l,
      p i * q j * q l + q i * p j * q l + q i * q j * p l,
      p i * q j * r l + p i * r j * q l + q i * p j * r l + q i * r j * p l + r i * p j * q l +
        r i * q j * p l,
      p i * r j * r l + r i * p j * r l + r i * r j * p l,
      q i * q j * q l,
      r i * q j * q l + q i * r j * q l + q i * q j * r l,
      q i * r j * r l + r i * q j * r l + r i * r j * q l,
      r i * r j * r l], fun a b c => ?_⟩
    simp
    ring

/-! ### Binary quadratics have nontrivial zeros over ℂ -/

lemma quad_root (A B C : ℂ) :
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ A * a ^ 2 + B * a * b + C * b ^ 2 = 0 := by
  by_cases hA : A = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hA]⟩
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (B ^ 2 - 4 * A * C)
    refine ⟨(-B + s) / (2 * A), 1, Or.inr one_ne_zero, ?_⟩
    field_simp
    linear_combination -hs

/-! ### Excluding a double line -/

/-- If `F` restricted to the plane spanned by `p, q, r` is `k·b·c²` (a double line `c = 0`
counted twice, possibly with `k = 0`), then `F` has a singular point on the line `c = 0`. -/
lemma no_double (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (P : Submodule ℂ (Fin 4 → ℂ)) (hP : Module.finrank ℂ P = 3)
    (p q r : Fin 4 → ℂ)
    (hspan : ∀ x ∈ P, ∃ a b c : ℂ, x = a • p + b • q + c • r)
    (hind : ∀ a b : ℂ, a • p + b • q = 0 → a = 0 ∧ b = 0)
    (k : ℂ) (hf : ∀ a b c : ℂ, eval (a • p + b • q + c • r) F = k * b * c ^ 2) : False := by
  obtain ⟨e, he⟩ : ∃ e, e ∉ P := by
    by_contra h
    push Not at h
    have hPt : P = ⊤ := eq_top_iff.mpr (fun x _ => h x)
    rw [hPt, finrank_top, Module.finrank_fin_fun] at hP
    omega
  obtain ⟨m, hm⟩ := expand3 F hF p q e
  obtain ⟨a, b, hab, hq0⟩ := quad_root (m 2) (m 4) (m 7)
  have hx0 : a • p + b • q ≠ 0 := by
    intro h
    obtain ⟨ha, hb⟩ := hind a b h
    rcases hab with h' | h'
    · exact h' ha
    · exact h' hb
  have hFx : eval (a • p + b • q) F = 0 := by simpa using hf a b 0
  have hDp : D F (a • p + b • q) p = 0 := by
    rw [D_formula F hF]
    have v1 : eval (a • p + b • q + p) F = 0 := by
      rw [show a • p + b • q + p = (a + 1) • p + b • q + (0:ℂ) • r by module, hf]; ring
    have v2 : eval (a • p + b • q - p) F = 0 := by
      rw [show a • p + b • q - p = (a - 1) • p + b • q + (0:ℂ) • r by module, hf]; ring
    have v3 : eval p F = 0 := by
      rw [show p = (1:ℂ) • p + (0:ℂ) • q + (0:ℂ) • r by module, hf]; ring
    rw [v1, v2, v3]; ring
  have hDq : D F (a • p + b • q) q = 0 := by
    rw [D_formula F hF]
    have v1 : eval (a • p + b • q + q) F = 0 := by
      rw [show a • p + b • q + q = a • p + (b + 1) • q + (0:ℂ) • r by module, hf]; ring
    have v2 : eval (a • p + b • q - q) F = 0 := by
      rw [show a • p + b • q - q = a • p + (b - 1) • q + (0:ℂ) • r by module, hf]; ring
    have v3 : eval q F = 0 := by
      rw [show q = (0:ℂ) • p + (1:ℂ) • q + (0:ℂ) • r by module, hf]; ring
    rw [v1, v2, v3]; ring
  have hDr : D F (a • p + b • q) r = 0 := by
    rw [D_formula F hF]
    have v1 : eval (a • p + b • q + r) F = k * b := by
      rw [show a • p + b • q + r = a • p + b • q + (1:ℂ) • r by module, hf]; ring
    have v2 : eval (a • p + b • q - r) F = k * b := by
      rw [show a • p + b • q - r = a • p + b • q + (-1:ℂ) • r by module, hf]; ring
    have v3 : eval r F = 0 := by
      rw [show r = (0:ℂ) • p + (0:ℂ) • q + (1:ℂ) • r by module, hf]; ring
    rw [v1, v2, v3]; ring
  have hDe : D F (a • p + b • q) e = 0 := by
    rw [D_formula F hF]
    have v1 : eval (a • p + b • q + e) F = eval (a • p + b • q + (1:ℂ) • e) F := by rw [one_smul]
    have v2 : eval (a • p + b • q - e) F = eval (a • p + b • q + (-1:ℂ) • e) F := by
      rw [neg_smul, one_smul, sub_eq_add_neg]
    have v3 : eval e F = eval ((0:ℂ) • p + (0:ℂ) • q + (1:ℂ) • e) F := by simp
    rw [v1, v2, v3, hm, hm, hm]
    linear_combination hq0
  let g : (Fin 4 → ℂ) →ₗ[ℂ] ℂ := ∑ i, (eval (a • p + b • q) (pderiv i F)) • LinearMap.proj i
  have hg : ∀ w, g w = D F (a • p + b • q) w := by
    intro w; simp [g, D, mul_comm]
  have hPk : P ≤ LinearMap.ker g := by
    intro y hy
    obtain ⟨a', b', c', rfl⟩ := hspan y hy
    rw [LinearMap.mem_ker, map_add, map_add, map_smul, map_smul, map_smul, hg, hg, hg, hDp, hDq, hDr]; simp
  have hek : e ∈ LinearMap.ker g := by rw [LinearMap.mem_ker, hg, hDe]
  have hlt : P < LinearMap.ker g := lt_of_le_of_ne hPk (fun h => he (by rw [h]; exact hek))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Submodule.finrank_le (LinearMap.ker g)
  rw [Module.finrank_fin_fun] at h2
  have htop : LinearMap.ker g = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
  obtain ⟨i, hi⟩ := hsm _ hx0 hFx
  have : Pi.single i 1 ∈ LinearMap.ker g := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, hg] at this
  apply hi
  simpa [D, Pi.single_apply] using this

end RLAux

open CubicSurface27 RLAux in
theorem solution (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (L : Submodule ℂ (Fin 4 → ℂ)) (hL : L ∈ linesOf F)
    (P : Submodule ℂ (Fin 4 → ℂ)) (hP : Module.finrank ℂ P = 3) (hLP : L ≤ P)
    (hM : ∃ M ∈ linesOf F, M ≤ P ∧ M ≠ L) :
    ∃ b ∈ linesOf F, ∃ c ∈ linesOf F, L ≠ b ∧ L ≠ c ∧ b ≠ c ∧ b ≤ P ∧ c ≤ P ∧
      ∀ x ∈ P, MvPolynomial.eval x F = 0 → x ∈ L ∨ x ∈ b ∨ x ∈ c := by
  obtain ⟨M, hMl, hMP, hML⟩ := hM
  -- a basis `e₁ ∈ L ∩ M`, `e₂ ∈ L`, `e₃ ∈ M` of `P`
  have hLM : L ⊓ M ≠ ⊥ := by
    intro h
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq L M
    rw [h, finrank_bot, hL.1, hMl.1] at h1
    have h2 := Submodule.finrank_mono (sup_le hLP hMP)
    rw [hP] at h2
    omega
  obtain ⟨e1, ⟨he1L, he1M⟩, he10⟩ := (Submodule.ne_bot_iff _).1 hLM
  obtain ⟨e2, he2L, he2⟩ : ∃ e2 ∈ L, e2 ∉ ℂ ∙ e1 := by
    by_contra h
    push Not at h
    have := Submodule.finrank_mono (show L ≤ ℂ ∙ e1 from h)
    rw [hL.1, finrank_span_singleton he10] at this
    omega
  obtain ⟨e3, he3M, he3⟩ : ∃ e3 ∈ M, e3 ∉ L := by
    by_contra h
    push Not at h
    exact hML (Submodule.eq_of_le_of_finrank_eq h (by rw [hMl.1, hL.1]))
  have hind12 : ∀ a b : ℂ, a • e1 + b • e2 = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    by_cases hb : b = 0
    · subst hb
      simp only [zero_smul, add_zero, smul_eq_zero] at h
      exact ⟨h.resolve_right he10, rfl⟩
    · exfalso
      apply he2
      rw [Submodule.mem_span_singleton]
      refine ⟨-(b⁻¹ * a), ?_⟩
      have hb2 : b • e2 = -(a • e1) := eq_neg_of_add_eq_zero_right h
      calc -(b⁻¹ * a) • e1 = b⁻¹ • (-(a • e1)) := by rw [smul_neg, smul_smul, neg_smul]
        _ = e2 := by rw [← hb2, smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hind : ∀ a b c : ℂ, a • e1 + b • e2 + c • e3 = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c h
    have hc : c = 0 := by
      by_contra hc
      apply he3
      have hc2 : c • e3 = -(a • e1 + b • e2) := eq_neg_of_add_eq_zero_right h
      have : e3 = c⁻¹ • (c • e3) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this, hc2]
      exact L.smul_mem _ (L.neg_mem (L.add_mem (L.smul_mem _ he1L) (L.smul_mem _ he2L)))
    subst hc
    simp only [zero_smul, add_zero] at h
    exact ⟨(hind12 a b h).1, (hind12 a b h).2, rfl⟩
  -- the coordinate map `ℂ³ → P`
  let T : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) :=
    (LinearMap.proj 0 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ).smulRight e1 +
      (LinearMap.proj 1 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ).smulRight e2 +
      (LinearMap.proj 2 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ).smulRight e3
  have hT : ∀ v, T v = v 0 • e1 + v 1 • e2 + v 2 • e3 := by intro v; simp [T]
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, hT] at hv
    obtain ⟨h0, h1, h2⟩ := hind _ _ _ hv
    funext i
    fin_cases i <;> simp [h0, h1, h2]
  have hTv : ∀ v a b c, T v = a • e1 + b • e2 + c • e3 → v 0 = a ∧ v 1 = b ∧ v 2 = c := by
    intro v a b c h
    rw [hT] at h
    have := hind (v 0 - a) (v 1 - b) (v 2 - c) (by linear_combination (norm := module) h)
    exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2.1, sub_eq_zero.1 this.2.2⟩
  have hrange : LinearMap.range T = P := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨v, rfl⟩
      rw [hT]
      exact P.add_mem (P.add_mem (P.smul_mem _ (hLP he1L)) (P.smul_mem _ (hLP he2L)))
        (P.smul_mem _ (hMP he3M))
    · rw [LinearMap.finrank_range_of_inj hTinj, hP, Module.finrank_fin_fun]
  have hspan : ∀ x ∈ P, ∃ a b c : ℂ, x = a • e1 + b • e2 + c • e3 := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨v, rfl⟩ := hx
    exact ⟨v 0, v 1, v 2, hT v⟩
  -- the restriction of `F` to `P`
  obtain ⟨k, hk⟩ := expand3 F hF e1 e2 e3
  have hA : ∀ a b : ℂ, k 0 * a ^ 3 + k 1 * a ^ 2 * b + k 3 * a * b ^ 2 + k 6 * b ^ 3 = 0 := by
    intro a b
    have h := hk a b 0
    rw [hL.2 _ (by simpa using L.add_mem (L.smul_mem a he1L) (L.smul_mem b he2L))] at h
    linear_combination -h
  have hB : ∀ a c : ℂ, k 0 * a ^ 3 + k 2 * a ^ 2 * c + k 5 * a * c ^ 2 + k 9 * c ^ 3 = 0 := by
    intro a c
    have h := hk a 0 c
    rw [hMl.2 _ (by simpa using M.add_mem (M.smul_mem a he1M) (M.smul_mem c he3M))] at h
    linear_combination -h
  have k0 : k 0 = 0 := by linear_combination hA 1 0
  have k6 : k 6 = 0 := by linear_combination hA 0 1
  have k9 : k 9 = 0 := by linear_combination hB 0 1
  have k1 : k 1 = 0 := by linear_combination (hA 1 1 - hA 1 (-1)) / 2 - k6
  have k3 : k 3 = 0 := by linear_combination (hA 1 1 + hA 1 (-1)) / 2 - k0
  have k2 : k 2 = 0 := by linear_combination (hB 1 1 - hB 1 (-1)) / 2 - k9
  have k5 : k 5 = 0 := by linear_combination (hB 1 1 + hB 1 (-1)) / 2 - k0
  have hmain : ∀ a b c : ℂ, eval (a • e1 + b • e2 + c • e3) F =
      b * c * (k 4 * a + k 7 * b + k 8 * c) := by
    intro a b c
    rw [hk, k0, k1, k2, k3, k5, k6, k9]
    ring
  -- smoothness excludes double lines
  have ndA : ¬ (k 4 = 0 ∧ k 7 = 0) := by
    rintro ⟨h4, h7⟩
    exact no_double F hF hsm P hP e1 e2 e3 hspan hind12 (k 8)
      (fun a b c => by rw [hmain, h4, h7]; ring)
  have ndB : ¬ (k 4 = 0 ∧ k 8 = 0) := by
    rintro ⟨h4, h8⟩
    refine no_double F hF hsm P hP e1 e3 e2 ?_ ?_ (k 7) ?_
    · intro x hx
      obtain ⟨a, b, c, rfl⟩ := hspan x hx
      exact ⟨a, c, b, add_right_comm _ _ _⟩
    · intro a b h
      have := hind a 0 b (by simpa using h)
      exact ⟨this.1, this.2.2⟩
    · intro a b c
      rw [add_right_comm, hmain, h4, h8]; ring
  -- the third line
  let φ : (Fin 3 → ℂ) →ₗ[ℂ] ℂ :=
    k 4 • LinearMap.proj 0 + k 7 • LinearMap.proj 1 + k 8 • LinearMap.proj 2
  have hφ : ∀ v, φ v = k 4 * v 0 + k 7 * v 1 + k 8 * v 2 := by intro v; simp [φ]
  have hφ0 : φ ≠ 0 := by
    intro h
    apply ndA
    constructor
    · simpa [hφ] using LinearMap.congr_fun h (Pi.single 0 1)
    · simpa [hφ] using LinearMap.congr_fun h (Pi.single 1 1)
  have hker : Module.finrank ℂ (LinearMap.ker φ) = 2 := by
    have hle : Module.finrank ℂ (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      rwa [Module.finrank_self] at this
    have hpos : 0 < Module.finrank ℂ (LinearMap.range φ) := by
      rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
      rwa [Ne, LinearMap.range_eq_bot]
    have := LinearMap.finrank_range_add_finrank_ker φ
    rw [Module.finrank_fin_fun] at this
    omega
  set N := (LinearMap.ker φ).map T with hN
  have hNl : N ∈ linesOf F := by
    refine ⟨?_, ?_⟩
    · rw [← hker]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective T hTinj _)).symm
    · rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hφ] at hv
      rw [hT, hmain, hv, mul_zero]
  have hNP : N ≤ P := hrange ▸ LinearMap.map_le_range
  have memN : ∀ a b c : ℂ, a • e1 + b • e2 + c • e3 ∈ N → k 4 * a + k 7 * b + k 8 * c = 0 := by
    rintro a b c ⟨v, hv, hTv'⟩
    obtain ⟨h0, h1, h2⟩ := hTv v a b c hTv'
    rw [SetLike.mem_coe, LinearMap.mem_ker, hφ, h0, h1, h2] at hv
    exact hv
  refine ⟨M, hMl, N, hNl, hML.symm, ?_, ?_, hMP, hNP, ?_⟩
  · intro h
    apply ndA
    have h1 := memN 1 0 0 (by simpa [← h] using he1L)
    have h2 := memN 0 1 0 (by simpa [← h] using he2L)
    constructor
    · linear_combination h1
    · linear_combination h2
  · intro h
    apply ndB
    have h1 := memN 1 0 0 (by simpa [← h] using he1M)
    have h3 := memN 0 0 1 (by simpa [← h] using he3M)
    constructor
    · linear_combination h1
    · linear_combination h3
  · intro x hx hFx
    obtain ⟨a, b, c, rfl⟩ := hspan x hx
    rw [hmain] at hFx
    rcases mul_eq_zero.1 hFx with h | h
    · rcases mul_eq_zero.1 h with h | h
      · subst h
        right; left
        simpa using M.add_mem (M.smul_mem a he1M) (M.smul_mem c he3M)
      · subst h
        left
        simpa using L.add_mem (L.smul_mem a he1L) (L.smul_mem b he2L)
    · right; right
      refine ⟨![a, b, c], ?_, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker, hφ]
        simpa using h
      · rw [hT]; simp
