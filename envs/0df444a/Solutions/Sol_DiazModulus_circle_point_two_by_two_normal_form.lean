-- Prove2me | solution 1 for DiazModulus.circle_point_two_by_two_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:46:53.472291+00:00
-- url     : https://prove2.me/submissions/e87b28d8-b2bf-46d3-b4ec-f9eedd140e59

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-!
# Normal form of a `2 × 2` configuration in `K + Ku + Kū`

Let `u` be transcendental over `K` with `ρ = u ū ∈ K`, so `ū = ρ / u`. Both `1, u` and `1, ū` are
`K`-independent. A key lemma: if `z i = ν (M i 0 + M i 1 t)` with `1, t` independent and `ν ≠ 0`,
then `z` is `K`-independent iff `det M ≠ 0` (via `Σ g i z i = ν ((g ᵥ* M) 0 + (g ᵥ* M) 1 t)` and
`Matrix.exists_vecMul_eq_zero_iff`). This gives the backward direction, where the products
expand into `K + Ku + Kū` using `u ū = ρ`.
Forward: `u (K + Ku + Kū) = K + Ku + Ku²`, so `u x i y j = A i j (u)` with `A i j ∈ K[X]` of degree
`≤ 2`. Transcendence turns the `2 × 2` minor into `A00 A11 = A01 A10` in `K[X]`. Extracting the
gcd `g` of `A00, A10` (`extract_gcd`) gives relatively prime `a0, a1`, and then `a0 ∣ A01`; so
`A i j = a i * b j` with `b0 = g`. If both `b j` were constants, `y` would be dependent, and
symmetrically for `a`; since `deg a i + deg b j ≤ 2` all degrees are `≤ 1`. With
`μ = x0 / a0(u)` we get `x i = μ a i(u)` and `y j = μ⁻¹ b j(u) / u = μ⁻¹ (b j₁ + (b j₀ / ρ) ū)`;
the determinants are non-zero by the key lemma.
-/

namespace R6_circleNF

open DiazModulus Polynomial Matrix

theorem smul_eq {K : Subfield ℂ} (c : K) (z : ℂ) : c • z = (c : ℂ) * z := rfl

theorem algebraMap_coe {K : Subfield ℂ} (c : K) : algebraMap K ℂ c = (c : ℂ) := rfl

theorem ne_zero_of_transcendental {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) : u ≠ 0 := by
  rintro rfl
  exact hT isAlgebraic_zero

/-- `1, u` are `K`-independent. -/
theorem indep_one (K : Subfield ℂ) (u : ℂ) (hT : Transcendental K u) (a b : K)
    (h : (a : ℂ) + (b : ℂ) * u = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply hT
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
    have : u = ((-a / b : K) : ℂ) := by
      push_cast
      field_simp
      linear_combination h
    rw [this]
    exact isAlgebraic_algebraMap (-a / b)
  subst hb
  refine ⟨?_, rfl⟩
  simpa using h

/-- `1, ū` are `K`-independent. -/
theorem indep_conj (K : Subfield ℂ) (u : ℂ) (hT : Transcendental K u) (hρ : u * conj u ∈ K)
    (a b : K) (h : (a : ℂ) + (b : ℂ) * conj u = 0) : a = 0 ∧ b = 0 := by
  have hu := ne_zero_of_transcendental hT
  obtain ⟨h1, h2⟩ := indep_one K u hT (b * ⟨u * conj u, hρ⟩) a (by
    push_cast
    linear_combination u * h)
  refine ⟨h2, ?_⟩
  have hρ0 : (⟨u * conj u, hρ⟩ : K) ≠ 0 := by
    intro h0
    have := congrArg Subtype.val h0
    simp only [ZeroMemClass.coe_zero] at this
    exact mul_ne_zero hu ((_root_.map_ne_zero _).mpr hu) this
  exact (mul_eq_zero.mp h1).resolve_right hρ0

/-- Independence of `z i = ν (M i 0 + M i 1 t)` is equivalent to `det M ≠ 0`. -/
theorem li_iff (K : Subfield ℂ) (t ν : ℂ)
    (ht : ∀ a b : K, (a : ℂ) + (b : ℂ) * t = 0 → a = 0 ∧ b = 0)
    (hν : ν ≠ 0) (M : Matrix (Fin 2) (Fin 2) K) (z : Fin 2 → ℂ)
    (hz : ∀ i, z i = ν * ((M i 0 : ℂ) + (M i 1 : ℂ) * t)) :
    LinearIndependent K z ↔ M.det ≠ 0 := by
  have key : ∀ g : Fin 2 → K,
      ∑ i, g i • z i = ν * (((g ᵥ* M) 0 : K) + ((g ᵥ* M) 1 : K) * t) := by
    intro g
    simp only [Fin.sum_univ_two, hz, Matrix.vecMul, dotProduct, smul_eq]
    push_cast
    ring
  have key2 : ∀ g : Fin 2 → K, ∑ i, g i • z i = 0 ↔ g ᵥ* M = 0 := by
    intro g
    rw [key, mul_eq_zero, or_iff_right hν]
    constructor
    · intro h
      obtain ⟨h0, h1⟩ := ht _ _ h
      funext k
      fin_cases k
      · exact h0
      · exact h1
    · intro h
      rw [h]
      simp
  rw [Fintype.linearIndependent_iff, Ne, ← Matrix.exists_vecMul_eq_zero_iff]
  constructor
  · rintro H ⟨v, hv, hvM⟩
    exact hv (funext (H v ((key2 v).2 hvM)))
  · intro H g hg i
    by_contra hgi
    exact H ⟨g, fun h => hgi (by simp [h]), (key2 g).1 hg⟩

/-- Two constant polynomials cannot both scale an independent pair. -/
theorem not_both_const (K : Subfield ℂ) (u : ℂ) (z : Fin 2 → ℂ) (hz : LinearIndependent K z)
    (s e : ℂ) (he : e ≠ 0) (p0 p1 : K[X]) (hp0 : p0 ≠ 0)
    (h0 : e * z 0 = s * aeval u p0) (h1 : e * z 1 = s * aeval u p1)
    (d0 : p0.natDegree = 0) (d1 : p1.natDegree = 0) : False := by
  rw [eq_C_of_natDegree_eq_zero d0] at h0 hp0
  rw [eq_C_of_natDegree_eq_zero d1] at h1
  simp only [aeval_C, algebraMap_coe] at h0 h1
  have hsum : ∑ i, (![p1.coeff 0, -p0.coeff 0] : Fin 2 → K) i • z i = 0 := by
    simp only [Fin.sum_univ_two, smul_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply mul_left_cancel₀ he
    push_cast
    linear_combination (p1.coeff 0 : ℂ) * h0 - (p0.coeff 0 : ℂ) * h1
  have := Fintype.linearIndependent_iff.1 hz _ hsum 1
  simp at this
  exact hp0 (by rw [this, C_0])

theorem eval_le_one (K : Subfield ℂ) (u : ℂ) (p : K[X]) (hp : p.natDegree ≤ 1) :
    aeval u p = (p.coeff 0 : ℂ) + (p.coeff 1 : ℂ) * u := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp]
  simp only [map_add, map_mul, aeval_C, aeval_X, algebraMap_coe]
  ring

end R6_circleNF

open DiazModulus R6_circleNF Polynomial in
theorem solution (K : Subfield ℂ) (u : ℂ)
    (hT : Transcendental K u) (hρ : u * conj u ∈ K) (x y : Fin 2 → ℂ) :
    (LinearIndependent K x ∧ LinearIndependent K y ∧ ∀ i j, x i * y j ∈ Submodule.span K ({1, u, conj u} : Set ℂ)) ↔
      ∃ (μ : ℂ) (P Q : Matrix (Fin 2) (Fin 2) K), μ ≠ 0 ∧ P.det ≠ 0 ∧ Q.det ≠ 0 ∧
        (∀ i, x i = μ * ((P i 0 : ℂ) + (P i 1 : ℂ) * u)) ∧
        (∀ j, y j = μ⁻¹ * ((Q 0 j : ℂ) + (Q 1 j : ℂ) * conj u)) := by
  have hu := ne_zero_of_transcendental hT
  have hcu : conj u ≠ 0 := (_root_.map_ne_zero _).mpr hu
  set ρK : K := ⟨u * conj u, hρ⟩ with hρKdef
  have hρK : (ρK : ℂ) = u * conj u := rfl
  have hI1 := indep_one K u hT
  have hIc := indep_conj K u hT hρ
  constructor
  · rintro ⟨hx, hy, hxy⟩
    -- the polynomials `A i j` with `A i j (u) = u x i y j`
    obtain ⟨A, hAdeg, hAev⟩ : ∃ A : Fin 2 → Fin 2 → K[X], (∀ i j, (A i j).natDegree ≤ 2) ∧
        ∀ i j, aeval u (A i j) = u * x i * y j := by
      have hcoef : ∀ i j, ∃ a b c : K, x i * y j = a + b * u + c * conj u := by
        intro i j
        obtain ⟨a, z, hz, he⟩ := Submodule.mem_span_insert.1 (hxy i j)
        obtain ⟨b, c, hbc⟩ := Submodule.mem_span_pair.1 hz
        refine ⟨a, b, c, ?_⟩
        rw [he, ← hbc, smul_eq, smul_eq, smul_eq, mul_one, add_assoc]
      choose a b c habc using hcoef
      refine ⟨fun i j => C (b i j) * X ^ 2 + C (a i j) * X + C (c i j * ρK),
        fun i j => natDegree_quadratic_le, fun i j => ?_⟩
      simp only [map_add, map_mul, aeval_C, aeval_X, map_pow, algebraMap_coe]
      rw [mul_assoc, habc]
      rw [hρK]
      ring
    have hinj := transcendental_iff_injective.1 hT
    have hxne : ∀ i, x i ≠ 0 := fun i => hx.ne_zero i
    have hyne : ∀ j, y j ≠ 0 := fun j => hy.ne_zero j
    have hprod : ∀ i j, u * x i * y j ≠ 0 := fun i j => mul_ne_zero (mul_ne_zero hu (hxne i)) (hyne j)
    have hAne : ∀ i j, A i j ≠ 0 := by
      intro i j h
      have := hAev i j
      rw [h, map_zero] at this
      exact hprod i j this.symm
    have hminor : A 0 0 * A 1 1 = A 0 1 * A 1 0 := by
      apply hinj
      simp only [map_mul, hAev]
      ring
    -- factorisation `A i j = a i * b j`
    obtain ⟨a0, a1, h00, h10, hunit⟩ := extract_gcd (A 0 0) (A 1 0)
    generalize gcd (A 0 0) (A 1 0) = g at h00 h10 hunit
    have hrel : IsRelPrime a0 a1 := gcd_isUnit_iff_isRelPrime.1 hunit
    have hg : g ≠ 0 := by intro h; apply hAne 0 0; rw [h00, h, zero_mul]
    have ha0 : a0 ≠ 0 := by intro h; apply hAne 0 0; rw [h00, h, mul_zero]
    have ha1 : a1 ≠ 0 := by intro h; apply hAne 1 0; rw [h10, h, mul_zero]
    have hdiv : a0 * A 1 1 = a1 * A 0 1 := by
      apply mul_left_cancel₀ hg
      calc g * (a0 * A 1 1) = A 0 0 * A 1 1 := by rw [h00]; ring
      _ = A 0 1 * A 1 0 := hminor
      _ = g * (a1 * A 0 1) := by rw [h10]; ring
    obtain ⟨b1, hb1⟩ := hrel.dvd_of_dvd_mul_left ⟨A 1 1, hdiv.symm⟩
    have h11 : A 1 1 = a1 * b1 := by
      apply mul_left_cancel₀ ha0
      rw [hdiv, hb1]
      ring
    have hb1ne : b1 ≠ 0 := by intro h; apply hAne 0 1; rw [hb1, h, mul_zero]
    -- the four evaluations
    have E00 : u * x 0 * y 0 = aeval u a0 * aeval u g := by rw [← hAev, h00, map_mul, mul_comm]
    have E10 : u * x 1 * y 0 = aeval u a1 * aeval u g := by rw [← hAev, h10, map_mul, mul_comm]
    have E01 : u * x 0 * y 1 = aeval u a0 * aeval u b1 := by rw [← hAev, hb1, map_mul]
    have E11 : u * x 1 * y 1 = aeval u a1 * aeval u b1 := by rw [← hAev, h11, map_mul]
    -- degrees
    have d00 : a0.natDegree + g.natDegree ≤ 2 := by
      rw [← natDegree_mul ha0 hg, mul_comm, ← h00]; exact hAdeg 0 0
    have d10 : a1.natDegree + g.natDegree ≤ 2 := by
      rw [← natDegree_mul ha1 hg, mul_comm, ← h10]; exact hAdeg 1 0
    have d01 : a0.natDegree + b1.natDegree ≤ 2 := by
      rw [← natDegree_mul ha0 hb1ne, ← hb1]; exact hAdeg 0 1
    have d11 : a1.natDegree + b1.natDegree ≤ 2 := by
      rw [← natDegree_mul ha1 hb1ne, ← h11]; exact hAdeg 1 1
    have hb_nc : ¬ (g.natDegree = 0 ∧ b1.natDegree = 0) := fun ⟨e0, e1⟩ =>
      not_both_const K u y hy (aeval u a0) (u * x 0) (mul_ne_zero hu (hxne 0)) g b1 hg
        E00 E01 e0 e1
    have ha_nc : ¬ (a0.natDegree = 0 ∧ a1.natDegree = 0) := fun ⟨e0, e1⟩ =>
      not_both_const K u x hx (aeval u g) (u * y 0) (mul_ne_zero hu (hyne 0)) a0 a1 ha0
        (by linear_combination E00) (by linear_combination E10) e0 e1
    have da0 : a0.natDegree ≤ 1 := by
      by_contra h; exact hb_nc ⟨by omega, by omega⟩
    have da1 : a1.natDegree ≤ 1 := by
      by_contra h; exact hb_nc ⟨by omega, by omega⟩
    have dg : g.natDegree ≤ 1 := by
      by_contra h; exact ha_nc ⟨by omega, by omega⟩
    have db1 : b1.natDegree ≤ 1 := by
      by_contra h; exact ha_nc ⟨by omega, by omega⟩
    -- the normal form
    have he0 : aeval u a0 ≠ 0 := left_ne_zero_of_mul (E00 ▸ hprod 0 0)
    have hf0 : aeval u g ≠ 0 := right_ne_zero_of_mul (E00 ▸ hprod 0 0)
    set μ := x 0 / aeval u a0 with hμ
    have hμ0 : μ ≠ 0 := div_ne_zero (hxne 0) he0
    let P : Matrix (Fin 2) (Fin 2) K := !![a0.coeff 0, a0.coeff 1; a1.coeff 0, a1.coeff 1]
    let Q : Matrix (Fin 2) (Fin 2) K :=
      !![g.coeff 1, b1.coeff 1; g.coeff 0 / ρK, b1.coeff 0 / ρK]
    have hxP : ∀ i, x i = μ * ((P i 0 : ℂ) + (P i 1 : ℂ) * u) := by
      rw [Fin.forall_fin_two]
      simp only [P, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [← eval_le_one K u a0 da0, ← eval_le_one K u a1 da1, hμ]
      constructor
      · field_simp
      · rw [div_mul_eq_mul_div, eq_div_iff he0]
        apply mul_right_cancel₀ hf0
        linear_combination (-x 1) * E00 + x 0 * E10
    have hyform : ∀ (p : K[X]), p.natDegree ≤ 1 → ∀ (yj : ℂ),
        u * x 0 * yj = aeval u a0 * aeval u p →
        yj = μ⁻¹ * (((p.coeff 1 : K) : ℂ) + ((p.coeff 0 / ρK : K) : ℂ) * conj u) := by
      intro p hp yj hyj
      rw [eval_le_one K u p hp] at hyj
      have hux : u * x 0 ≠ 0 := mul_ne_zero hu (hxne 0)
      have h1 : yj = aeval u a0 * ((p.coeff 0 : ℂ) + (p.coeff 1 : ℂ) * u) / (u * x 0) := by
        rw [eq_div_iff hux]
        linear_combination hyj
      rw [h1, hμ, inv_div]
      push_cast
      rw [hρK]
      field_simp
      ring
    have hyQ : ∀ j, y j = μ⁻¹ * ((Q 0 j : ℂ) + (Q 1 j : ℂ) * conj u) := by
      rw [Fin.forall_fin_two]
      simp only [Q, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      exact ⟨hyform g dg (y 0) E00, hyform b1 db1 (y 1) E01⟩
    refine ⟨μ, P, Q, hμ0, (li_iff K u μ hI1 hμ0 P x hxP).1 hx, ?_, hxP, hyQ⟩
    rw [← Matrix.det_transpose]
    exact (li_iff K (conj u) μ⁻¹ hIc (inv_ne_zero hμ0) Q.transpose y hyQ).1 hy
  · rintro ⟨μ, P, Q, hμ, hP, hQ, hxP, hyQ⟩
    refine ⟨(li_iff K u μ hI1 hμ P x hxP).2 hP,
      (li_iff K (conj u) μ⁻¹ hIc (inv_ne_zero hμ) Q.transpose y hyQ).2
        (by rwa [Matrix.det_transpose]), fun i j => ?_⟩
    have hμμ : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    have : x i * y j = (P i 0 * Q 0 j + P i 1 * Q 1 j * ρK) • (1 : ℂ) + (P i 1 * Q 0 j) • u +
        (P i 0 * Q 1 j) • conj u := by
      rw [hxP, hyQ]
      simp only [smul_eq]
      push_cast
      rw [hρK]
      linear_combination ((P i 0 + P i 1 * u : ℂ) * (Q 0 j + Q 1 j * conj u)) * hμμ
    rw [this]
    refine add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      (Submodule.smul_mem _ _ (Submodule.subset_span ?_)))
      (Submodule.smul_mem _ _ (Submodule.subset_span ?_)) <;> simp
