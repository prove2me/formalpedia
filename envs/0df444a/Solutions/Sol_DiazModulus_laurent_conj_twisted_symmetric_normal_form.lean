-- Prove2me | solution 1 for DiazModulus.laurent_conj_twisted_symmetric_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:49:08.660537+00:00
-- url     : https://prove2.me/submissions/1479d159-c6c9-4033-9812-94d2754008e8

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A twisted-symmetric Laurent polynomial is G(v) + γ̄ · conj(v G(v)) modulo span(1, v̄)

Let `v ∉ Q̄`, `v v̄ = 1`, `g = F(v)/vᴺ` and `ḡ = γ v g` with `γ γ̄ = 1`. Write `w = v̄ = 1/v`.
* Split `F = A + Xᴺ B` (division by the monic `Xᴺ`), so `deg A < N`, and put `f₀ = B(0)`,
  `G = B − f₀`. Then `G(0) = 0` and `g = A(v)/vᴺ + f₀ + G(v)`.
* Conjugation of a polynomial value: `conj(P(v)) vᴷ = (reflect K Pᐤ)(v)` when `deg P ≤ K`, where
  `Pᐤ` has the conjugate coefficients (`Polynomial.eval₂_reflect_mul_pow` at `w`, `⅟w = v`).
  So `conj(A(v)/vᴺ) = A'(v)` with `A' = reflect N Aᐤ`, and `A'(0) = conj(A_N) = 0`.
* The relation `ḡ = γ v g`, times `v^(N+K)` with `K = deg G`, reads `P(v) v^(N+K) = Q(v)` with
  `P = A' − γ X G − γ f₀ X` and `Q` of degree at most `N + K`. As `v` is transcendental,
  `X^(N+K) P = Q`; since `P(0) = 0`, the left side has degree `> N + K` unless `P = 0`. So
  `conj(A(v)/vᴺ) = γ v G(v) + γ f₀ v`.
* Conjugating, `A(v)/vᴺ = γ̄ conj(v G(v)) + γ̄ f̄₀ v̄`, so
  `g − (G(v) + γ̄ conj(v G(v))) = f₀ · 1 + γ̄ f̄₀ · v̄`.
-/

namespace R18_C3

open DiazModulus Polynomial

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = cjQ a from rfl, Polynomial.aeval_algHom_apply, hp, map_zero]

/-- Conjugation on `Q̄`. -/
noncomputable def σQ : ↥Qbar →+* ↥Qbar :=
  ((starRingEnd ℂ).comp Qbar.subtype).codRestrict Qbar fun a => conj_mem_Qbar a.2

theorem σQ_coe (a : ↥Qbar) : (σQ a : ℂ) = conj (a : ℂ) := rfl

/-- Outside `Q̄`, evaluation is injective. -/
theorem aeval_injective {u : ℂ} (hu : u ∉ Qbar) : Function.Injective (aeval (R := ↥Qbar) u) := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff_injective.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h'))

theorem conj_aeval (z : ℂ) (P : (↥Qbar)[X]) : conj (aeval z P) = aeval (conj z) (P.map σQ) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  rfl

/-- `conj(P(v)) vᴷ = (reflect K Pᐤ)(v)` for `deg P ≤ K`. -/
theorem conj_poly {v : ℂ} (hwv : conj v * v = 1) (P : (↥Qbar)[X]) (K : ℕ)
    (hK : P.natDegree ≤ K) :
    conj (aeval v P) * v ^ K = aeval v (reflect K (P.map σQ)) := by
  let _ : Invertible (conj v) := ⟨v, by rw [mul_comm]; exact hwv, hwv⟩
  have h2 := eval₂_reflect_mul_pow (algebraMap (↥Qbar) ℂ) (conj v) K (P.map σQ)
    ((natDegree_map_le).trans hK)
  change aeval v (reflect K (P.map σQ)) * conj v ^ K = aeval (conj v) (P.map σQ) at h2
  rw [conj_aeval, ← h2, mul_assoc, ← mul_pow, hwv, one_pow, mul_one]

/-- `P(v) vᴹ = Q(v)` with `P(0) = 0` and `deg Q ≤ M` forces `P = 0`. -/
theorem key {v : ℂ} (hv : v ∉ Qbar) {P Q : (↥Qbar)[X]} {M : ℕ} (h0 : P.coeff 0 = 0)
    (hQ : Q.natDegree ≤ M) (h : aeval v P * v ^ M = aeval v Q) : P = 0 := by
  have e : X ^ M * P = Q := aeval_injective hv (by rw [map_mul, ← h]; simp [mul_comm])
  by_contra hP
  have hd := natDegree_X_pow_mul M hP
  rw [e] at hd
  have : P.natDegree = 0 := by omega
  exact hP (by rw [eq_C_of_natDegree_eq_zero this, h0, map_zero])

end R18_C3

open DiazModulus R18_C3 Polynomial in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (N : ℕ) (F : Polynomial ↥Qbar) (γ : ℂ) (hγ : γ ∈ Qbar) (hγ1 : γ * conj γ = 1)
    (hF : conj (Polynomial.aeval v F / v ^ N) = γ * v * (Polynomial.aeval v F / v ^ N)) :
    ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧
      Polynomial.aeval v F / v ^ N - (Polynomial.aeval v G + conj γ * conj (v * Polynomial.aeval v G)) ∈
        Submodule.span Qbar ({1, conj v} : Set ℂ) := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ Subfield.zero_mem _)
  have hwv : conj v * v = 1 := by rw [mul_comm]; exact hv1
  obtain ⟨Γ, rfl⟩ : ∃ Γ : ↥Qbar, (Γ : ℂ) = γ := ⟨⟨γ, hγ⟩, rfl⟩
  set A := F %ₘ X ^ N with hAdef
  set B := F /ₘ X ^ N with hBdef
  have hFAB : F = A + X ^ N * B := (modByMonic_add_div F (X ^ N)).symm
  have hAdeg : A.degree < N := by
    have := degree_modByMonic_lt F (monic_X_pow (R := ↥Qbar) N)
    rwa [degree_X_pow] at this
  have hAN : A.natDegree ≤ N := natDegree_le_of_degree_le hAdeg.le
  have hAc : A.coeff N = 0 := coeff_eq_zero_of_degree_lt hAdeg
  set f₀ := B.coeff 0
  set G := B - C f₀ with hGdef
  refine ⟨G, by simp [G, f₀], ?_⟩
  set K := G.natDegree
  have hA' := conj_poly hwv A N hAN
  have hRG := conj_poly hwv G K le_rfl
  set a := aeval v A
  set gg := aeval v G
  set a' := aeval v (reflect N (A.map σQ))
  set rg := aeval v (reflect K (G.map σQ))
  have hg : aeval v F / v ^ N = a / v ^ N + f₀ + gg := by
    have hB : aeval v B = f₀ + gg := by
      simp only [gg, G, map_sub, aeval_C]
      rw [show algebraMap (↥Qbar) ℂ f₀ = (f₀ : ℂ) from rfl]
      ring
    rw [hFAB, map_add, map_mul, hB, map_pow, aeval_X]
    field_simp
    ring
  have hcN : conj (a / v ^ N) = a' := by
    have hw0 : conj v ≠ 0 := fun h => by rw [h, zero_mul] at hwv; exact zero_ne_one hwv
    rw [← hA', map_div₀, map_pow, div_eq_iff (pow_ne_zero _ hw0), mul_assoc, ← mul_pow, hv1,
      one_pow, mul_one]
  -- the relation `ḡ = γ v g`, cleared of denominators
  have hP : reflect N (A.map σQ) - C Γ * X * G - C (Γ * f₀) * X = 0 := by
    refine key hv (M := N + K) (Q := C Γ * X ^ (K + 1) * A - C (σQ f₀) * X ^ (N + K) -
      reflect K (G.map σQ) * X ^ N) ?_ ?_ ?_
    · simp [coeff_reflect, coeff_map, hAc]
    · have h1 : (C Γ * X ^ (K + 1) * A).natDegree ≤ N + K := by
        rcases eq_or_ne A 0 with h | h
        · simp [h]
        · have hlt : A.natDegree < N := (natDegree_lt_iff_degree_lt h).2 hAdeg
          refine (natDegree_mul_le).trans ?_
          have := (natDegree_C_mul_le Γ (X ^ (K + 1) : (↥Qbar)[X])).trans
            (natDegree_X_pow_le (R := ↥Qbar) (K + 1))
          omega
      have h2 : (C (σQ f₀) * X ^ (N + K) : (↥Qbar)[X]).natDegree ≤ N + K :=
        (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)
      have h3 : (reflect K (G.map σQ) * X ^ N).natDegree ≤ N + K := by
        refine (natDegree_mul_le).trans ?_
        have := (natDegree_reflect_le (N := K) (p := G.map σQ)).trans
          (max_le le_rfl ((natDegree_map_le).trans le_rfl))
        have := natDegree_X_pow_le (R := ↥Qbar) N
        omega
      exact (natDegree_sub_le_of_le (natDegree_sub_le_of_le h1 h2) h3).trans (by simp)
    · rw [hg, map_add, map_add, hcN] at hF
      have hF2 : a' + conj (f₀ : ℂ) + conj gg = Γ * v * (a / v ^ N + f₀ + gg) := hF
      simp only [map_sub, map_mul, map_pow, aeval_C, aeval_X]
      change (a' - (Γ : ℂ) * v * gg - (Γ * f₀ : ↥Qbar) * v) * v ^ (N + K) =
        (Γ : ℂ) * v ^ (K + 1) * a - (σQ f₀ : ℂ) * v ^ (N + K) - rg * v ^ N
      rw [σQ_coe]
      have ha : a = a / v ^ N * v ^ N := by field_simp
      rw [ha]
      push_cast
      linear_combination v ^ (N + K) * hF2 - v ^ N * hRG
  have hPv := congrArg (aeval v) hP
  simp only [map_sub, map_mul, aeval_C, aeval_X, map_zero] at hPv
  change a' - (Γ : ℂ) * v * gg - (Γ * f₀ : ↥Qbar) * v = 0 at hPv
  have haN : a / v ^ N = conj ((Γ : ℂ) * v * gg + (Γ * f₀ : ↥Qbar) * v) := by
    rw [← sub_eq_zero.1 (by linear_combination hPv :
      a' - ((Γ : ℂ) * v * gg + (Γ * f₀ : ↥Qbar) * v) = 0), ← hcN, conj_conj]
  rw [hg, haN]
  refine Submodule.mem_span_pair.2 ⟨f₀, σQ Γ * σQ f₀, ?_⟩
  simp only [Subfield.smul_def, smul_eq_mul, map_add, map_mul, Subfield.coe_mul, σQ_coe]
  ring
