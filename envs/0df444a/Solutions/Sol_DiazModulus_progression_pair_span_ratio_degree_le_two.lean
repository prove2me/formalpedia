-- Prove2me | solution 1 for DiazModulus.progression_pair_span_ratio_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T07:31:34.747848+00:00
-- url     : https://prove2.me/submissions/75b1a78f-2223-498e-87b5-40f8fcc7000c

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_quadratic_over_ratio_of_mem_progression_pair_span

open Complex ComplexConjugate

/-! # A ratio `h = p(u)/q(u)` with `1, u, u⁻¹ ∈ c·⟨1, h, h², k, hk⟩` has degree at most 2

Write `K = Q̄`, `d = max(deg p, deg q)`; `p, q ≠ 0` (otherwise coprimality makes the other one a
unit and `d = 0`). Since `u` is transcendental, `X ↦ u` extends to a field embedding
`ι : K(X) → ℂ` (`RatFunc.liftAlgHom`), and `ι f = h` for `f = p/q ∈ K(X)`. From
`p · denom f = q · num f` and coprimality, `p ∣ num f` and `q ∣ denom f`, so Mathlib's degree
formula `[K(X) : K(f)] = max(deg num f, deg denom f)` (`RatFunc.finrank_eq_max_natDegree`) gives
`d ≤ [K(X) : K(f)]`. In particular `f` is not constant, hence transcendental over `K`, and so is
`h`; thus `h ∉ K`, and `quadratic_over_ratio_of_mem_progression_pair_span` gives `A, B, C ∈ K[X]`,
not all zero, with `A(h) u² + B(h) u + C(h) = 0`. By injectivity of `ι`,
`A(f) X² + B(f) X + C(f) = 0` in `K(X)`, so `X` is a root of the polynomial
`P = A(f) Y² + B(f) Y + C(f)` over `K(f)`, which is non-zero because `f` is transcendental.
Hence `[K(X) : K(f)] = [K(f)(X) : K(f)] = deg minpoly ≤ deg P ≤ 2`, and `d ≤ 2`.
-/

namespace R14_degree_ratio

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem aeval_injective {u : ℂ} (hu : u ∉ Qbar) :
    Function.Injective (aeval (R := ↥Qbar) u) :=
  (injective_iff_map_eq_zero _).2 fun P hP => transcendental_iff.1 (tr_of_not_mem hu) P hP

/-- The evaluation embedding `K(X) → ℂ`, `X ↦ u`. -/
noncomputable def ev {u : ℂ} (hu : u ∉ Qbar) : RatFunc (↥Qbar) →ₐ[↥Qbar] ℂ :=
  RatFunc.liftAlgHom (aeval u)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_injective hu))

theorem ev_alg {u : ℂ} (hu : u ∉ Qbar) (P : (↥Qbar)[X]) :
    ev hu (algebraMap _ _ P) = aeval u P := by
  simp [ev, RatFunc.liftAlgHom_apply]

/-- `d ≤ [K(X) : K(p/q)]` for coprime non-zero `p, q`. -/
theorem lower_bound {p q : (↥Qbar)[X]} (hcop : IsCoprime p q) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    max p.natDegree q.natDegree ≤ Module.finrank
      (IntermediateField.adjoin (↥Qbar)
        {(algebraMap _ (RatFunc (↥Qbar)) p / algebraMap _ _ q : RatFunc (↥Qbar))})
      (RatFunc (↥Qbar)) := by
  set f : RatFunc (↥Qbar) := algebraMap _ _ p / algebraMap _ _ q with hf
  have hcross : p * f.denom = q * f.num := by
    apply IsFractionRing.injective (↥Qbar)[X] (RatFunc (↥Qbar))
    have h2 : algebraMap _ (RatFunc (↥Qbar)) f.num / algebraMap _ _ f.denom =
        algebraMap _ (RatFunc (↥Qbar)) p / algebraMap _ _ q := RatFunc.num_div_denom f
    rw [div_eq_div_iff (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
      (RatFunc.algebraMap_ne_zero hq0)] at h2
    simp only [map_mul]
    linear_combination -h2
  have hnum0 : f.num ≠ 0 := by
    intro e; rw [e, mul_zero] at hcross; exact mul_ne_zero hp0 f.denom_ne_zero hcross
  have hdp : p ∣ f.num :=
    hcop.dvd_of_dvd_mul_left ⟨f.denom, by linear_combination -hcross⟩
  have hdq : q ∣ f.denom :=
    hcop.symm.dvd_of_dvd_mul_left ⟨f.num, by linear_combination hcross⟩
  rw [RatFunc.finrank_eq_max_natDegree]
  exact max_le_max (natDegree_le_of_dvd hdp hnum0) (natDegree_le_of_dvd hdq f.denom_ne_zero)

/-- `f = p/q` is not constant when `d ≥ 1`. -/
theorem nonconst {p q : (↥Qbar)[X]} (hcop : IsCoprime p q) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hdeg : 1 ≤ max p.natDegree q.natDegree) :
    ¬ ∃ k, (algebraMap _ (RatFunc (↥Qbar)) p / algebraMap _ _ q : RatFunc (↥Qbar)) =
      RatFunc.C k := by
  intro hk
  have hb := lower_bound hcop hp0 hq0
  rw [RatFunc.finrank_eq_max_natDegree] at hb
  rw [RatFunc.eq_C_iff] at hk
  omega

/-- `h = p(u)/q(u)` is transcendental over `K` when `d ≥ 1`. -/
theorem h_transcendental {u : ℂ} (hu : u ∉ Qbar) {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hdeg : 1 ≤ max p.natDegree q.natDegree) :
    Transcendental (↥Qbar) (aeval u p / aeval u q) := by
  set f : RatFunc (↥Qbar) := algebraMap _ _ p / algebraMap _ _ q with hf
  have hιf : ev hu f = aeval u p / aeval u q := by rw [hf, map_div₀, ev_alg, ev_alg]
  rintro ⟨A, hA0, hA⟩
  refine RatFunc.transcendental_of_ne_C f (nonconst hcop hp0 hq0 hdeg)
    ⟨A, hA0, (ev hu).toRingHom.injective ?_⟩
  change ev hu (aeval f A) = ev hu 0
  rw [← aeval_algHom_apply, hιf, hA, map_zero]

/-- A non-trivial quadratic relation for `u` over `K(ι f)` bounds `[K(X) : K(f)]` by `2`. -/
theorem finrank_le_two {u : ℂ} (hu : u ∉ Qbar) (f : RatFunc (↥Qbar))
    (hf : ¬ ∃ k, f = RatFunc.C k) {A B C : (↥Qbar)[X]} (hne : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0)
    (hrel : aeval (ev hu f) A * u ^ 2 + aeval (ev hu f) B * u + aeval (ev hu f) C = 0) :
    Module.finrank (IntermediateField.adjoin (↥Qbar) {f}) (RatFunc (↥Qbar)) ≤ 2 := by
  set F := IntermediateField.adjoin (↥Qbar) {f} with hF
  set g : F := IntermediateField.AdjoinSimple.gen (↥Qbar) f with hg
  have hcoe : ∀ R : (↥Qbar)[X], ((aeval g R : F) : RatFunc (↥Qbar)) = aeval f R :=
    fun R => (aeval_algHom_apply F.val g R).symm
  have htrf := transcendental_iff.1 (RatFunc.transcendental_of_ne_C f hf)
  have hevX : ev hu RatFunc.X = u := by rw [← RatFunc.algebraMap_X, ev_alg, aeval_X]
  have key : aeval f A * RatFunc.X ^ 2 + aeval f B * RatFunc.X + aeval f C = 0 := by
    apply (ev hu).toRingHom.injective
    change ev hu _ = ev hu 0
    rw [map_zero, map_add, map_add, map_mul, map_mul, map_pow, hevX, ← aeval_algHom_apply,
      ← aeval_algHom_apply, ← aeval_algHom_apply]
    exact hrel
  set P : F[X] := Polynomial.C (aeval g A) * X ^ 2 + Polynomial.C (aeval g B) * X +
    Polynomial.C (aeval g C) with hP
  have hP0 : P ≠ 0 := by
    intro hP0
    have e2 : aeval g A = 0 := by simpa [hP] using congrArg (coeff · 2) hP0
    have e1 : aeval g B = 0 := by simpa [hP] using congrArg (coeff · 1) hP0
    have e0 : aeval g C = 0 := by simpa [hP] using congrArg (coeff · 0) hP0
    have hA : A = 0 := htrf A (by rw [← hcoe, e2]; rfl)
    have hB : B = 0 := htrf B (by rw [← hcoe, e1]; rfl)
    have hC : C = 0 := htrf C (by rw [← hcoe, e0]; rfl)
    rcases hne with h | h | h
    exacts [h hA, h hB, h hC]
  have hPX : aeval (RatFunc.X : RatFunc (↥Qbar)) P = 0 := by
    simp only [hP, map_add, map_mul, map_pow, aeval_C, aeval_X,
      IntermediateField.algebraMap_apply, hcoe]
    exact key
  have hint : IsIntegral F (RatFunc.X : RatFunc (↥Qbar)) := (show IsAlgebraic F _ from
    ⟨P, hP0, hPX⟩).isIntegral
  rw [← (RatFunc.IntermediateField.adjoinXEquiv F).toLinearEquiv.finrank_eq,
    IntermediateField.adjoin.finrank hint]
  refine (natDegree_le_natDegree (minpoly.degree_le_of_ne_zero F _ hP0 hPX)).trans ?_
  rw [hP]
  compute_degree!

end R14_degree_ratio

open DiazModulus R14_degree_ratio Polynomial in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (p q : Polynomial ↥Qbar) (hcop : IsCoprime p q)
    (hdeg : 1 ≤ max p.natDegree q.natDegree) (c k : ℂ) (hc : c ≠ 0)
    (h1 : (1 : ℂ) ∈ Submodule.span Qbar ({c, c * (Polynomial.aeval u p / Polynomial.aeval u q), c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ 2, c * k, c * (Polynomial.aeval u p / Polynomial.aeval u q) * k} : Set ℂ)) (hu1 : u ∈ Submodule.span Qbar ({c, c * (Polynomial.aeval u p / Polynomial.aeval u q), c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ 2, c * k, c * (Polynomial.aeval u p / Polynomial.aeval u q) * k} : Set ℂ)) (hui : u⁻¹ ∈ Submodule.span Qbar ({c, c * (Polynomial.aeval u p / Polynomial.aeval u q), c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ 2, c * k, c * (Polynomial.aeval u p / Polynomial.aeval u q) * k} : Set ℂ)) :
    max p.natDegree q.natDegree ≤ 2 := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_left.1 hcop)
    simp [this] at hdeg
  have hq0 : q ≠ 0 := by
    rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
    simp [this] at hdeg
  have htr := h_transcendental hu hcop hp0 hq0 hdeg
  have hh : aeval u p / aeval u q ∉ Qbar := fun hm =>
    htr (isAlgebraic_algebraMap (⟨_, hm⟩ : ↥Qbar))
  obtain ⟨A, B, C, hne, hrel⟩ :=
    DiazModulus.quadratic_over_ratio_of_mem_progression_pair_span u hu c _ k hc hh h1 hu1 hui
  set f : RatFunc (↥Qbar) := algebraMap _ _ p / algebraMap _ _ q with hf
  have hιf : ev hu f = aeval u p / aeval u q := by rw [hf, map_div₀, ev_alg, ev_alg]
  rw [← hιf] at hrel
  exact (lower_bound hcop hp0 hq0).trans
    (finrank_le_two hu f (nonconst hcop hp0 hq0 hdeg) hne hrel)
