-- Prove2me | solution 1 for DiazModulus.quadratic_ratio_pole_fractions_independent
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:32:37.955287+00:00
-- url     : https://prove2.me/submissions/c00ebfac-0ef6-42d6-bef9-49124af20af2

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_quadratic_pencil_wronskian_span
import Theorems.Thm_DiazModulus_quadratic_ratio_wronskian_free

open Complex ComplexConjugate

/-! # The pole fractions `y₀(αᵢ + βᵢw)/(h − λᵢ)` are independent modulo `H₀`

Write `h = p(u)/q(u)`, `w = J(u)/q(u)` with `J = p′q − pq′`, and `gᵢ = q(αᵢq + βᵢJ)/(u(p − λᵢq))`
evaluated at `u`. Since `u` is transcendental and `p − λq ≠ 0` (coprimality and `max deg = 2`), all
denominators are non-zero. The `H₀`-part `a + bu + cu⁻¹` equals `R(u)/u` with
`R = c + aX + bX²`, and `quadratic_pencil_wronskian_span` writes `R = a′q + b′p + c′J`. Dividing
the relation by `y₀ = q(u)/u` and multiplying by `Π(h − λⱼ)` gives `A(h) + B(h)·w = 0` with
`A = (a′ + b′X)Π + Σ dᵢαᵢΠᵢ`, `B = c′Π + Σ dᵢβᵢΠᵢ`, where `Π = Π(X − λⱼ)` and `Πᵢ = Π_{j≠i}(X − λⱼ)`.
`quadratic_ratio_wronskian_free` gives `A = B = 0`. Evaluating at `X = λᵢ` (the `λⱼ` are distinct)
leaves `dᵢαᵢ = dᵢβᵢ = 0`, so `dᵢ = 0`. Then `a + bu + cu⁻¹ = 0`, and `a = b = c = 0` because
`c + aX + bX²` vanishes at the transcendental `u`. -/

namespace R20_pole

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem aeval_ne_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (hP : P ≠ 0) : aeval u P ≠ 0 :=
  fun h => hP (transcendental_iff.1 (tr_of_not_mem hu) P h)

theorem u_ne_zero {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)

/-- `1, u, u⁻¹` are free over `Q̄`. -/
theorem lin3 {u : ℂ} (hu : u ∉ Qbar) {a b c : ↥Qbar} (h : (a : ℂ) + b * u + c * u⁻¹ = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hu0 := u_ne_zero hu
  have hP := transcendental_iff.1 (tr_of_not_mem hu) (C c + C a * X + C b * X ^ 2) (by
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]
    field_simp at h
    linear_combination h)
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (coeff · 1) hP
  · simpa using congrArg (coeff · 2) hP
  · simpa using congrArg (coeff · 0) hP

theorem q_ne_zero {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) : q ≠ 0 := by
  rintro rfl
  have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
  simp at hdeg
  omega

theorem pencil_ne_zero {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (l : ↥Qbar) : p - C l * q ≠ 0 := by
  intro h
  have e : p = C l * q := sub_eq_zero.1 h
  rw [e] at hcop hdeg
  have h0 := natDegree_eq_zero_of_isUnit (isCoprime_self.1 (IsCoprime.mul_left_iff.1 hcop).2)
  have h1 := natDegree_C_mul_le l q
  omega

end R20_pole

open DiazModulus R20_pole in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (p q : (↥Qbar)[X])
    (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2)
    (l α β : Fin 3 → ↥Qbar) (hl : Function.Injective l) (hαβ : ∀ i, α i ≠ 0 ∨ β i ≠ 0)
    (a b c : ↥Qbar) (d : Fin 3 → ↥Qbar)
    (hrel : (a : ℂ) + (b : ℂ) * u + (c : ℂ) * u⁻¹ + ∑ i, (d i : ℂ) *
        (aeval u q * ((α i : ℂ) * aeval u q + (β i : ℂ) * aeval u (derivative p * q - p * derivative q)) /
          (u * (aeval u p - (l i : ℂ) * aeval u q))) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  set J := derivative p * q - p * derivative q with hJ
  have hu0 := u_ne_zero hu
  have hq0 : aeval u q ≠ 0 := aeval_ne_zero hu (q_ne_zero hcop hdeg)
  have he : ∀ i, aeval u p - (l i : ℂ) * aeval u q ≠ 0 := fun i => by
    simpa [am] using aeval_ne_zero hu (pencil_ne_zero hcop hdeg (l i))
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  obtain ⟨a', b', c', hR⟩ := DiazModulus.quadratic_pencil_wronskian_span p q hcop hdeg
    (C c + C a * X + C b * X ^ 2) (by compute_degree!)
  have hRu : (c : ℂ) + a * u + b * u ^ 2 =
      a' * aeval u q + b' * aeval u p + c' * aeval u J := by
    rw [← hJ] at hR
    simpa only [map_add, map_mul, map_pow, aeval_C, aeval_X, am] using congrArg (aeval u) hR
  rw [Fin.sum_univ_three] at hrel
  set L0 := X - C (l 0) with hL0
  set L1 := X - C (l 1) with hL1
  set L2 := X - C (l 2) with hL2
  set A := (C a' + C b' * X) * (L0 * L1 * L2) + C (d 0 * α 0) * (L1 * L2) +
    C (d 1 * α 1) * (L0 * L2) + C (d 2 * α 2) * (L0 * L1) with hA
  set B := C c' * (L0 * L1 * L2) + C (d 0 * β 0) * (L1 * L2) +
    C (d 1 * β 1) * (L0 * L2) + C (d 2 * β 2) * (L0 * L1) with hB
  have hAB := DiazModulus.quadratic_ratio_wronskian_free u hu p q hcop hdeg A B (by
    set e0 := aeval u p - (l 0 : ℂ) * aeval u q
    set e1 := aeval u p - (l 1 : ℂ) * aeval u q
    set e2 := aeval u p - (l 2 : ℂ) * aeval u q
    rw [← hJ]
    simp only [hA, hB, hL0, hL1, hL2, map_add, map_mul, map_sub, aeval_C, aeval_X, am,
]
    linear_combination (norm := skip) (e0 * e1 * e2 / aeval u q ^ 4) * u * hrel -
      (e0 * e1 * e2 / aeval u q ^ 4) * hRu
    field_simp
    ring)
  have n01 : l 0 ≠ l 1 := hl.ne (by decide)
  have n02 : l 0 ≠ l 2 := hl.ne (by decide)
  have n12 : l 1 ≠ l 2 := hl.ne (by decide)
  have kill : ∀ i, (d i = 0 ∨ α i = 0) → (d i = 0 ∨ β i = 0) → d i = 0 := fun i hα hβ => by
    rcases hαβ i with h | h
    · exact hα.resolve_right h
    · exact hβ.resolve_right h
  have ev : ∀ P : (↥Qbar)[X], P = 0 → ∀ x, eval x P = 0 := fun P hP x => by rw [hP, eval_zero]
  have hd : ∀ i, d i = 0 := by
    intro i
    have hA' := ev A hAB.1 (l i)
    have hB' := ev B hAB.2 (l i)
    fin_cases i <;>
    · simp [hA, hB, hL0, hL1, hL2, sub_eq_zero, n01, n02, n12, n01.symm, n02.symm, n12.symm]
        at hA' hB'
      exact kill _ hA' hB'
  have hd' : d = 0 := funext hd
  subst hd'
  simp only [Pi.zero_apply, Subfield.coe_zero, zero_mul, add_zero] at hrel
  obtain ⟨ha, hb, hc⟩ := lin3 hu hrel
  exact ⟨ha, hb, hc, rfl⟩
