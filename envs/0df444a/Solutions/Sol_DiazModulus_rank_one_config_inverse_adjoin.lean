-- Prove2me | solution 1 for DiazModulus.rank_one_config_inverse_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T14:02:26.321181+00:00
-- url     : https://prove2.me/submissions/9b5eac01-8463-4f65-bf16-369e27269554

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_rank_one_polynomial_matrix_factor

open Complex ComplexConjugate

/-! # Adjoining `u` and `u⁻¹`, with `u` transcendental over `F`

Write `x i * y j = c i j + l i j * u + m i j * u⁻¹` with `c i j ∈ V₀ ⊆ F` and `l i j, m i j ∈ K`
(`Submodule.mem_sup`, `Submodule.mem_span_pair`). It is enough to show that every `m i j` is `0`
(`inv_coeff`): the hypotheses do not change when `u` is replaced by `u⁻¹`, which is again
transcendental over `F` (`IsAlgebraic.inv_iff`), and that swap exchanges `l` and `m`. Then
`x i * y j = c i j ∈ V₀`.

For `inv_coeff`, put `P i j = l i j X² + c i j X + m i j ∈ F[X]`, so that `P i j (u) = u x i y j`.
All `P i j` are non-zero, and each `2 × 2` minor of `P` vanishes at `u`, hence is `0` because `u`
is transcendental over `F`. The rank-one factorisation node gives `P i j = a i * b j` in `F[X]`.
Evaluating at `u`, `x i` is a fixed non-zero multiple of `a i (u)`, and `y j` one of `b j (u)`, so
the `a i (u)` are `K`-independent, and so are the `b j (u)` (`linInd_scale`).

The degree count (`coeff_zero_eq_zero`) uses only that `deg a i + deg b j ≤ 2` and that the
coefficients of `X⁰` and `X²` of every `a i * b j` lie in `K`. Suppose
`a i₀(0) b j₀(0) = m i₀ j₀ ≠ 0`. If every `a i` is constant, then `a i = m i j₀ / b j₀(0)`, so the
two numbers `a i (u)` lie in a `K`-line, which is impossible (`card_le`). Otherwise some `a i₁`
has degree at least `1`, so every `b j` has degree at most `1`, and `b j(0) = m i₀ j / a i₀(0)`.
If some `b j₁` has degree `1`, then `a i₁` has degree exactly `1` and the `X²` coefficient gives
`b j(1) = l i₁ j / a i₁(1)`. In every case the three numbers `b j (u)` lie in the `K`-span of two
fixed numbers, which is again impossible. This is the factorisation-and-degree proof of the lemma
on adjoining a generic point of a circle; the case split above does not use that the factor `a`
is coprime.
-/

namespace R16_inv
open DiazModulus Polynomial

theorem am {F : Subfield ℂ} (r : F) : algebraMap F ℂ r = r := rfl

/-- A number of `K` times an element of `S` lies in the `K`-span of `S`. -/
theorem mul_mem_span {K : Subfield ℂ} {k z : ℂ} (hk : k ∈ K) {S : Set ℂ} (hz : z ∈ S) :
    k * z ∈ Submodule.span K S := by
  have := Submodule.smul_mem (Submodule.span K S) (⟨k, hk⟩ : K) (Submodule.subset_span hz)
  rwa [Subfield.smul_def, smul_eq_mul] at this

/-- Rescaling a `K`-independent family by a non-zero complex number keeps it independent. -/
theorem linInd_scale {K : Subfield ℂ} {ι : Type*} {f g : ι → ℂ} {t s : ℂ}
    (hf : LinearIndependent K f) (ht : t ≠ 0) (hs : s ≠ 0) (h : ∀ i, g i * s = f i * t) :
    LinearIndependent K g := by
  have e : g = (LinearMap.mulRight K (t / s)) ∘ f := by
    funext i
    simp only [Function.comp_apply, LinearMap.mulRight_apply]
    field_simp
    exact h i
  rw [e]
  exact hf.map' _ (LinearMap.ker_eq_bot.mpr (mul_left_injective₀ (div_ne_zero ht hs)))

/-- A `K`-independent family inside the span of a finite set is no larger than the set. -/
theorem card_le {K : Subfield ℂ} {ι : Type*} [Fintype ι] {g : ι → ℂ}
    (hg : LinearIndependent K g) (S : Finset ℂ) (hS : ∀ i, g i ∈ Submodule.span K (S : Set ℂ)) :
    Fintype.card ι ≤ S.card := by
  simpa using linearIndependent_le_span_aux' g hg (S : Set ℂ) (by rintro _ ⟨i, rfl⟩; exact hS i)

theorem coeff_two {F : Type*} [Field F] {p q : F[X]} (hp : p.natDegree ≤ 1)
    (hq : q.natDegree ≤ 1) : (p * q).coeff 2 = p.coeff 1 * q.coeff 1 := by
  have hp2 : p.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hq2 : q.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, hp2,
    hq2]

/-- The degree count: the constant coefficients of the products vanish. -/
theorem coeff_zero_eq_zero (K F : Subfield ℂ) (u : ℂ) (a : Fin 2 → F[X]) (b : Fin 3 → F[X])
    (ha : LinearIndependent K (fun i => aeval u (a i)))
    (hb : LinearIndependent K (fun j => aeval u (b j)))
    (hdeg : ∀ i j, (a i * b j).natDegree ≤ 2)
    (h0 : ∀ i j, (((a i * b j).coeff 0 : F) : ℂ) ∈ K)
    (h2 : ∀ i j, (((a i * b j).coeff 2 : F) : ℂ) ∈ K) :
    ∀ i j, (a i * b j).coeff 0 = 0 := by
  intro i0 j0
  by_contra hne
  rw [mul_coeff_zero] at hne
  have hA0 : ((a i0).coeff 0 : ℂ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hne
  have hB0 : ((b j0).coeff 0 : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hne
  have ha0 : ∀ i, a i ≠ 0 := fun i h => ha.ne_zero i (by simp [h])
  have hb0 : ∀ j, b j ≠ 0 := fun j h => hb.ne_zero j (by simp [h])
  have hd : ∀ i j, (a i).natDegree + (b j).natDegree ≤ 2 := fun i j => by
    rw [← natDegree_mul (ha0 i) (hb0 j)]; exact hdeg i j
  have h0' : ∀ i j, ((a i).coeff 0 : ℂ) * (b j).coeff 0 ∈ K := fun i j => by
    simpa [mul_coeff_zero] using h0 i j
  by_cases hI : ∀ i, (a i).natDegree = 0
  · refine absurd (card_le ha {((b j0).coeff 0 : ℂ)⁻¹} fun i => ?_) (by simp)
    rw [eq_C_of_natDegree_eq_zero (hI i), aeval_C, am,
      show ((a i).coeff 0 : ℂ) = (a i).coeff 0 * (b j0).coeff 0 * ((b j0).coeff 0 : ℂ)⁻¹ by
        field_simp]
    exact mul_mem_span (h0' i j0) (by simp)
  push Not at hI
  obtain ⟨i1, hi1⟩ := hI
  have hb1 : ∀ j, (b j).natDegree ≤ 1 := fun j => by have := hd i1 j; omega
  obtain ⟨ν, hν⟩ : ∃ ν : ℂ, ∀ j, ∃ k ∈ K, ((b j).coeff 1 : ℂ) = k * ν := by
    by_cases h : ∀ j, (b j).coeff 1 = 0
    · exact ⟨0, fun j => ⟨0, K.zero_mem, by simp [h j]⟩⟩
    push Not at h
    obtain ⟨j1, hj1⟩ := h
    have ha1 : ∀ i, (a i).natDegree ≤ 1 := fun i => by
      have := hd i j1; have := le_natDegree_of_ne_zero hj1; omega
    have hA1 : ((a i1).coeff 1 : ℂ) ≠ 0 := by
      have e : (a i1).natDegree = 1 := by have := ha1 i1; omega
      have : (a i1).coeff 1 ≠ 0 := by rw [← e]; exact leadingCoeff_ne_zero.mpr (ha0 i1)
      exact_mod_cast this
    refine ⟨((a i1).coeff 1 : ℂ)⁻¹, fun j => ⟨_, h2 i1 j, ?_⟩⟩
    rw [coeff_two (ha1 i1) (hb1 j), Subfield.coe_mul]
    field_simp
  refine absurd (card_le hb {ν * u, ((a i0).coeff 0 : ℂ)⁻¹} fun j => ?_)
    (by have := Finset.card_le_two (a := ν * u) (b := ((a i0).coeff 0 : ℂ)⁻¹); simp; omega)
  obtain ⟨k, hk, hkν⟩ := hν j
  rw [eq_X_add_C_of_natDegree_le_one (hb1 j)]
  simp only [map_add, map_mul, aeval_C, aeval_X, am, hkν, mul_assoc]
  rw [show ((b j).coeff 0 : ℂ) = (a i0).coeff 0 * (b j).coeff 0 * ((a i0).coeff 0 : ℂ)⁻¹ by
    field_simp]
  exact Submodule.add_mem _ (mul_mem_span hk (by simp)) (mul_mem_span (h0' i0 j) (by simp))

/-- The coefficients of `u⁻¹` vanish. -/
theorem inv_coeff (K F : Subfield ℂ) (hKF : K ≤ F) (u : ℂ) (hu : Transcendental F u)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (c : Fin 2 → Fin 3 → F) (l m : Fin 2 → Fin 3 → K)
    (heq : ∀ i j, x i * y j = c i j + l i j * u + m i j * u⁻¹) : ∀ i j, m i j = 0 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ isAlgebraic_zero)
  let P : Fin 2 → Fin 3 → F[X] := fun i j =>
    C ⟨l i j, hKF (l i j).2⟩ * X ^ 2 + C (c i j) * X + C ⟨m i j, hKF (m i j).2⟩
  have hPu : ∀ i j, aeval u (P i j) = u * (x i * y j) := fun i j => by
    simp only [P, map_add, map_mul, map_pow, aeval_C, aeval_X, am, heq]
    field_simp
    ring
  have hne : ∀ i j, u * (x i * y j) ≠ 0 := fun i j =>
    mul_ne_zero hu0 (mul_ne_zero (hx.ne_zero i) (hy.ne_zero j))
  have hP0 : ∀ i j, P i j ≠ 0 := fun i j h => hne i j (by rw [← hPu, h, map_zero])
  have hminor : ∀ i i' j j', P i j * P i' j' = P i j' * P i' j := fun i i' j j' => by
    by_contra h
    exact hu ⟨_, sub_ne_zero.mpr h, by simp only [map_sub, map_mul, hPu]; ring⟩
  obtain ⟨a, b, -, hab⟩ := rank_one_polynomial_matrix_factor (↥F) P hP0 hminor
  have hab' : ∀ i j, aeval u (a i) * aeval u (b j) = u * (x i * y j) := fun i j => by
    rw [← map_mul, ← hab, hPu]
  have h00 : aeval u (a 0) * aeval u (b 0) ≠ 0 := by rw [hab']; exact hne 0 0
  have ha := linInd_scale (g := fun i => aeval u (a i)) hx (mul_ne_zero hu0 (hy.ne_zero 0))
    (right_ne_zero_of_mul h00) fun i => (hab' i 0).trans (by ring)
  have hb := linInd_scale (g := fun j => aeval u (b j)) hy (mul_ne_zero hu0 (hx.ne_zero 0))
    (left_ne_zero_of_mul h00) fun j => (mul_comm _ _).trans ((hab' 0 j).trans (by ring))
  have key := coeff_zero_eq_zero K F u a b ha hb
    (fun i j => by rw [← hab]; exact natDegree_quadratic_le)
    (fun i j => by rw [← hab]; simp [P]) (fun i j => by rw [← hab]; simp [P])
  intro i j
  have h1 := key i j
  rw [← hab] at h1
  simp [P] at h1
  simpa using congrArg Subtype.val h1

end R16_inv

open DiazModulus R16_inv in
theorem solution (K F : Subfield ℂ) (hKF : K ≤ F)
    (V₀ : Submodule K ℂ) (hV₀ : ∀ v ∈ V₀, v ∈ F) (u : ℂ) (hu : Transcendental F u)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ V₀ ⊔ Submodule.span K ({u, u⁻¹} : Set ℂ)) :
    ∀ i j, x i * y j ∈ V₀ := by
  have hdec : ∀ i j, ∃ c ∈ V₀, ∃ l m : K, x i * y j = c + l * u + m * u⁻¹ := by
    intro i j
    obtain ⟨c, hc, z, hz, he⟩ := Submodule.mem_sup.mp (hxy i j)
    obtain ⟨l, m, rfl⟩ := Submodule.mem_span_pair.mp hz
    exact ⟨c, hc, l, m, by rw [← he, Subfield.smul_def, Subfield.smul_def, smul_eq_mul,
      smul_eq_mul, add_assoc]⟩
  choose c hc l m h using hdec
  let cF : Fin 2 → Fin 3 → F := fun i j => ⟨c i j, hV₀ _ (hc i j)⟩
  have hm := inv_coeff K F hKF u hu x y hx hy cF l m h
  have hl := inv_coeff K F hKF u⁻¹ (fun h' => hu (IsAlgebraic.inv_iff.mp h')) x y hx hy cF m l
    fun i j => by rw [h, inv_inv]; ring
  intro i j
  simpa [h, hm, hl] using hc i j
