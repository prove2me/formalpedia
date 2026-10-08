-- Prove2me | solution 1 for DiazModulus.circle_point_extension_carries_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-05T08:18:38.775648+00:00
-- url     : https://prove2.me/submissions/301b2c23-2714-408c-b86d-aecdd519770d

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-!
# Two-by-three configurations at a point of algebraic modulus

Let `u ∉ Q̄` with `ρ = u ū` algebraic, and let `w` be `u²`, `ū²` or `(u - a)⁻¹` for a non-zero
`a ∈ Q̄`. Then `V = Q̄ + Q̄u + Q̄ū + Q̄w` contains all six products `xᵢyⱼ` of some `x ∈ ℂ²` and
`y ∈ ℂ³`, each free over `Q̄`. What makes this work is `u⁻¹ = ρ⁻¹ū ∈ V` (`span_inv_mem`).

* `w = u²`: `x = (1, u)`, `y = (u⁻¹, 1, u)`; the products are `u⁻¹, 1, u, 1, u, u²`.
* `w = ū²`: `x = (1, u⁻¹)`, `y = (u, 1, u⁻¹)`; the products are `u, 1, u⁻¹, 1, u⁻¹, u⁻²`, and
  `u⁻² = ρ⁻²ū²`.
* `w = (u - a)⁻¹`: `x = (u⁻¹, w)`, `y = (1, u, u² - au)`; the products are `u⁻¹, 1, u - a, w,
  1 + aw, u`.

Freeness: `u` is transcendental over `Q̄` (`three_terms`).
-/

namespace R4B_configs

open DiazModulus Polynomial

/-! ## Transcendence of `u` over `Q̄` -/

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes: `u` is transcendental over `ℚ`,
hence over `Q̄`, which is algebraic over `ℚ`. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem ne_zero_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 :=
  fun h => hu (h ▸ Subfield.zero_mem _)

/-- `a + b uᵐ + c uⁿ = 0`, with `0, m, n` distinct, forces `a = b = c = 0`. -/
theorem three_terms {u : ℂ} (hu : u ∉ Qbar) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n)
    {a b c : ↥Qbar} (h : (a : ℂ) + b * u ^ m + c * u ^ n = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hP := aeval_eq_zero hu (P := C a + C b * X ^ m + C c * X ^ n)
    (by simp only [map_add, map_mul, aeval_C, aeval_X_pow]; exact h)
  have h0 := congrArg (coeff · 0) hP
  have h1 := congrArg (coeff · m) hP
  have h2 := congrArg (coeff · n) hP
  simp [coeff_C, coeff_X_pow, hm, hn, hmn, hm.symm, hn.symm, hmn.symm] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem quad_terms {u : ℂ} (hu : u ∉ Qbar) {a b c : ↥Qbar}
    (h : (a : ℂ) + b * u + c * u ^ 2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have h' : (a : ℂ) + b * u ^ 1 + c * u ^ 2 = 0 := by rw [pow_one]; exact h
  exact three_terms hu one_ne_zero two_ne_zero (by norm_num) h'

theorem two_terms {u : ℂ} (hu : u ∉ Qbar) {a b : ↥Qbar} (h : (a : ℂ) + b * u = 0) :
    a = 0 ∧ b = 0 := by
  have h' : (a : ℂ) + b * u + (0 : ↥Qbar) * u ^ 2 = 0 := by simpa using h
  obtain ⟨ha, hb, -⟩ := quad_terms hu h'
  exact ⟨ha, hb⟩

/-! ## Membership in a `Q̄`-span -/

theorem span_mem_of_eq {S : Set ℂ} {v z : ℂ} (h : v = z) (hz : z ∈ Submodule.span Qbar S) :
    v ∈ Submodule.span Qbar S := by
  rwa [h]

theorem span_mul_mem {S : Set ℂ} {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ Submodule.span Qbar S) :
    c * v ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hv
  rwa [Subfield.smul_def, smul_eq_mul] at this

/-- `u⁻¹ = ρ⁻¹ū` with `ρ = u ū`. -/
theorem inv_eq_mul_conj {u : ℂ} (hu0 : u ≠ 0) : u⁻¹ = (u * conj u)⁻¹ * conj u := by
  rw [mul_inv, mul_assoc, inv_mul_cancel₀ ((_root_.map_ne_zero _).2 hu0), mul_one]

/-- If `ρ = u ū ∈ Q̄`, then `u⁻¹` lies in every `Q̄`-span containing `ū`. -/
theorem span_inv_mem {u : ℂ} (hu0 : u ≠ 0) (hρ : u * conj u ∈ Qbar) {S : Set ℂ}
    (hS : conj u ∈ S) : u⁻¹ ∈ Submodule.span Qbar S := by
  rw [inv_eq_mul_conj hu0]
  exact span_mul_mem (inv_mem hρ) (Submodule.subset_span hS)

/-! ## The three configurations -/

/-- `w = u²`: `x = (1, u)`, `y = (u⁻¹, 1, u)`. -/
theorem config_sq {u : ℂ} (hu : u ∉ Qbar) (hρ : u * conj u ∈ Qbar) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, u ^ 2} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  have hu1 : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  have h1 : (1 : ℂ) ∈ Submodule.span Qbar ({1, u, conj u, u ^ 2} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hU : u ∈ Submodule.span Qbar ({1, u, conj u, u ^ 2} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hW : u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, u ^ 2} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hI := span_inv_mem (S := {1, u, conj u, u ^ 2}) hu0 hρ (by simp)
  refine ⟨![1, u], ![u⁻¹, 1, u], ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t h
    exact two_terms hu (by simpa [Subfield.smul_def] using h)
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (g 0 : ℂ) * u⁻¹ + g 1 + g 2 * u = 0 := by
      simpa [Fin.sum_univ_three, Subfield.smul_def] using hg
    obtain ⟨e0, e1, e2⟩ := quad_terms hu (a := g 0) (b := g 1) (c := g 2)
      (by linear_combination u * hg' - (g 0 : ℂ) * hu1)
    intro i
    fin_cases i <;> assumption
  · intro i j
    fin_cases i <;> fin_cases j
    · exact span_mem_of_eq (show (1 : ℂ) * u⁻¹ = u⁻¹ by ring) hI
    · exact span_mem_of_eq (show (1 : ℂ) * 1 = 1 by ring) h1
    · exact span_mem_of_eq (show (1 : ℂ) * u = u by ring) hU
    · exact span_mem_of_eq hu1 h1
    · exact span_mem_of_eq (show u * 1 = u by ring) hU
    · exact span_mem_of_eq (show u * u = u ^ 2 by ring) hW

/-- `w = ū²`: `x = (1, u⁻¹)`, `y = (u, 1, u⁻¹)`. -/
theorem config_conj_sq {u : ℂ} (hu : u ∉ Qbar) (hρ : u * conj u ∈ Qbar) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, conj u ^ 2} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  have hu1 : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  have h1 : (1 : ℂ) ∈ Submodule.span Qbar ({1, u, conj u, conj u ^ 2} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hU : u ∈ Submodule.span Qbar ({1, u, conj u, conj u ^ 2} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hI := span_inv_mem (S := {1, u, conj u, conj u ^ 2}) hu0 hρ (by simp)
  -- `u⁻² = ρ⁻² ū²`
  have hI2 : u⁻¹ * u⁻¹ ∈ Submodule.span Qbar ({1, u, conj u, conj u ^ 2} : Set ℂ) := by
    have e := inv_eq_mul_conj hu0
    refine span_mem_of_eq (z := (u * conj u)⁻¹ ^ 2 * conj u ^ 2)
      (by linear_combination (u⁻¹ + (u * conj u)⁻¹ * conj u) * e) ?_
    exact span_mul_mem (pow_mem (inv_mem hρ) 2) (Submodule.subset_span (by simp))
  refine ⟨![1, u⁻¹], ![u, 1, u⁻¹], ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have h' : (s : ℂ) + t * u⁻¹ = 0 := by simpa [Subfield.smul_def] using h
    obtain ⟨e1, e0⟩ := two_terms hu (a := t) (b := s)
      (by linear_combination u * h' - (t : ℂ) * hu1)
    exact ⟨e0, e1⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (g 0 : ℂ) * u + g 1 + g 2 * u⁻¹ = 0 := by
      simpa [Fin.sum_univ_three, Subfield.smul_def] using hg
    obtain ⟨e2, e1, e0⟩ := quad_terms hu (a := g 2) (b := g 1) (c := g 0)
      (by linear_combination u * hg' - (g 2 : ℂ) * hu1)
    intro i
    fin_cases i <;> assumption
  · intro i j
    fin_cases i <;> fin_cases j
    · exact span_mem_of_eq (show (1 : ℂ) * u = u by ring) hU
    · exact span_mem_of_eq (show (1 : ℂ) * 1 = 1 by ring) h1
    · exact span_mem_of_eq (show (1 : ℂ) * u⁻¹ = u⁻¹ by ring) hI
    · exact span_mem_of_eq (show u⁻¹ * u = 1 by rw [mul_comm]; exact hu1) h1
    · exact span_mem_of_eq (show u⁻¹ * 1 = u⁻¹ by ring) hI
    · exact hI2

/-- `w = (u - a)⁻¹`: `x = (u⁻¹, w)`, `y = (1, u, u² - au)`. -/
theorem config_shift {u : ℂ} {a : ↥Qbar} (hu : u ∉ Qbar) (hρ : u * conj u ∈ Qbar)
    (ha0 : (a : ℂ) ≠ 0) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  have hv0 : u - a ≠ 0 := fun h => hu (by rw [sub_eq_zero.1 h]; exact a.2)
  have hu1 : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  have hv1 : (u - a) * (u - a)⁻¹ = 1 := mul_inv_cancel₀ hv0
  have ha : a ≠ 0 := fun h => ha0 (by simp [h])
  have h1 : (1 : ℂ) ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hU : u ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hW : (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hI := span_inv_mem (S := {1, u, conj u, (u - a)⁻¹}) hu0 hρ (by simp)
  have hA : u - a ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ) :=
    sub_mem hU (span_mem_of_eq (mul_one _).symm (span_mul_mem a.2 h1))
  have hB : 1 + a * (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ) :=
    add_mem h1 (span_mul_mem a.2 hW)
  refine ⟨![u⁻¹, (u - a)⁻¹], ![1, u, u ^ 2 - a * u], ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have h' : (s : ℂ) * u⁻¹ + t * (u - a)⁻¹ = 0 := by simpa [Subfield.smul_def] using h
    -- clearing denominators: `s (u - a) + t u = 0`
    obtain ⟨e1, e2⟩ := two_terms hu (a := -(s * a)) (b := s + t) (by
      push_cast
      linear_combination (u * (u - a)) * h' - ((s : ℂ) * (u - a)) * hu1 - ((t : ℂ) * u) * hv1)
    have hs : s = 0 := (mul_eq_zero.1 (neg_eq_zero.1 e1)).resolve_right ha
    rw [hs, zero_add] at e2
    exact ⟨hs, e2⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (g 0 : ℂ) + g 1 * u + g 2 * (u ^ 2 - a * u) = 0 := by
      simpa [Fin.sum_univ_three, Subfield.smul_def] using hg
    obtain ⟨e0, e1, e2⟩ := quad_terms hu (a := g 0) (b := g 1 - g 2 * a) (c := g 2) (by
      push_cast
      linear_combination hg')
    rw [e2, zero_mul, sub_zero] at e1
    intro i
    fin_cases i <;> assumption
  · intro i j
    fin_cases i <;> fin_cases j
    · exact span_mem_of_eq (show u⁻¹ * 1 = u⁻¹ by ring) hI
    · exact span_mem_of_eq (show u⁻¹ * u = 1 by rw [mul_comm]; exact hu1) h1
    · exact span_mem_of_eq (show u⁻¹ * (u ^ 2 - a * u) = u - a by
        linear_combination (u - a) * hu1) hA
    · exact span_mem_of_eq (show (u - a)⁻¹ * 1 = (u - a)⁻¹ by ring) hW
    · exact span_mem_of_eq (show (u - a)⁻¹ * u = 1 + a * (u - a)⁻¹ by
        linear_combination hv1) hB
    · exact span_mem_of_eq (show (u - a)⁻¹ * (u ^ 2 - a * u) = u by
        linear_combination u * hv1) hU

end R4B_configs

open DiazModulus R4B_configs in
theorem solution (u w : ℂ) (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hw : w = u ^ 2 ∨ w = conj u ^ 2 ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ w = (u - a)⁻¹) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  have hρ' := mem_Qbar_iff.2 hρ
  rcases hw with rfl | rfl | ⟨a, ha, ha0, rfl⟩
  · exact config_sq hu hρ'
  · exact config_conj_sq hu hρ'
  · exact config_shift (a := ⟨a, ha⟩) hu hρ' ha0

#print axioms solution
