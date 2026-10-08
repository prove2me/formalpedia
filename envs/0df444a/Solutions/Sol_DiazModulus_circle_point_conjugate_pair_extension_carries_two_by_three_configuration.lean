-- Prove2me | solution 1 for DiazModulus.circle_point_conjugate_pair_extension_carries_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T08:26:19.887746+00:00
-- url     : https://prove2.me/submissions/4840b65e-cf13-4dca-a3fa-b8b835caf276

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-!
# Two-by-three configurations in `Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄`

Let `u ∉ Q̄` with `ρ = u ū` algebraic, let `a ∈ Q̄` be non-zero, and let `z` be `u / (u² - a)` when
`a ā ≠ ρ²`, or `u / (u² - a)²` when `a ā = ρ²`. Then `W = Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄` contains all
six products `xᵢyⱼ` of `x = (1, u²)` and `y = (b, bu², bu⁴)` for a suitable non-zero `b`, and both
`x` and `y` are free over `Q̄`. The six products are `b, bu², bu⁴, bu², bu⁴, bu⁶`
(`config_of_mem`). What makes this work is `u⁻¹ = ρ⁻¹ū ∈ W` (`span_inv_mem`), and that `z̄` is again
a rational function of `u`, since `ū = ρ u⁻¹`.

* `a ā ≠ ρ²`, `z = u / (u² - a)`: with `a' = ρ² / ā`, which differs from `a`,
  `z̄ = -(ρ / ā) · u / (u² - a')`, so `y₁ = u / (u² - a') ∈ W`. Take `b = (u (u² - a)(u² - a'))⁻¹`:
  `b = (a a')⁻¹u⁻¹ + (a (a - a'))⁻¹z + (a' (a' - a))⁻¹y₁`, `bu² = (z - y₁) / (a - a')`,
  `bu⁴ = (a z - a' y₁) / (a - a')`, `bu⁶ = u + (a² z - a'² y₁) / (a - a')`.
* `a ā = ρ²`, `z = u / (u² - a)²`: now `z̄ = (ρ / ā²) · u³ / (u² - a)²`, so
  `y₂ = u / (u² - a) = (ā² / ρ) z̄ - a z ∈ W`. Take `b = (u (u² - a)²)⁻¹`:
  `b = a⁻²u⁻¹ - a⁻²y₂ + a⁻¹z`, `bu² = z`, `bu⁴ = y₂ + a z`, `bu⁶ = u + 2a y₂ + a² z`.

Freeness: `u` is transcendental over `Q̄` (`three_terms`, with exponents `2` and `4`).
-/

namespace R5_config

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

/-- `u² - c ≠ 0` for `c ∈ Q̄`: otherwise `u²`, hence `u`, would be algebraic. -/
theorem sq_sub_ne_zero {u : ℂ} (hu : u ∉ Qbar) {c : ℂ} (hc : c ∈ Qbar) : u ^ 2 - c ≠ 0 := by
  intro h
  have h2 : u ^ 2 ∈ Qbar := by rw [sub_eq_zero.1 h]; exact hc
  exact hu (mem_Qbar_iff.2 ((mem_Qbar_iff.1 h2).of_pow two_pos))

/-- `Q̄` is stable under complex conjugation. -/
theorem conj_mem_Qbar {c : ℂ} (hc : c ∈ Qbar) : conj c ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 hc).algHom
    ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ))

/-! ## Membership in a `Q̄`-span -/

theorem span_mem_of_eq {S : Set ℂ} {v z : ℂ} (h : v = z) (hz : z ∈ Submodule.span Qbar S) :
    v ∈ Submodule.span Qbar S := by
  rwa [h]

theorem span_mul_mem {S : Set ℂ} {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ Submodule.span Qbar S) :
    c * v ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hv
  rwa [Subfield.smul_def, smul_eq_mul] at this

/-- A `Q̄`-combination of three members of a `Q̄`-span is a member. -/
theorem span_comb_mem {S : Set ℂ} {c₁ c₂ c₃ v₁ v₂ v₃ : ℂ} (h₁ : c₁ ∈ Qbar) (h₂ : c₂ ∈ Qbar)
    (h₃ : c₃ ∈ Qbar) (hv₁ : v₁ ∈ Submodule.span Qbar S) (hv₂ : v₂ ∈ Submodule.span Qbar S)
    (hv₃ : v₃ ∈ Submodule.span Qbar S) : c₁ * v₁ + c₂ * v₂ + c₃ * v₃ ∈ Submodule.span Qbar S :=
  add_mem (add_mem (span_mul_mem h₁ hv₁) (span_mul_mem h₂ hv₂)) (span_mul_mem h₃ hv₃)

/-- `u⁻¹ = ρ⁻¹ū` with `ρ = u ū`. -/
theorem inv_eq_mul_conj {u : ℂ} (hu0 : u ≠ 0) : u⁻¹ = (u * conj u)⁻¹ * conj u := by
  rw [mul_inv, mul_assoc, inv_mul_cancel₀ ((_root_.map_ne_zero _).2 hu0), mul_one]

/-- If `ρ = u ū ∈ Q̄`, then `u⁻¹` lies in every `Q̄`-span containing `ū`. -/
theorem span_inv_mem {u : ℂ} (hu0 : u ≠ 0) (hρ : u * conj u ∈ Qbar) {S : Set ℂ}
    (hS : conj u ∈ S) : u⁻¹ ∈ Submodule.span Qbar S := by
  rw [inv_eq_mul_conj hu0]
  exact span_mul_mem (inv_mem hρ) (Submodule.subset_span hS)

/-! ## The configuration `x = (1, u²)`, `y = (b, bu², bu⁴)` -/

/-- If `b ≠ 0` and `b, bu², bu⁴, bu⁶` lie in a `Q̄`-span, then `x = (1, u²)` and
`y = (b, bu², bu⁴)` are free over `Q̄` and their six products lie in that span. -/
theorem config_of_mem {u b : ℂ} (hu : u ∉ Qbar) (hb : b ≠ 0) {S : Set ℂ}
    (h0 : b ∈ Submodule.span Qbar S) (h2 : b * u ^ 2 ∈ Submodule.span Qbar S)
    (h4 : b * u ^ 4 ∈ Submodule.span Qbar S) (h6 : b * u ^ 6 ∈ Submodule.span Qbar S) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧ ∀ i j, x i * y j ∈ Submodule.span Qbar S := by
  refine ⟨![1, u ^ 2], ![b, b * u ^ 2, b * u ^ 4], ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have h' : (s : ℂ) + t * u ^ 2 + (0 : ↥Qbar) * u ^ 4 = 0 := by
      simpa [Subfield.smul_def] using h
    obtain ⟨e0, e1, -⟩ := three_terms hu two_ne_zero four_ne_zero (by norm_num) h'
    exact ⟨e0, e1⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : b * ((g 0 : ℂ) + g 1 * u ^ 2 + g 2 * u ^ 4) = 0 := by
      simp only [Fin.sum_univ_three, Subfield.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
      linear_combination hg
    obtain ⟨e0, e1, e2⟩ := three_terms hu two_ne_zero four_ne_zero (by norm_num)
      ((mul_eq_zero.1 hg').resolve_left hb)
    intro i
    fin_cases i <;> assumption
  · intro i j
    fin_cases i <;> fin_cases j
    · exact span_mem_of_eq (show (1 : ℂ) * b = b by ring) h0
    · exact span_mem_of_eq (show (1 : ℂ) * (b * u ^ 2) = b * u ^ 2 by ring) h2
    · exact span_mem_of_eq (show (1 : ℂ) * (b * u ^ 4) = b * u ^ 4 by ring) h4
    · exact span_mem_of_eq (show u ^ 2 * b = b * u ^ 2 by ring) h2
    · exact span_mem_of_eq (show u ^ 2 * (b * u ^ 2) = b * u ^ 4 by ring) h4
    · exact span_mem_of_eq (show u ^ 2 * (b * u ^ 4) = b * u ^ 6 by ring) h6

/-! ## The two cases -/

/-- `a ā ≠ ρ²`, `z = u / (u² - a)`: `b = (u (u² - a)(u² - a'))⁻¹` with `a' = ρ² / ā`. -/
theorem config_F1 {u a z : ℂ} (hu : u ∉ Qbar) (hρ : u * conj u ∈ Qbar) (ha : a ∈ Qbar)
    (ha0 : a ≠ 0) (h : a * conj a ≠ (u * conj u) ^ 2) (hz : z = u / (u ^ 2 - a)) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  have hc0 : conj u ≠ 0 := (_root_.map_ne_zero _).2 hu0
  have hā := conj_mem_Qbar ha
  have hā0 : conj a ≠ 0 := (_root_.map_ne_zero _).2 ha0
  obtain ⟨a', ha'⟩ : ∃ a', a' = (u * conj u) ^ 2 / conj a := ⟨_, rfl⟩
  have ha'Q : a' ∈ Qbar := ha' ▸ div_mem (pow_mem hρ 2) hā
  have ha'mul : a' * conj a = (u * conj u) ^ 2 := by rw [ha', div_mul_cancel₀ _ hā0]
  have ha'0 : a' ≠ 0 := by
    rw [ha']; exact div_ne_zero (pow_ne_zero 2 (mul_ne_zero hu0 hc0)) hā0
  have hd : a - a' ≠ 0 := fun e => h (by linear_combination (conj a) * e + ha'mul)
  have hd' : a' - a ≠ 0 := fun e => hd (by linear_combination -e)
  have hv := sq_sub_ne_zero hu ha
  have hv' := sq_sub_ne_zero hu ha'Q
  have hcv : conj u ^ 2 - conj a ≠ 0 := by
    rw [← map_pow, ← map_sub]; exact (_root_.map_ne_zero _).2 hv
  have hU : u ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hZ : z ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hZc : conj z ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hI := span_inv_mem (S := {1, u, conj u, z, conj z}) hu0 hρ (by simp)
  -- `y₁ = u / (u² - a') = -(ā / ρ) z̄`
  have hY : u / (u ^ 2 - a') ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
    refine span_mem_of_eq ?_ (span_mul_mem (neg_mem (div_mem hā hρ)) hZc)
    rw [hz, map_div₀, map_sub, map_pow]
    field_simp
    linear_combination -ha'mul
  refine config_of_mem hu (b := (u * (u ^ 2 - a) * (u ^ 2 - a'))⁻¹)
    (inv_ne_zero (mul_ne_zero (mul_ne_zero hu0 hv) hv')) ?_ ?_ ?_ ?_
  · -- `b = (a a')⁻¹ u⁻¹ + (a (a - a'))⁻¹ z + (a' (a' - a))⁻¹ y₁`
    refine span_mem_of_eq ?_ (span_comb_mem (inv_mem (mul_mem ha ha'Q))
      (inv_mem (mul_mem ha (sub_mem ha ha'Q))) (inv_mem (mul_mem ha'Q (sub_mem ha'Q ha))) hI hZ hY)
    rw [hz]
    field_simp
    ring
  · -- `bu² = (a - a')⁻¹ z - (a - a')⁻¹ y₁`
    refine span_mem_of_eq ?_ (span_comb_mem (zero_mem _) (inv_mem (sub_mem ha ha'Q))
      (neg_mem (inv_mem (sub_mem ha ha'Q))) hU hZ hY)
    rw [hz]
    field_simp
    ring
  · -- `bu⁴ = (a / (a - a')) z - (a' / (a - a')) y₁`
    refine span_mem_of_eq ?_ (span_comb_mem (zero_mem _) (div_mem ha (sub_mem ha ha'Q))
      (neg_mem (div_mem ha'Q (sub_mem ha ha'Q))) hU hZ hY)
    rw [hz]
    field_simp
    ring
  · -- `bu⁶ = u + (a² / (a - a')) z - (a'² / (a - a')) y₁`
    refine span_mem_of_eq ?_ (span_comb_mem (one_mem _) (div_mem (pow_mem ha 2) (sub_mem ha ha'Q))
      (neg_mem (div_mem (pow_mem ha'Q 2) (sub_mem ha ha'Q))) hU hZ hY)
    rw [hz]
    field_simp
    ring

/-- `a ā = ρ²`, `z = u / (u² - a)²`: `b = (u (u² - a)²)⁻¹`. -/
theorem config_F2 {u a z : ℂ} (hu : u ∉ Qbar) (hρ : u * conj u ∈ Qbar) (ha : a ∈ Qbar)
    (ha0 : a ≠ 0) (h : a * conj a = (u * conj u) ^ 2) (hz : z = u / (u ^ 2 - a) ^ 2) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  have hc0 : conj u ≠ 0 := (_root_.map_ne_zero _).2 hu0
  have hā := conj_mem_Qbar ha
  have hv := sq_sub_ne_zero hu ha
  have hcv : conj u ^ 2 - conj a ≠ 0 := by
    rw [← map_pow, ← map_sub]; exact (_root_.map_ne_zero _).2 hv
  have hU : u ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hZ : z ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hZc : conj z ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have hI := span_inv_mem (S := {1, u, conj u, z, conj z}) hu0 hρ (by simp)
  -- `y₂ = u / (u² - a) = (ā² / ρ) z̄ - a z`
  have hY : u / (u ^ 2 - a) ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
    refine span_mem_of_eq ?_
      (sub_mem (span_mul_mem (div_mem (pow_mem hā 2) hρ) hZc) (span_mul_mem ha hZ))
    rw [hz, map_div₀, map_pow, map_sub, map_pow]
    field_simp
    linear_combination (2 * u ^ 2 * conj a - a * conj a - (u * conj u) ^ 2) * h
  refine config_of_mem hu (b := (u * (u ^ 2 - a) ^ 2)⁻¹)
    (inv_ne_zero (mul_ne_zero hu0 (pow_ne_zero 2 hv))) ?_ ?_ ?_ ?_
  · -- `b = a⁻² u⁻¹ - a⁻² y₂ + a⁻¹ z`
    refine span_mem_of_eq ?_ (span_comb_mem (inv_mem (pow_mem ha 2))
      (neg_mem (inv_mem (pow_mem ha 2))) (inv_mem ha) hI hY hZ)
    rw [hz]
    field_simp
    ring
  · -- `bu² = z`
    refine span_mem_of_eq ?_ hZ
    rw [hz]
    field_simp
  · -- `bu⁴ = y₂ + a z`
    refine span_mem_of_eq ?_ (add_mem hY (span_mul_mem ha hZ))
    rw [hz]
    field_simp
    ring
  · -- `bu⁶ = u + 2a y₂ + a² z`
    refine span_mem_of_eq ?_ (span_comb_mem (one_mem _) (add_mem ha ha) (pow_mem ha 2) hU hY hZ)
    rw [hz]
    field_simp
    ring

end R5_config

open DiazModulus R5_config in
theorem solution (u a z : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha : a ∈ Qbar) (ha0 : a ≠ 0)
    (hz : (a * conj a ≠ (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a)) ∨
      (a * conj a = (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a) ^ 2)) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
  have hρ' := mem_Qbar_iff.2 hρ
  rcases hz with ⟨h, hz⟩ | ⟨h, hz⟩
  · exact config_F1 hu hρ' ha ha0 h hz
  · exact config_F2 hu hρ' ha ha0 h hz

#print axioms solution
