-- Prove2me | solution 1 for DiazModulus.conj_swapped_two_orbit_configuration_invisible_to_four_dimensional_extensions
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T11:59:37.340807+00:00
-- url     : https://prove2.me/submissions/c55512bb-d52d-471c-a971-6e8751db19db

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_two_orbit_configuration_invisible_to_four_dimensional_extensions

open Complex ComplexConjugate

/-! # The swapped two-orbit space: conjugation-stable, a configuration, invisible

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, and `a, a₁, a₂ ∈ Q̄` non-zero with `a ā ≠ s²` and
`a₁ ≠ a₂`. Put `g = a₁/(u − a) + a₂/(u + a)` and `W = span_Q̄ {1, u, u⁻¹, g, ḡ}`.
Since `ū = s²/u`, conjugation sends the pole pair `±a` to the pole pair `±b`, `b = s²/ā ∈ Q̄`:
`ḡ = (ā₂ − ā₁)/ā + γ/(u − b) + δ/(u + b)` with `γ = −ā₁ b/ā`, `δ = −ā₂ b/ā` (`conj_swap`, a rational
identity). As `1 ∈ W`, `W = span_Q̄ {1, u, u⁻¹, g, g'}` with `g' = γ/(u − b) + δ/(u + b)`. Here `b ≠ 0`,
`γ, δ ≠ 0`, and `a² ≠ b²`: otherwise `(a ā)² = (s²)²`, so `a ā = −s²` (the other sign is excluded),
while `a ā + s² = |a|² + |u|² > 0`. With `a₁ ≠ a₂` and `u ū = s²` algebraic, the R14 node
`two_orbit_configuration_invisible_to_four_dimensional_extensions` gives the `2 × 3` configuration
and the invisibility to four-dimensional extensions for `W`. Conjugation stability needs no partial
fractions: `ū = s² u⁻¹`, `conj u⁻¹ = s⁻² u`, conjugation swaps `g` and `ḡ`, and conjugation is
additive and maps `q • w` to `q̄ • w̄` with `q̄ ∈ Q̄`, so by induction on the span `W̄ ⊆ W`.
The reality of `s` is not used: `ū = s²/u` follows from `s² = u ū` alone.
-/

namespace R15_swap

open DiazModulus

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = cjQ a from rfl, Polynomial.aeval_algHom_apply, hp, map_zero]

theorem span_mul_mem {S : Set ℂ} {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ Submodule.span Qbar S) :
    c * v ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hv
  rwa [Subfield.smul_def, smul_eq_mul] at this

theorem span_mem_of_eq {S : Set ℂ} {v z : ℂ} (h : v = z) (hz : z ∈ Submodule.span Qbar S) :
    v ∈ Submodule.span Qbar S := by
  rwa [h]

/-- A span whose generators have conjugates in it is conjugation-stable. -/
theorem span_conj_stable {S : Set ℂ} (hS : ∀ x ∈ S, conj x ∈ Submodule.span Qbar S) :
    ∀ w ∈ Submodule.span Qbar S, conj w ∈ Submodule.span Qbar S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = (⟨conj (c : ℂ), conj_mem_Qbar c.2⟩ : ↥Qbar) • conj x :=
      map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

theorem sub_ne {u x : ℂ} (hu : u ∉ Qbar) (hx : x ∈ Qbar) : u - x ≠ 0 :=
  fun h => hu (by rw [sub_eq_zero.1 h]; exact hx)

theorem add_ne {u x : ℂ} (hu : u ∉ Qbar) (hx : x ∈ Qbar) : u + x ≠ 0 := by
  rw [← sub_neg_eq_add]; exact sub_ne hu (neg_mem hx)

/-- `span_Q̄ {1, u, u⁻¹, g, ḡ}` is conjugation-stable as soon as `u ū = s²` with `s ∈ Q̄`. -/
theorem conj_stable {u s g : ℂ} (hu0 : u ≠ 0) (hs : s ∈ Qbar) (hss : s * s = u * conj u) :
    ∀ w ∈ Submodule.span Qbar ({1, u, u⁻¹, g, conj g} : Set ℂ),
      conj w ∈ Submodule.span Qbar ({1, u, u⁻¹, g, conj g} : Set ℂ) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  have hcu0 : conj u ≠ 0 := (map_ne_zero _).2 hu0
  have hss' : s * s ∈ Qbar := mul_mem hs hs
  have m1 : (1 : ℂ) ∈ Submodule.span Qbar ({1, u, u⁻¹, g, conj g} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have mu : u ∈ Submodule.span Qbar ({1, u, u⁻¹, g, conj g} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have mi : u⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, g, conj g} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have mg : g ∈ Submodule.span Qbar ({1, u, u⁻¹, g, conj g} : Set ℂ) :=
    Submodule.subset_span (by simp)
  have mcg : conj g ∈ Submodule.span Qbar ({1, u, u⁻¹, g, conj g} : Set ℂ) :=
    Submodule.subset_span (by simp)
  refine span_conj_stable ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · rw [map_one]; exact m1
  · -- `ū = s² u⁻¹`
    refine span_mem_of_eq ?_ (span_mul_mem hss' mi)
    field_simp
    linear_combination -hss
  · -- `conj u⁻¹ = s⁻² u`
    refine span_mem_of_eq ?_ (span_mul_mem (inv_mem hss') mu)
    rw [map_inv₀]
    field_simp
    linear_combination hss
  · exact mcg
  · rw [Complex.conj_conj]; exact mg

/-- Conjugating the pole pair at `±a` gives a constant plus the pole pair at `±b`, `ā b = s²`. -/
theorem conj_swap {u s a a₁ a₂ b : ℂ} (hu0 : u ≠ 0) (hA0 : conj a ≠ 0) (hub : u - b ≠ 0)
    (hub' : u + b ≠ 0) (hss : s * s = u * conj u) (hAb : conj a * b = s * s) :
    conj (a₁ / (u - a) + a₂ / (u + a)) = (conj a₂ - conj a₁) / conj a +
      (-(conj a₁ * b / conj a) / (u - b) + -(conj a₂ * b / conj a) / (u + b)) := by
  have hU : conj u = s * s / u := by rw [eq_div_iff hu0]; linear_combination -hss
  have e1 : conj u - conj a = -conj a * (u - b) / u := by
    rw [hU, eq_div_iff hu0, sub_mul, div_mul_cancel₀ _ hu0]
    linear_combination -hAb
  have e2 : conj u + conj a = conj a * (u + b) / u := by
    rw [hU, eq_div_iff hu0, add_mul, div_mul_cancel₀ _ hu0]
    linear_combination -hAb
  rw [map_add, map_div₀, map_div₀, map_sub, map_add, e1, e2]
  field_simp
  ring

/-- Replacing a generator `h = c + h'` (`c ∈ Q̄`) by `h'` does not change a span containing `1`. -/
theorem span_replace {q r g h h' c : ℂ} (hc : c ∈ Qbar) (hh : h = c + h') :
    Submodule.span Qbar ({1, q, r, g, h} : Set ℂ) =
      Submodule.span Qbar ({1, q, r, g, h'} : Set ℂ) := by
  have hh' : h' = h + -c * 1 := by rw [hh]; ring
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · rw [hh, ← mul_one c]
      exact Submodule.add_mem _ (span_mul_mem hc (Submodule.subset_span (by simp)))
        (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · rw [hh']
      exact Submodule.add_mem _ (Submodule.subset_span (by simp))
        (span_mul_mem (neg_mem hc) (Submodule.subset_span (by simp)))

end R15_swap

open DiazModulus R15_swap in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (a a₁ a₂ : ℂ) (ha : a ∈ Qbar) (ha₁ : a₁ ∈ Qbar) (ha₂ : a₂ ∈ Qbar) (ha0 : a ≠ 0)
    (haa : a * conj a ≠ s * s) (ha₁0 : a₁ ≠ 0) (ha₂0 : a₂ ≠ 0) (ha₁₂ : a₁ ≠ a₂) :
    (∀ w ∈ Submodule.span Qbar ({1, u, u⁻¹, (a₁ / (u - a) + a₂ / (u + a)), conj (a₁ / (u - a) + a₂ / (u + a))} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, u⁻¹, (a₁ / (u - a) + a₂ / (u + a)), conj (a₁ / (u - a) + a₂ / (u + a))} : Set ℂ)) ∧
      (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, (a₁ / (u - a) + a₂ / (u + a)), conj (a₁ / (u - a) + a₂ / (u + a))} : Set ℂ)) ∧
        Submodule.span Qbar (Set.range (fun p : Fin 2 × Fin 3 => x p.1 * y p.2)) = Submodule.span Qbar ({1, u, u⁻¹, (a₁ / (u - a) + a₂ / (u + a)), conj (a₁ / (u - a) + a₂ / (u + a))} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, u⁻¹, (a₁ / (u - a) + a₂ / (u + a)), conj (a₁ / (u - a) + a₂ / (u + a))} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  have hss' : s * s ∈ Qbar := mul_mem hs hs
  have hA0 : conj a ≠ 0 := (map_ne_zero _).2 ha0
  have hcA : conj a ∈ Qbar := conj_mem_Qbar ha
  have hc₁ : conj a₁ ∈ Qbar := conj_mem_Qbar ha₁
  have hc₂ : conj a₂ ∈ Qbar := conj_mem_Qbar ha₂
  -- the conjugate pole `b = s²/ā`
  obtain ⟨b, hbdef⟩ : ∃ b : ℂ, b = s * s / conj a := ⟨_, rfl⟩
  have hbQ : b ∈ Qbar := by rw [hbdef]; exact div_mem hss' hcA
  have hb0 : b ≠ 0 := by rw [hbdef]; exact div_ne_zero (mul_ne_zero hs0 hs0) hA0
  have hAb : conj a * b = s * s := by rw [hbdef]; field_simp
  -- `a² ≠ b²`: else `(a ā)² = (s²)²`, and `a ā + s² = |a|² + |u|² > 0`
  have hab : a ^ 2 ≠ b ^ 2 := by
    intro h
    have h1 : (a * conj a - s * s) * (a * conj a + s * s) = 0 := by
      linear_combination conj a ^ 2 * h + (conj a * b + s * s) * hAb
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact haa (sub_eq_zero.1 h2)
    · have h3 : a * conj a + s * s = ((Complex.normSq a + Complex.normSq u : ℝ) : ℂ) := by
        rw [hss, Complex.mul_conj, Complex.mul_conj]; push_cast; ring
      have hpos : 0 < Complex.normSq a + Complex.normSq u :=
        add_pos_of_nonneg_of_pos (Complex.normSq_nonneg a) (Complex.normSq_pos.2 hu0)
      rw [h3] at h2
      exact hpos.ne' (by exact_mod_cast h2)
  have hγ : -(conj a₁ * b / conj a) ∈ Qbar := neg_mem (div_mem (mul_mem hc₁ hbQ) hcA)
  have hδ : -(conj a₂ * b / conj a) ∈ Qbar := neg_mem (div_mem (mul_mem hc₂ hbQ) hcA)
  have hγ0 : -(conj a₁ * b / conj a) ≠ 0 :=
    neg_ne_zero.2 (div_ne_zero (mul_ne_zero ((map_ne_zero _).2 ha₁0) hb0) hA0)
  have hδ0 : -(conj a₂ * b / conj a) ≠ 0 :=
    neg_ne_zero.2 (div_ne_zero (mul_ne_zero ((map_ne_zero _).2 ha₂0) hb0) hA0)
  have hρ : IsAlgebraic ℚ (u * conj u) := mem_Qbar_iff.1 (by rw [← hss]; exact hss')
  have hTb := DiazModulus.two_orbit_configuration_invisible_to_four_dimensional_extensions
    u hu a b a₁ a₂ _ _ ha hbQ ha₁ ha₂ hγ hδ ha0 hb0 hab ha₁0 ha₂0 hγ0 hδ0 (Or.inl ha₁₂) hρ
  have hconj := conj_swap (a₁ := a₁) (a₂ := a₂) hu0 hA0 (sub_ne hu hbQ) (add_ne hu hbQ) hss hAb
  have hc₀ : (conj a₂ - conj a₁) / conj a ∈ Qbar := div_mem (sub_mem hc₂ hc₁) hcA
  refine ⟨conj_stable hu0 hs hss, ?_⟩
  rw [span_replace hc₀ hconj]
  exact hTb
