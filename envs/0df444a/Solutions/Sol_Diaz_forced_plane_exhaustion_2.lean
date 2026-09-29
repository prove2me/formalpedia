-- Prove2me | solution 2 for Diaz.forced_plane_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:18:32.254738+00:00
-- url     : https://prove2.me/submissions/cfe0537a-a8d8-47d3-9115-b7229b08b41f

/-
`Diaz.forced_plane_exhaustion` is `Diaz.binary_form_eq_zero` applied to the pair
`(x, y) = (u, ū)`.  The only thing to supply is that the ratio `u/ū` is again
transcendental over `K`: `u² = (u/ū)(u ū)` and `u ū ∈ K`, so an algebraic ratio
would make `u²`, hence `u`, algebraic.
-/
import Mathlib
import Theorems.Thm_Diaz_binary_form_eq_zero

open ComplexConjugate

private theorem gr_algebraMap_mk (K : Subfield ℂ) (a : ℂ) (h : a ∈ K) :
    (algebraMap (↥K) ℂ) ⟨a, h⟩ = a := rfl

/-- With `ρ = u ū ∈ K` and `u` transcendental over `K`, the ratio `u/ū` is
transcendental over `K`. -/
private theorem gr_ratio_transcendental {K : Subfield ℂ} {u : ℂ}
    (hT : Transcendental K u) (hu0 : u ≠ 0) (hρ : u * conj u ∈ K) :
    Transcendental K (u / conj u) := by
  have hcu : conj u ≠ 0 := by simpa using hu0
  intro halg
  have h1 : (u / conj u) ∈ algebraicClosure (↥K) ℂ := mem_algebraicClosure_iff.2 halg
  have h2 : (u * conj u) ∈ algebraicClosure (↥K) ℂ := by
    refine mem_algebraicClosure_iff.2 ⟨Polynomial.X - Polynomial.C ⟨u * conj u, hρ⟩, ?_, ?_⟩
    · exact Polynomial.X_sub_C_ne_zero _
    · rw [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        gr_algebraMap_mk, sub_self]
  have h3 : u ^ 2 ∈ algebraicClosure (↥K) ℂ := by
    have he : u ^ 2 = (u / conj u) * (u * conj u) := by field_simp <;> ring
    rw [he]; exact mul_mem h1 h2
  exact hT (IsAlgebraic.of_pow (by norm_num) (mem_algebraicClosure_iff.1 h3))

theorem solution {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u)
    (hu0 : u ≠ 0) (hρ : u * conj u ∈ K) (d : ℕ) (c : ℕ → ℂ) (hc : ∀ i, c i ∈ K)
    (h : ∑ i ∈ Finset.range (d + 1), c i * u ^ i * (conj u) ^ (d - i) = 0) :
    ∀ i ∈ Finset.range (d + 1), c i = 0 := by
  have hcu : conj u ≠ 0 := by simpa using hu0
  exact Diaz.binary_form_eq_zero hcu (gr_ratio_transcendental hT hu0 hρ) d c hc h
