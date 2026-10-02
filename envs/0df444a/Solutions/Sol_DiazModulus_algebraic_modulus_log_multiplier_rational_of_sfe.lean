-- Prove2me | solution 1 for DiazModulus.algebraic_modulus_log_multiplier_rational_of_sfe
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T14:42:38.900982+00:00
-- url     : https://prove2.me/submissions/149affac-ad2c-42e6-8822-5e15749928bd

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Schanuel_gelfond_schneider
import Theorems.Thm_DiazModulus_logAlg_conj_stable

/-!
# Algebraic modulus: the multiplier of a logarithm is rational, under strong four exponentials

The second open statement on p. 399 of Waldschmidt's *Diophantine Approximation on Linear
Algebraic Groups*, which he derives from the strong four exponentials conjecture: if `l ∈ ℒ ∖ {0}`,
`|u|` is algebraic and `e^{ul}` is algebraic, then `u ∈ ℚ` or `ul/l̄ ∈ ℚ`. No Baker is needed.

1. Strong four exponentials at `x = (1, u)` and `y = (l, ū l̄)`. The four products are `l`,
   `ū l̄ = conj (ul)`, `ul` and `u ū l̄ = |u|² l̄`; the first three lie in `ℒ`, the last is a
   `Q̄`-multiple of `l̄ ∈ ℒ`. So `x` or `y` is `Q̄`-dependent.
2. `x` dependent: `u ∈ Q̄`, and Gelfond–Schneider makes `e^{ul}` transcendental unless `u ∈ ℚ`.
3. `y` dependent: `conj (ul) = c l` with `c ∈ Q̄`, and Gelfond–Schneider makes `e^{cl} = conj e^{ul}`
   transcendental unless `c ∈ ℚ`. Conjugating, `ul = c l̄`.
-/

open Complex ComplexConjugate

namespace DiazLogMultiplier

open DiazModulus

theorem mem_of_log {z : ℂ} (h : z ∈ LogAlg) : z ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert_of_mem _ h)

/-- `u ū z = |u|² z` lies in `ℒ̃` when `|u|` is algebraic and `z ∈ ℒ`. -/
theorem mul_conj_mul_mem {u z : ℂ} (hu : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ)) (hz : z ∈ LogAlg) :
    u * conj u * z ∈ LogAlgTilde := by
  have hmem : ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar := mem_Qbar_iff.mpr (hu.pow 2)
  have e : u * conj u * z = (⟨((‖u‖ : ℝ) : ℂ) ^ 2, hmem⟩ : Qbar) • z := by
    show u * conj u * z = ((‖u‖ : ℝ) : ℂ) ^ 2 * z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [e]
  exact Submodule.smul_mem _ _ (mem_of_log hz)

/-- Under strong four exponentials, `u ∈ ℚ` or `ul/l̄ ∈ ℚ`. -/
theorem log_multiplier_rational (hS : StrongFourExponentials) (l u : ℂ) (hl : l ∈ LogAlg)
    (hl0 : l ≠ 0) (hu : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ))
    (hul : IsAlgebraic ℚ (Complex.exp (u * l))) :
    (∃ q : ℚ, u = (q : ℂ)) ∨ (∃ q : ℚ, u * l / conj l = (q : ℂ)) := by
  by_cases h1 : ∃ q : ℚ, u = (q : ℂ)
  · exact Or.inl h1
  by_cases h2 : ∃ q : ℚ, u * l / conj l = (q : ℂ)
  · exact Or.inr h2
  exfalso
  have hnq : ∀ q : ℚ, u ≠ (q : ℂ) := fun q hq => h1 ⟨q, hq⟩
  have hnq' : ∀ q : ℚ, u * l / conj l ≠ (q : ℂ) := fun q hq => h2 ⟨q, hq⟩
  have hulc : conj (u * l) ∈ LogAlg := logAlg_conj_stable (u * l) hul
  -- `x = (1, u)` is free over `Q̄`: otherwise `u ∈ Q̄ ∖ ℚ`, and Gelfond–Schneider applies
  have hx : LinearIndependent (↥Qbar) ![(1 : ℂ), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    change (s : ℂ) * 1 + (t : ℂ) * u = 0 at hst
    by_cases ht : (t : ℂ) = 0
    · rw [ht, zero_mul, add_zero, mul_one] at hst
      exact ⟨ZeroMemClass.coe_eq_zero.mp hst, ZeroMemClass.coe_eq_zero.mp ht⟩
    · exfalso
      have hu_eq : u = -(s : ℂ) / t := by
        rw [eq_div_iff ht]
        linear_combination hst
      have hualg : IsAlgebraic ℚ u := by
        rw [hu_eq]
        exact mem_Qbar_iff.mp (Qbar.div_mem (Qbar.neg_mem s.2) t.2)
      exact Schanuel.gelfond_schneider u l hualg hnq hl hl0 hul
  -- `y = (l, ū l̄)` is free over `Q̄`: otherwise `conj (ul) = c l` with `c ∈ Q̄`
  have hy : LinearIndependent (↥Qbar) ![l, conj u * conj l] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    change (a : ℂ) * l + (b : ℂ) * (conj u * conj l) = 0 at hab
    by_cases hb : (b : ℂ) = 0
    · rw [hb, zero_mul, add_zero] at hab
      exact ⟨ZeroMemClass.coe_eq_zero.mp ((mul_eq_zero.mp hab).resolve_right hl0),
        ZeroMemClass.coe_eq_zero.mp hb⟩
    · exfalso
      have hcQ : -(a : ℂ) / b ∈ Qbar := Qbar.div_mem (Qbar.neg_mem a.2) b.2
      have hcl : conj (u * l) = -(a : ℂ) / b * l := by
        rw [map_mul, div_mul_eq_mul_div, eq_div_iff hb]
        linear_combination hab
      by_cases hcq : ∃ q : ℚ, -(a : ℂ) / b = (q : ℂ)
      · -- `c = q ∈ ℚ`: conjugating, `ul = q l̄`
        obtain ⟨q, hq⟩ := hcq
        apply hnq' q
        have hcl0 : conj l ≠ 0 := (map_ne_zero _).mpr hl0
        have h2 := congrArg conj hcl
        rw [Complex.conj_conj, hq, map_mul, map_ratCast] at h2
        rw [div_eq_iff hcl0]
        exact h2
      · -- `c ∉ ℚ`: Gelfond–Schneider makes `e^{cl} = e^{conj (ul)}` transcendental
        have hcq' : ∀ q : ℚ, -(a : ℂ) / b ≠ (q : ℂ) := fun q hq => hcq ⟨q, hq⟩
        apply Schanuel.gelfond_schneider _ l (mem_Qbar_iff.mp hcQ) hcq' hl hl0
        rw [← hcl]
        exact hulc
  have h11 : (1 : ℂ) * l ∈ LogAlgTilde := by
    rw [one_mul]
    exact mem_of_log hl
  have h12 : (1 : ℂ) * (conj u * conj l) ∈ LogAlgTilde := by
    rw [one_mul, ← map_mul]
    exact mem_of_log hulc
  have h21 : u * l ∈ LogAlgTilde := mem_of_log hul
  have h22 : u * (conj u * conj l) ∈ LogAlgTilde := by
    rw [← mul_assoc]
    exact mul_conj_mul_mem hu (logAlg_conj_stable l hl)
  exact hS 1 u l (conj u * conj l) hx hy ⟨h11, h12, h21, h22⟩

end DiazLogMultiplier

open DiazModulus DiazLogMultiplier in
theorem solution (hS : StrongFourExponentials) :
    ∀ l u : ℂ, l ∈ LogAlg → l ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) →
      IsAlgebraic ℚ (Complex.exp (u * l)) →
      (∃ q : ℚ, u = (q : ℂ)) ∨ (∃ q : ℚ, u * l / conj l = (q : ℂ)) :=
  log_multiplier_rational hS
