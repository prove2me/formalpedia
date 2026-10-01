-- Prove2me | solution 1 for DiazModulus.algebraic_modulus_log_multiplier_rational
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T08:56:01.499987+00:00
-- url     : https://prove2.me/submissions/1b3b32a8-3837-4624-bb56-b7ab103cbb66

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Schanuel_gelfond_schneider
import Theorems.Thm_DiazModulus_logAlg_conj_stable

/-!
# Multipliers of a logarithm, with algebraic modulus

Waldschmidt's *Diophantine Approximation on Linear Algebraic Groups* (2000), p. 399, lists as an open
problem, following G. Diaz (JTNB 9, 1997), a consequence of the strong four exponentials conjecture:
if `λ ∈ ℒ ∖ {0}`, `|u|` is algebraic and `e^{uλ}` is algebraic, then `u ∈ ℚ` or `uλ/λ̄ ∈ ℚ`.

Here it is proved for `u ∈ ℒ̃`, assuming Roy's strong six exponentials theorem (`hSSE`) and Baker's
theorem in its two-logarithm inhomogeneous form (`hB`).

* If `u` is algebraic, Gelfond–Schneider gives `u ∈ ℚ`.
* Otherwise the six products of `x = (1, u)` and `y = (λ, conj (uλ), 1)` lie in `ℒ̃`, because
  `u · conj (uλ) = |u|² λ̄`. As `x` is free over `Q̄`, `y` is not: `aλ + b·conj (uλ) + c = 0`.
  Baker makes `λ` and `conj (uλ)` linearly dependent over `ℚ`, so `conj (uλ) = rλ` with `r`
  rational; conjugating, `uλ/λ̄ = r`.
-/

open Complex ComplexConjugate

namespace ModulusMultiplier

open DiazModulus

theorem mem_of_log {z : ℂ} (h : z ∈ LogAlg) : z ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert_of_mem _ h)

theorem one_mem : (1 : ℂ) ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem mul_mem {c z : ℂ} (hc : c ∈ Qbar) (hz : z ∈ LogAlgTilde) : c * z ∈ LogAlgTilde :=
  Submodule.smul_mem LogAlgTilde (⟨c, hc⟩ : ↥Qbar) hz

end ModulusMultiplier

open DiazModulus ModulusMultiplier in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y))
    {l u : ℂ} (hl : l ∈ LogAlg) (hl0 : l ≠ 0) (hu : u ∈ LogAlgTilde)
    (hnorm : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ))
    (hexp : IsAlgebraic ℚ (Complex.exp (u * l))) :
    (∃ q : ℚ, u = (q : ℂ)) ∨ (∃ q : ℚ, u * l / conj l = (q : ℂ)) := by
  by_cases huQ : u ∈ Qbar
  · -- `u` algebraic: Gelfond–Schneider
    left
    by_contra hne
    push Not at hne
    exact Schanuel.gelfond_schneider u l (mem_Qbar_iff.mp huQ) hne hl hl0 hexp
  right
  have hul : u * l ∈ LogAlg := hexp
  obtain ⟨μ, hμ⟩ : ∃ μ, conj (u * l) = μ := ⟨_, rfl⟩
  have hμL : μ ∈ LogAlg := hμ ▸ logAlg_conj_stable _ hul
  have hlc : conj l ∈ LogAlg := logAlg_conj_stable _ hl
  -- `x = (1, u)` is free over `Q̄`
  have hx : LinearIndependent (↥Qbar) ![(1 : ℂ), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' : (s : ℂ) * 1 + (t : ℂ) * u = 0 := hst
    by_cases ht : (t : ℂ) = 0
    · have hs : (s : ℂ) = 0 := by simpa [ht] using h'
      exact ⟨by exact_mod_cast hs, by exact_mod_cast ht⟩
    · exfalso
      apply huQ
      have hu' : u = -(s : ℂ) / t := by field_simp; linear_combination h'
      rw [hu']
      exact Qbar.div_mem (Qbar.neg_mem s.2) t.2
  -- the six products lie in `ℒ̃`
  have hprod : ∀ i j, ![(1 : ℂ), u] i * ![l, μ, 1] j ∈ LogAlgTilde := by
    have hn2 : ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar := Qbar.pow_mem (mem_Qbar_iff.mpr hnorm) 2
    have huμ : u * μ = ((‖u‖ : ℝ) : ℂ) ^ 2 * conj l := by
      rw [← hμ, map_mul, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using mem_of_log hl
    · simpa using mem_of_log hμL
    · simpa using one_mem
    · simpa using mem_of_log hul
    · simpa [huμ] using mul_mem hn2 (mem_of_log hlc)
    · simpa using hu
  have hy : ¬ LinearIndependent (↥Qbar) ![l, μ, 1] := fun hy => hSSE _ _ hx hy hprod
  rw [Fintype.not_linearIndependent_iff] at hy
  obtain ⟨g, hg, i₀, hi₀⟩ := hy
  rw [Fin.sum_univ_three] at hg
  have hg' : (g 0 : ℂ) * l + (g 1 : ℂ) * μ + (g 2 : ℂ) * 1 = 0 := hg
  -- Baker: `λ` and `μ` are linearly dependent over `ℚ`
  have hdep : ¬ ∀ p q : ℚ, (p : ℂ) * l + (q : ℂ) * μ = 0 → p = 0 ∧ q = 0 := by
    intro hind
    by_cases hab : (g 0 : ℂ) = 0 ∧ (g 1 : ℂ) = 0
    · have h2 : (g 2 : ℂ) = 0 := by rw [hab.1, hab.2] at hg'; simpa using hg'
      have h0 : g 0 = 0 := by exact_mod_cast hab.1
      have h1 : g 1 = 0 := by exact_mod_cast hab.2
      have h2' : g 2 = 0 := by exact_mod_cast h2
      have hall : ∀ i, g i = 0 := by
        intro i; fin_cases i
        · exact h0
        · exact h1
        · exact h2'
      exact hi₀ (hall i₀)
    · refine hB l μ (g 0) (g 1) hl hμL hind (mem_Qbar_iff.mp (g 0).2) (mem_Qbar_iff.mp (g 1).2)
        hab ?_
      have : (g 0 : ℂ) * l + (g 1 : ℂ) * μ = -(g 2 : ℂ) := by linear_combination hg'
      rw [this]
      exact (mem_Qbar_iff.mp (g 2).2).neg
  push Not at hdep
  obtain ⟨p, q, hpq, hne⟩ := hdep
  have hq : (q : ℂ) ≠ 0 := by
    intro hq0
    have hq0' : q = 0 := by exact_mod_cast hq0
    have hpl : (p : ℂ) * l = 0 := by rw [hq0, zero_mul, add_zero] at hpq; exact hpq
    have hp : p = 0 := by
      rcases mul_eq_zero.mp hpl with h | h
      · exact_mod_cast h
      · exact absurd h hl0
    exact hne hp hq0'
  refine ⟨-(p / q), ?_⟩
  have hlc0 : conj l ≠ 0 := (map_ne_zero _).mpr hl0
  have hμ' : μ = -((p : ℂ) / q) * l := by field_simp; linear_combination hpq
  have hcl : u * l = -((p : ℂ) / q) * conj l := by
    rw [← Complex.conj_conj (u * l), hμ, hμ', map_mul, map_neg, map_div₀, map_ratCast, map_ratCast]
  rw [hcl]
  push_cast
  field_simp
