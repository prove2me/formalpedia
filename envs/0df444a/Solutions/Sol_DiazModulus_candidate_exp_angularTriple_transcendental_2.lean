-- Prove2me | solution 2 for DiazModulus.candidate_exp_angularTriple_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T10:19:42.548964+00:00
-- url     : https://prove2.me/submissions/9b47d154-6863-4d92-8970-51890f7b6995

import Definitions.Def_DiazModulus
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_six_exponentials
import Theorems.Thm_DiazModulus_diaz_locus_dictionary
import Theorems.Thm_Diaz_locus_stable
import Theorems.Thm_Diaz_elliptic_axis_alignment
import Theorems.Thm_Diaz_indep_of_not_axis

open Complex ComplexConjugate

/-- Algebraicity over `ℚ` survives complex conjugation. -/
private theorem isAlgebraic_conj {z : ℂ} (h : IsAlgebraic ℚ z) :
    IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hpz⟩ := h
  refine ⟨p, hp0, ?_⟩
  have hc := congrArg (starRingEnd ℂ) hpz
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, map_sum, Polynomial.sum]
    using hc

private theorem core (hHL : DiazModulus.HermiteLindemann)
    (hSix : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
      ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)))
    {u : ℂ} (h : DiazModulus.IsCandidate u) :
    Transcendental ℚ (Complex.exp (u ^ 2 / conj u)) := by
  -- read the candidate in the locus vocabulary
  obtain ⟨hu0, hexp, hrho⟩ := (DiazModulus.diaz_locus_dictionary.2 u).1 h
  have hcu0 : conj u ≠ 0 := by simpa using hu0
  have hcQ : u * conj u ∈ DiazModulus.Qbar := DiazModulus.mem_Qbar_iff.mpr hrho
  have hc0 : u * conj u ≠ 0 := mul_ne_zero hu0 hcu0
  -- Hermite–Lindemann: `u` itself is transcendental
  have hutr : ¬ IsAlgebraic ℚ u := fun ha => hHL u hu0 ha hexp
  set t : ℂ := u ^ 2 / (u * conj u) with ht_def
  have ht0 : t ≠ 0 := by
    rw [ht_def]; exact div_ne_zero (pow_ne_zero 2 hu0) hc0
  have httr : ¬ IsAlgebraic ℚ t := by
    intro hta
    refine hutr (IsAlgebraic.of_pow two_pos ?_)
    have hu2 : u ^ 2 = (u * conj u) * t := by rw [ht_def]; field_simp
    rw [hu2]
    exact DiazModulus.mem_Qbar_iff.mp
      (mul_mem hcQ (DiazModulus.mem_Qbar_iff.mpr hta))
  -- the first family: `(u, conj u)`.  A locus point is off both axes, and off the axes
  -- `u` and `conj u` are `ℚ`-independent.
  have hoff := (Diaz.elliptic_axis_alignment hutr hrho).1
  have hxli : LinearIndependent ℚ ![u, conj u] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    refine Diaz.indep_of_not_axis hoff.1 hoff.2 ?_
    simpa [Rat.smul_def] using hab
  -- the second family: `(1, t, t⁻¹)`
  have hyli : LinearIndependent ℚ ![(1 : ℂ), t, t⁻¹] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def, mul_one] at hg
    have hq : (g 1 : ℂ) * t ^ 2 + (g 0 : ℂ) * t + (g 2 : ℂ) = 0 := by
      field_simp at hg
      linear_combination hg
    set p : Polynomial ℚ :=
      Polynomial.C (g 1) * Polynomial.X ^ 2 + Polynomial.C (g 0) * Polynomial.X
        + Polynomial.C (g 2) with hp_def
    have hpt : Polynomial.aeval t p = 0 := by
      rw [hp_def]
      simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
        map_pow, eq_ratCast]
      linear_combination hq
    have hp0 : p = 0 := by
      by_contra hne
      exact httr ⟨p, hne, hpt⟩
    have h2 : g 1 = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 2) hp0
      simpa [hp_def] using this
    have h1 : g 0 = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 1) hp0
      simpa [hp_def] using this
    have h0 : g 2 = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 0) hp0
      simpa [hp_def] using this
    intro i
    fin_cases i <;> assumption
  -- suppose the target exponential were algebraic; then all six of them are
  by_contra hcon
  rw [Transcendental, not_not] at hcon
  have hconj : IsAlgebraic ℚ (Complex.exp ((conj u) ^ 2 / u)) := by
    have hce : ((conj u) ^ 2 / u) = conj (u ^ 2 / conj u) := by
      simp [map_div₀, map_pow]
    rw [hce, Complex.exp_conj]
    exact isAlgebraic_conj hcon
  -- the locus is conjugation-stable, so `exp (conj u)` is algebraic too
  have hcexp : IsAlgebraic ℚ (Complex.exp (conj u)) :=
    (Diaz.locus_stable hu0 hexp hrho).1.2.1
  have e01 : u * t = u ^ 2 / conj u := by rw [ht_def]; field_simp
  have e02 : u * t⁻¹ = conj u := by rw [ht_def]; field_simp
  have e11 : conj u * t = u := by rw [ht_def]; field_simp
  have e12 : conj u * t⁻¹ = (conj u) ^ 2 / u := by rw [ht_def]; field_simp
  have hall : ∀ (i : Fin 2) (j : Fin 3),
      IsAlgebraic ℚ (Complex.exp (![u, conj u] i * ![(1 : ℂ), t, t⁻¹] j)) := by
    intro i j
    fin_cases i
    · fin_cases j
      · show IsAlgebraic ℚ (Complex.exp (u * 1))
        rw [mul_one]; exact hexp
      · show IsAlgebraic ℚ (Complex.exp (u * t))
        rw [e01]; exact hcon
      · show IsAlgebraic ℚ (Complex.exp (u * t⁻¹))
        rw [e02]; exact hcexp
    · fin_cases j
      · show IsAlgebraic ℚ (Complex.exp (conj u * 1))
        rw [mul_one]; exact hcexp
      · show IsAlgebraic ℚ (Complex.exp (conj u * t))
        rw [e11]; exact hexp
      · show IsAlgebraic ℚ (Complex.exp (conj u * t⁻¹))
        rw [e12]; exact hconj
  obtain ⟨i, j, hij⟩ := hSix ![u, conj u] ![(1 : ℂ), t, t⁻¹] hxli hyli
  exact hij (hall i j)

open DiazModulus in
theorem solution {u : ℂ} (h : IsCandidate u) :
    Transcendental ℚ (Complex.exp (u ^ 2 / conj u)) :=
  core hermite_lindemann_holds six_exponentials h
