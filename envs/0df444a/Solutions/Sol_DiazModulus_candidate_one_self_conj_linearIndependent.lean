-- Prove2me | solution 1 for DiazModulus.candidate_one_self_conj_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T17:57:24.346781+00:00
-- url     : https://prove2.me/submissions/a0bdf5ab-9513-4bd1-8089-fc42a7dbf8b8

import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

/-!
# `1`, `u`, `conj u` are `Q̄`-linearly independent for a candidate `u`

`DiazModulus.StrongFourExponentials` consumes `Q̄`-linear independence of pairs, and
`DiazModulus.diaz_of_strongFourExponentials_and_hermite_lindemann` is already proved, so this
is the node joining the candidate picture to that reduction.

The argument is elementary.  A relation `A + B·u + C·conj u = 0` over `Q̄`, multiplied by `u`,
becomes `B·u² + A·u + C·(u * conj u) = 0`, and `u * conj u = ‖u‖²` is algebraic by the
candidate's second clause.  If `B ≠ 0` we may complete the square: `(u + A/(2B))²` lies in `Q̄`,
so `u` does too by `IsAlgebraic.of_pow`.  If `B = 0` and `A ≠ 0` then `conj u ∈ Q̄`, hence
`u ∈ Q̄`.  Either way `u` is algebraic, and Hermite–Lindemann contradicts the candidate's third
clause.  What remains, `A = B = 0`, forces `C · conj u = 0` with `conj u ≠ 0`.

Hermite–Lindemann is not assumed here: it is the mission's own proved node
`DiazModulus.hermite_lindemann_holds`, imported above.
-/

namespace DiazModulus

/-- Algebraicity over `ℚ` survives complex conjugation: a rational polynomial killing `z`
has coefficients fixed by `conj`, so it kills `conj z` too. -/
private theorem isAlgebraic_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hpz⟩ := h
  refine ⟨p, hp0, ?_⟩
  have hc := congrArg (starRingEnd ℂ) hpz
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, map_sum, Polynomial.sum]
    using hc

private theorem conj_mem_Qbar {z : ℂ} (h : z ∈ Qbar) : conj z ∈ Qbar :=
  mem_Qbar_iff.mpr (isAlgebraic_conj (mem_Qbar_iff.mp h))

private theorem two_mem_Qbar : (2 : ℂ) ∈ Qbar := by simp

private theorem four_mem_Qbar : (4 : ℂ) ∈ Qbar := by simp

/-- The `Q̄`-action on `ℂ` is multiplication by the underlying complex number. -/
private theorem qbar_smul (a : ↥Qbar) (z : ℂ) : a • z = (a : ℂ) * z := rfl

/-- For a candidate `u`, the three complex numbers `1`, `u`, `conj u` are linearly independent
over the field of algebraic numbers. -/
theorem candidate_one_self_conj_linearIndependent_aux {u : ℂ} (h : IsCandidate u) :
    LinearIndependent (↥Qbar) ![(1 : ℂ), u, conj u] := by
  obtain ⟨hu0, hmod, hexp⟩ := h
  -- Hermite–Lindemann, from the mission's proved node.
  have hHL : HermiteLindemann := DiazModulus.hermite_lindemann_holds
  -- A candidate is transcendental: otherwise `exp u` would be transcendental.
  have hT : u ∉ Qbar := fun hm => hHL u hu0 (mem_Qbar_iff.mp hm) hexp
  -- `u * conj u = ‖u‖²` is algebraic.
  have hc : u * conj u ∈ Qbar := by
    have hnorm : ((‖u‖ : ℝ) : ℂ) ∈ Qbar := mem_Qbar_iff.mpr hmod
    have key : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [key]
    exact pow_mem hnorm 2
  have hcu : conj u ≠ 0 := by simpa using hu0
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hrel : (g 0 : ℂ) + (g 1 : ℂ) * u + (g 2 : ℂ) * conj u = 0 := by
    rw [Fin.sum_univ_three] at hg
    simpa [qbar_smul] using hg
  -- Step 1: the coefficient of `u` vanishes, by completing the square.
  have hB : (g 1 : ℂ) = 0 := by
    by_contra hBne
    refine hT ?_
    have hq : (g 1 : ℂ) * u ^ 2 + (g 0 : ℂ) * u + (g 2 : ℂ) * (u * conj u) = 0 := by
      linear_combination u * hrel
    set a : ℂ := (g 0 : ℂ) / (g 1 : ℂ) with ha
    set d : ℂ := ((g 2 : ℂ) * (u * conj u)) / (g 1 : ℂ) with hd
    have haQ : a ∈ Qbar := div_mem (g 0).2 (g 1).2
    have hdQ : d ∈ Qbar := div_mem (mul_mem (g 2).2 hc) (g 1).2
    have hmonic : u ^ 2 + a * u + d = 0 := by
      rw [ha, hd]
      field_simp
      linear_combination hq
    have hsq : (u + a / 2) ^ 2 = a ^ 2 / 4 - d := by linear_combination hmonic
    have hsqQ : (u + a / 2) ^ 2 ∈ Qbar := by
      rw [hsq]
      exact sub_mem (div_mem (pow_mem haQ 2) four_mem_Qbar) hdQ
    have hwQ : u + a / 2 ∈ Qbar :=
      mem_Qbar_iff.mpr (IsAlgebraic.of_pow two_pos (mem_Qbar_iff.mp hsqQ))
    have := sub_mem hwQ (div_mem haQ two_mem_Qbar)
    simpa using this
  -- Step 2: the constant coefficient vanishes, else `conj u` — hence `u` — is algebraic.
  have hrel2 : (g 0 : ℂ) + (g 2 : ℂ) * conj u = 0 := by
    rw [hB] at hrel
    linear_combination hrel
  have hA : (g 0 : ℂ) = 0 := by
    by_contra hAne
    have hCne : (g 2 : ℂ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, add_zero] at hrel2
      exact hAne hrel2
    have hconj : conj u = -(g 0 : ℂ) / (g 2 : ℂ) := by
      field_simp
      linear_combination hrel2
    have hcq : conj u ∈ Qbar := by
      rw [hconj]
      exact div_mem (neg_mem (g 0).2) (g 2).2
    exact hT (by simpa using conj_mem_Qbar hcq)
  -- Step 3: what is left forces the last coefficient to vanish.
  have hC : (g 2 : ℂ) = 0 := by
    rw [hA] at hrel2
    have : (g 2 : ℂ) * conj u = 0 := by linear_combination hrel2
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hcu
  fin_cases i
  · exact ZeroMemClass.coe_eq_zero.mp hA
  · exact ZeroMemClass.coe_eq_zero.mp hB
  · exact ZeroMemClass.coe_eq_zero.mp hC

end DiazModulus

open DiazModulus in
theorem solution {u : ℂ} (h : IsCandidate u) :
    LinearIndependent (↥Qbar) ![(1 : ℂ), u, conj u] :=
  DiazModulus.candidate_one_self_conj_linearIndependent_aux h
