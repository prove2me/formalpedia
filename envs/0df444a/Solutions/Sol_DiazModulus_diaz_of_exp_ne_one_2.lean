-- Prove2me | solution 2 for DiazModulus.diaz_of_exp_ne_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T05:32:06.045329+00:00
-- url     : https://prove2.me/submissions/61a82beb-f548-4111-984a-0b0181ed693b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Graph repair B — an alternative reduction of `DiazModulus.diaz_of_exp_ne_one`
(`9182eef2-1c37-4982-859b-566c87120292`, Open).

Children:
  * `DiazModulus.diaz_of_exp_real_generic`  (already in the subgraph, Open leaf — untouched)
  * `DiazModulus.candidate_exp_angularTriple_transcendental`  (Proved, currently unlinked)

The point of the reduction is the `u.re = 0` branch.  On the imaginary axis `conj u = -u`,
so the angular exponent degenerates: `u² / conj u = -u`.  The angular node then says
`exp (-u) = (exp u)⁻¹` is transcendental, which contradicts `exp u` algebraic because `Q̄`
is a field.  So no candidate lies on the imaginary axis.

The angular node is genuinely consumed: it is the only thing in the file that rules out an
imaginary-axis candidate.
-/
import Theorems.Thm_DiazModulus_diaz_of_exp_real_generic
import Theorems.Thm_DiazModulus_candidate_exp_angularTriple_transcendental

open Complex ComplexConjugate

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im ≠ 0 → Complex.exp u ≠ 1 → Transcendental ℚ (Complex.exp u) := by
  intro u hu hmod hexp him hne
  by_cases hre : u.re = 0
  · intro halg
    have hc : IsCandidate u := ⟨hu, hmod, halg⟩
    have hT := candidate_exp_angularTriple_transcendental hc
    have hconj : conj u = -u := by
      apply Complex.ext <;> simp [hre]
    have hval : u ^ 2 / conj u = -u := by
      rw [hconj, div_neg, pow_two, mul_div_assoc, div_self hu, mul_one]
    rw [hval, Complex.exp_neg] at hT
    exact hT (mem_Qbar_iff.mp (inv_mem (mem_Qbar_iff.mpr halg)))
  · exact diaz_of_exp_real_generic u hu hmod hexp him hne hre
