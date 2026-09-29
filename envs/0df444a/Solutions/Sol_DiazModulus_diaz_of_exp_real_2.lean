-- Prove2me | solution 2 for DiazModulus.diaz_of_exp_real
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T05:30:32.719785+00:00
-- url     : https://prove2.me/submissions/3c68a103-efcb-4060-8250-b5976e72c83f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Graph repair A — an alternative reduction of `DiazModulus.diaz_of_exp_real`
(`c57418e5-9b00-4d3b-b481-7344ef1e207e`, Open).

Children:
  * `DiazModulus.diaz_of_exp_real_self_not_real`  (already in the subgraph, Open)
  * `DiazModulus.candidate_one_self_conj_linearIndependent`  (Proved, currently unlinked)

The point of the reduction is the `u.im = 0` branch.  The existing sketch closes it with
`diaz_of_exp_real_self_real`, which routes through `diaz_on_axes_of_hermite_lindemann`.
Here it is closed instead by the independence node: on the real axis `conj u = u`, so the
family `![1, u, conj u]` repeats its second and third entries and cannot be linearly
independent — while `candidate_one_self_conj_linearIndependent` says it is, for every
candidate.  So no candidate has `u.im = 0`.

The independence node is genuinely consumed: it is the only thing in the file that rules
out a real-axis candidate.
-/
import Theorems.Thm_DiazModulus_diaz_of_exp_real_self_not_real
import Theorems.Thm_DiazModulus_candidate_one_self_conj_linearIndependent

open Complex ComplexConjugate

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      Transcendental ℚ (Complex.exp u) := by
  intro u hu hmod hexp
  by_cases him : u.im = 0
  · intro halg
    have hc : IsCandidate u := ⟨hu, hmod, halg⟩
    have hind := candidate_one_self_conj_linearIndependent hc
    have hconj : conj u = u := Complex.conj_eq_iff_im.mpr him
    have hval : (![(1 : ℂ), u, conj u]) 1 = (![(1 : ℂ), u, conj u]) 2 := by
      simp [hconj]
    have : (1 : Fin 3) = 2 := hind.injective hval
    exact absurd this (by decide)
  · exact diaz_of_exp_real_self_not_real u hu hmod hexp him
