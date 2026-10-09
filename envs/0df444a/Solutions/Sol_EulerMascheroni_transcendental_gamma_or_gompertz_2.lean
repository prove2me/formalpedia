-- Prove2me | solution 2 for EulerMascheroni.transcendental_gamma_or_gompertz
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-09T02:29:05.547125+00:00
-- url     : https://prove2.me/submissions/d2ea50b3-d3dd-4b74-8a87-ed43e93285d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_eulerMascheroni_gompertz
import Definitions.Def_eulerMascheroni_mixedCover
import Theorems.Thm_EulerMascheroni_Mixed_hardy_identity
import Theorems.Thm_EulerMascheroni_Mixed_expEin_one_not_mem_exp_span

open Real

/-- Rivoal's disjunction from the algebraic non-membership `e·Ein(1) ∉ Q̄ + Q̄·e`.

If `γ` and `δ` were both algebraic, the Hardy identity `Ein(1) = γ + δ/e`, multiplied by `e`,
would exhibit `e·Ein(1) = δ + γ·e` as an element of the `Q̄`-span of `1` and `e`, contradicting
`expEin_one_not_mem_exp_span`. This is the exact algebraic analogue of the rational route that
proves `irrational_gamma_or_gompertz`, and it avoids the algebraic independence of `e` and
`e·Ein(1)` entirely. -/
theorem solution :
    Transcendental ℚ Real.eulerMascheroniConstant ∨
      Transcendental ℚ EulerMascheroni.gompertzConstant := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hγ, hδ⟩ := hcon
  -- `Transcendental ℚ x` is by definition `¬ IsAlgebraic ℚ x`.
  have hγ' : IsAlgebraic ℚ Real.eulerMascheroniConstant := by
    by_contra h; exact hγ h
  have hδ' : IsAlgebraic ℚ EulerMascheroni.gompertzConstant := by
    by_contra h; exact hδ h
  have hE : EulerMascheroni.Mixed.expEin 1
      = (EulerMascheroni.gompertzConstant : ℂ)
        + (Real.eulerMascheroniConstant : ℂ) * Complex.exp 1 := by
    unfold EulerMascheroni.Mixed.expEin
    rw [EulerMascheroni.Mixed.hardy_identity]
    field_simp [Complex.exp_ne_zero]
    ring
  exact EulerMascheroni.Mixed.expEin_one_not_mem_exp_span _ _ hδ' hγ' hE
