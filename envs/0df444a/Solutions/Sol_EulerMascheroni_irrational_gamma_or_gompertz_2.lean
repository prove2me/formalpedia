-- Prove2me | solution 2 for EulerMascheroni.irrational_gamma_or_gompertz
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-14T20:02:47.885964+00:00
-- url     : https://prove2.me/submissions/0a46695c-d6eb-407d-b812-36a85f7b248b

import Definitions.Def_eulerMascheroni_gompertz
import Definitions.Def_eulerMascheroni_mixedCover
import Theorems.Thm_EulerMascheroni_Mixed_hardy_identity
import Theorems.Thm_EulerMascheroni_Mixed_e_values_rat_linear_independent

open Real

/-- Aptekarev's disjunction from ℚ-linear independence of `1, e, e·Ein(1)`.
If both `γ = p` and `δ = r` were rational, the Hardy identity
`e·Ein(1) = e·γ + δ` would give the rational relation
`(-r) + (-p)·e + 1·(e·Ein(1)) = 0`, whose `Ein`-coefficient is `1 ≠ 0`. -/
theorem solution :
    Irrational Real.eulerMascheroniConstant ∨ Irrational EulerMascheroni.gompertzConstant := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hγ, hδ⟩ := hcon
  simp only [Irrational, not_not, Set.mem_range] at hγ hδ
  obtain ⟨p, hp⟩ := hγ
  obtain ⟨r, hr⟩ := hδ
  have hE : EulerMascheroni.Mixed.expEin 1 = (p : ℂ) * Complex.exp 1 + (r : ℂ) := by
    unfold EulerMascheroni.Mixed.expEin
    rw [EulerMascheroni.Mixed.hardy_identity, ← hp, ← hr]
    push_cast
    field_simp [Complex.exp_ne_zero]
  have hrel := EulerMascheroni.Mixed.e_values_rat_linear_independent (-r) (-p) 1
    (by push_cast; rw [hE]; ring)
  exact one_ne_zero hrel.2.2
