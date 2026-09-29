-- Prove2me | solution 3 for EulerMascheroni.irrational_gamma_or_gompertz
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-14T20:03:59.590448+00:00
-- url     : https://prove2.me/submissions/3072d54d-5ae0-4eab-9877-b1b1899e430c

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
