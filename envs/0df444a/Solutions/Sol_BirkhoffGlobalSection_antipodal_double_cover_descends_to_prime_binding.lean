-- Prove2me | solution 1 for BirkhoffGlobalSection.antipodal_double_cover_descends_to_prime_binding
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T00:40:07.235229+00:00
-- url     : https://prove2.me/submissions/495869f5-9127-4178-b764-e5b46126b4ce

import Definitions.Def_BirkhoffGlobalSection
import Mathlib

open BirkhoffGlobalSection

theorem solution {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (hinv : IsAntipodallyInvariantComponent μ c)
    (hfree : IsAntipodallyFreeComponent μ c)
    (γ : PeriodicOrbit φ)
    (hdouble : IsAntipodalDoubleCover φ γ) :
    IsPrimeQuotientBinding φ hanti γ := by
  obtain ⟨hsimple, hhalf⟩ := hdouble
  have key : ∀ (t : ℝ) (s : LeftEnergyState μ c),
      quotientTimeMap φ hanti t (toAntipodalQuotient s)
        = toAntipodalQuotient ((φ t s : LeftEnergyState μ c)) := fun _ _ => rfl
  have hP : 0 < γ.period := γ.period_pos
  refine ⟨?_, ?_⟩
  · rw [key]
    have hsound :
        ((φ (γ.period / 2) γ.point : LeftEnergyState μ c) : Phase)
            = (γ.point : Phase) ∨
          ((φ (γ.period / 2) γ.point : LeftEnergyState μ c) : Phase)
            = -((γ.point : LeftEnergyState μ c) : Phase) := Or.inr hhalf
    exact Quotient.sound hsound
  · intro t ht0 hlt hcontra
    rw [key] at hcontra
    have hrel :
        ((φ t γ.point : LeftEnergyState μ c) : Phase) = (γ.point : Phase) ∨
          ((φ t γ.point : LeftEnergyState μ c) : Phase)
            = -((γ.point : LeftEnergyState μ c) : Phase) :=
      Quotient.exact hcontra
    rcases hrel with hc | hc
    · exact hsimple t ht0 (by linarith) (Subtype.ext hc)
    · have hstep :
          ((φ t (φ t γ.point) : LeftEnergyState μ c) : Phase)
            = -((φ t γ.point : LeftEnergyState μ c) : Phase) :=
        hanti t γ.point (φ t γ.point) hc
      have h2 : ((φ (t + t) γ.point : LeftEnergyState μ c) : Phase)
          = (γ.point : Phase) := by
        rw [φ.map_add, hstep, hc, neg_neg]
      exact hsimple (t + t) (by linarith) (by linarith) (Subtype.ext h2)
