-- Prove2me | solution 1 for BirkhoffGlobalSection.antipodal_quotient_dynamics_continuous
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T09:01:46.227449+00:00
-- url     : https://prove2.me/submissions/fa6cbabb-47b3-453a-9eb5-648a8d325697

import Mathlib
import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Topology.CompactOpen
set_option autoImplicit false
open BirkhoffGlobalSection

theorem solution {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (hinv : IsAntipodallyInvariantComponent μ c)
    (hfree : IsAntipodallyFreeComponent μ c) :
    IsContinuousQuotientDynamics φ hanti := by
  letI : Setoid (LeftEnergyState μ c) := antipodalSetoid μ c
  refine ⟨?_, ?_, ?_⟩
  · have hq : Topology.IsQuotientMap
        (@Quotient.mk' (LeftEnergyState μ c) (antipodalSetoid μ c)) :=
      isQuotientMap_quotient_mk'
    apply hq.continuous_lift_prod_right
    change Continuous (fun p : ℝ × LeftEnergyState μ c =>
      (Quotient.mk' (φ p.1 p.2) : AntipodalQuotientState μ c))
    exact continuous_quotient_mk'.comp (φ.continuous continuous_fst continuous_snd)
  · intro x
    induction x using Quotient.inductionOn with
    | h s =>
      change (Quotient.mk' (φ 0 s) : AntipodalQuotientState μ c) = Quotient.mk' s
      rw [Flow.map_zero_apply]
  · intro t₁ t₂ x
    induction x using Quotient.inductionOn with
    | h s =>
      change (Quotient.mk' (φ (t₁ + t₂) s) : AntipodalQuotientState μ c) =
        Quotient.mk' (φ t₁ (φ t₂ s))
      rw [Flow.map_add]
#print axioms solution
