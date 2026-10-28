-- Prove2me | solution 2 for BalkemaDeHaan.DiscreteDomain.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T14:54:14.598557+00:00
-- url     : https://prove2.me/submissions/8069db0a-b0a6-420b-a506-261d650fff5a

import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw
import Theorems.Thm_BalkemaDeHaan_DiscreteDomain_tailEquiv_discrete_levels
import Theorems.Thm_BalkemaDeHaan_DiscreteDomain_levels_12b_12a
import Theorems.Thm_BalkemaDeHaan_DiscreteDomain_tailEquiv_mem_Dr
import Theorems.Thm_BalkemaDeHaan_DiscreteDomain_discrete_mem_Dr

set_option autoImplicit false
open MeasureTheory Filter Topology BalkemaDeHaan.DiscreteDomain

-- carved from submission b678504e-739e-488b-b18d-de13abf032ba, lines 1316-1332

/-- Theorem 5, p. 800 (PDF 9): for `p > 0` and `c ≥ 0`, `F ∈ D_r(Π_{p,c})` iff `F` is tail
equivalent to a discrete distribution function `F₀` whose jumps `t₀ < t₁ < ⋯ → ∞` satisfy
(12a) and (12b). -/
theorem solution (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    InDr μ (piPC p c) ↔
      ∃ ν₀ : Measure ℝ, IsProbabilityMeasure ν₀ ∧ ∃ t : ℕ → ℝ,
        IsDiscreteWithJumps ν₀ t ∧ GapRatio t p c ∧ TailRatio ν₀ t p ∧ TailEquiv μ ν₀ := by
  constructor
  · intro hμ
    obtain ⟨b, _, _, hb, ν₀, hprob, t, hdisc, hlev, heq⟩ :=
      tailEquiv_discrete_levels p c hp hc μ hμ
    haveI := hprob
    obtain ⟨h12b, h12a⟩ := levels_12b_12a p c hp hc μ hμ b hb ν₀ t hdisc hlev heq
    exact ⟨ν₀, hprob, t, hdisc, h12a, h12b, heq⟩
  · rintro ⟨ν₀, hprob, t, hdisc, h12a, h12b, heq⟩
    haveI := hprob
    exact tailEquiv_mem_Dr p c hp hc μ ν₀ heq (discrete_mem_Dr p c hp hc ν₀ t hdisc h12a h12b)
