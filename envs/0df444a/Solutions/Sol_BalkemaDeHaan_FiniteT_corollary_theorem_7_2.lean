-- Prove2me | solution 2 for BalkemaDeHaan.FiniteT.corollary_theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:16.209281+00:00
-- url     : https://prove2.me/submissions/a6448432-f242-4044-a40e-66d1cf1a21f2

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife
import Theorems.Thm_BalkemaDeHaan_FiniteT_pi0_lipschitz
import Theorems.Thm_BalkemaDeHaan_FiniteT_theorem_7

-- carved verbatim out of submission ab212d39-d03c-4567-a3ee-8be9d1f0e21b, lines 658-664

section
open MeasureTheory ProbabilityTheory
open BalkemaDeHaan
open BalkemaDeHaan.FiniteT

theorem corollary_theorem_7_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ)
    (f f' a' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f')
    (ha' : ∀ t ≥ t₀, HasDerivWithinAt (normA μ f) (a' t) (Set.Ici t₀) t)
    (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hclose : ∀ t ≥ t₀, |c - a' t| ≤ ε) :
    ∀ t ≥ t₀, ∀ x : ℝ,
      |pi0 c x - BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t)| ≤ ε := by
  intro t ht x
  have hbounds : ∀ t ≥ t₀, c - ε ≤ a' t ∧ a' t ≤ c + ε := by
    intro t ht
    have := abs_le.mp (hclose t ht)
    constructor <;> linarith
  obtain ⟨h1, h2⟩ := BalkemaDeHaan.FiniteT.theorem_7 μ t₀ f f' a' hdens ha' (c - ε) (c + ε) hbounds t ht x
  have hl1 := BalkemaDeHaan.FiniteT.pi0_lipschitz c hc (c + ε) x
  have hl2 := BalkemaDeHaan.FiniteT.pi0_lipschitz c hc (c - ε) x
  rw [show c - (c + ε) = -ε by ring, abs_neg, abs_of_nonneg hε] at hl1
  rw [show c - (c - ε) = ε by ring, abs_of_nonneg hε] at hl2
  have hl1' := abs_le.mp hl1
  have hl2' := abs_le.mp hl2
  rw [abs_le]
  constructor <;> linarith

end

section
open MeasureTheory ProbabilityTheory
open BalkemaDeHaan.FiniteT

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' a' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f')
    (ha' : ∀ t ≥ t₀, HasDerivWithinAt (normA μ f) (a' t) (Set.Ici t₀) t)
    (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hclose : ∀ t ≥ t₀, |c - a' t| ≤ ε) :
    ∀ t ≥ t₀, ∀ x : ℝ, |pi0 c x - BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t)| ≤ ε := by
  exact corollary_theorem_7_core μ t₀ f f' a' hdens ha' c ε hc hε hclose

end
