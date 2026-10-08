-- Prove2me | solution 1 for ConvexRiskFn.Order.condExp_icx_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T05:06:35.826392+00:00
-- url     : https://prove2.me/submissions/79e5b352-0257-420d-9e5d-ded601d75be0

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_ConvexRiskFn_Order_Setting
open MeasureTheory

theorem solution {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P] (p : ENNReal) (hp1 : 1 ≤ p)
    (X : Ω → ℝ) (hX : MemLp X p P) :
    MemLp (P[X|m]) p P ∧ StochasticOrders.MonotoneConvex.IcxOrder P P (P[X|m]) X := by
  refine ⟨MemLp.condExp hp1 hX, ?_⟩
  intro φ _ hφ hleft hright
  have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have hJ := hφ.map_condExp_le_univ hm hc.lowerSemicontinuous (hX.integrable hp1) hright
  calc
    (∫ ω, φ (P[X|m] ω) ∂P) ≤ ∫ ω, P[φ ∘ X|m] ω ∂P :=
      integral_mono_ae hleft integrable_condExp hJ
    _ = ∫ ω, φ (X ω) ∂P := integral_condExp hm

#print axioms solution

open MeasureTheory
namespace ConvexRiskFn.Order

/-- Proof of Theorem 5.1, p. 446: by Jensen's inequality `𝔼[X | 𝒢] ⪯_icx X` for every σ-algebra
`𝒢 ⊂ ℱ`; together with the standing assumption of §5.1 (p. 443) that `𝔼[X | 𝒢] ∈ 𝒳`. -/
example {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P] (p : ENNReal) (hp1 : 1 ≤ p)
    (X : Ω → ℝ) (hX : MemLp X p P) :
    MemLp (P[X|m]) p P ∧ StochasticOrders.MonotoneConvex.IcxOrder P P (P[X|m]) X := by
  exact solution m hm P p hp1 X hX

end ConvexRiskFn.Order

#print axioms solution
