-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.prod_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:26:02.519725+00:00
-- url     : https://prove2.me/submissions/b54deccb-e10f-4777-80a8-56fef29800b4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMemMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L1QuotientIntegralBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  obtain ⟨hWs, -, hWc, -⟩ := hW
  obtain ⟨hNs, -, hNc, -⟩ := hN
  have := hWs; have := hNs
  rw [ae_iff]
  have hsub : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r |
      ¬ (Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r)} ⊆
      ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) ∪
        (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) := by
    intro p hp
    by_cases h1 : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z
    · exact Or.inr ⟨Set.mem_univ _, fun h2 => hp ⟨h1, h2⟩⟩
    · exact Or.inl ⟨h1, Set.mem_univ _⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hWc, zero_mul]
  · rw [Measure.prod_prod, hNc, mul_zero]
end Formalism.FourierDecayAlt.P.S3dx4
