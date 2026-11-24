-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.ae_Om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:28.133992+00:00
-- url     : https://prove2.me/submissions/4bd79c90-92a2-41e1-b771-9e177510e690

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
theorem _root_.solution (z z' : Vc k r) :
    ∀ᵐ ζ : ℂ, ζ ∈ Om k r z z' ∨ zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
  have hnull : (volume : Measure ℂ) (Metric.sphere (0 : ℂ) (Real.sqrt (Tz k r z * Tz k r z'))) = 0 :=
    Measure.addHaar_sphere volume _ _
  have hae : ∀ᵐ ζ : ℂ, ζ ∉ Metric.sphere (0 : ℂ) (Real.sqrt (Tz k r z * Tz k r z')) := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_mem_eq]
    exact hnull
  filter_upwards [hae] with ζ hζ
  by_cases h : ζ ∈ Om k r z z'
  · exact Or.inl h
  · right
    have h0 : ¬ (Tz k r z * Tz k r z' < Complex.normSq ζ) := h
    have h' : Complex.normSq ζ ≤ Tz k r z * Tz k r z' := not_lt.1 h0
    unfold zWeight
    rw [if_neg]
    intro hle
    apply hζ
    rw [mem_sphere_zero_iff_norm, ← le_antisymm h' hle, Complex.normSq_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)]
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
