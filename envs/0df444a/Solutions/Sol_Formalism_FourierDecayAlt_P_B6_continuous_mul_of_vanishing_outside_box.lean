-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.continuous_mul_of_vanishing_outside_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:40:55.009919+00:00
-- url     : https://prove2.me/submissions/a9448f6d-6908-48cd-894f-3e5eb89ca85f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_quadrant_is_open

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {u v : ℝ × ℝ → ℂ} (hu : Continuous u)
    (hz : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2 → u t = 0) (hv : ContinuousOn v Quad) :
    Continuous (fun t => u t * v t) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t ∈ Quad
  · exact hu.continuousAt.mul (hv.continuousAt (quadrant_is_open.mem_nhds ht))
  · have hB : IsClosed (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) := isClosed_Icc.prod isClosed_Icc
    have htB : t ∈ (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2)ᶜ := by
      intro h
      apply ht
      refine ⟨?_, ?_⟩
      · have := h.1.1
        show (0 : ℝ) < t.1
        linarith
      · have := h.2.1
        show (0 : ℝ) < t.2
        linarith
    have : (fun t => u t * v t) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [hB.isOpen_compl.mem_nhds htB] with s hs
      rw [hz s (fun h => hs ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2.le⟩⟩), zero_mul]
    exact continuousAt_const.congr this.symm
end Formalism.FourierDecayAlt.P.B6
