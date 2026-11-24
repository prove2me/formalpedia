-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.Gt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:22:37.909802+00:00
-- url     : https://prove2.me/submissions/b39aeaeb-9c28-4c10-83ae-f27558c9a2b5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_wt_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Et_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Et_bound

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
theorem _root_.solution (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ),
    AdmW α c 2 2 F → AdmW α c' 2 2 F' → ∀ τ p, ‖Gt D F F' τ p‖ ≤ wt D τ p * (K * c * c' * XX Ξ p) := by
  obtain ⟨K, hK, hb⟩ := Et_bound H
  have hBc : IsCompact (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) := isCompact_Icc.prod isCompact_Icc
  have hBm : MeasurableSet (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) := hBc.isClosed.measurableSet
  refine ⟨K * (volume.real (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2)), by positivity, ?_⟩
  intro F F' c c' hF hF' τ p
  unfold Gt
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_nonneg D τ p)]
  refine mul_le_mul_of_nonneg_left ?_ (wt_nonneg D τ p)
  have key : ∀ t : ℝ × ℝ, ‖Et D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))‖ ≤
      (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2).indicator (fun _ => K * c * c' * XX Ξ p) t := by
    intro t
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    by_cases ht : t ∈ Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2
    · rw [Set.indicator_of_mem ht]; exact hb F F' c c' hF hF' p t
    · rw [Set.indicator_of_notMem ht, Et_zero D F F' p
        (fun h => ht ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2.le⟩⟩), norm_zero]
  have hint : Integrable ((Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2).indicator
      (fun _ : ℝ × ℝ => K * c * c' * XX Ξ p)) volume :=
    (integrable_indicator_iff hBm).2 (continuousOn_const.integrableOn_compact hBc)
  calc _ ≤ ∫ t, (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2).indicator
        (fun _ : ℝ × ℝ => K * c * c' * XX Ξ p) t := norm_integral_le_of_norm_le hint (ae_of_all _ key)
    _ = _ := by
      rw [integral_indicator hBm, setIntegral_const, smul_eq_mul]
      ring
end Formalism.FourierDecayAlt.P.B6
