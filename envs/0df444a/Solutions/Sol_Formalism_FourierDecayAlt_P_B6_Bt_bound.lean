-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.Bt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:46.573528+00:00
-- url     : https://prove2.me/submissions/d47f2eb0-a37f-4a49-b8f8-3e1e6eff7841

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Wd_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Wd_tsupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_XX_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_QR_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regBracket_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_zero
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_Bt_zero__4cb6bf3235ab

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
    AdmW α c 2 2 F → AdmW α c' 2 2 F' → ∀ p t, ‖Bt D F F' (p, t)‖ ≤ K * c * c' * XX Ξ p := by
  obtain ⟨K, hK, hb⟩ := QR_bound H
  have hcs : HasCompactSupport (Wd D) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      ((Wd_tsupport D).trans Set.Ioo_subset_Icc_self)
  obtain ⟨C, hC⟩ := (Wd_contDiff D).continuous.bounded_above_of_compact_support hcs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C * C * K, by positivity, ?_⟩
  intro F F' c c' hF hF' p t
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hX := XX_nonneg Ξ p
  have nn : 0 ≤ K * c * c' * XX Ξ p := by positivity
  by_cases hp : D.inSS p
  · by_cases ht : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2
    · rw [Bt_eq D F F' hp, regBracket_eq, norm_mul, Complex.norm_real, norm_mul]
      have q := hb 0 0 F F' c c' (admissibleWeight_mono hF (by omega) (by omega))
        (admissibleWeight_mono hF' (by omega) (by omega)) p hp t.1
        ⟨ht.1.1.le, ht.1.2.le⟩ t.2 ⟨ht.2.1.le, ht.2.2.le⟩
      simp only [add_zero, pow_zero, one_mul] at q
      calc _ ≤ (C * C) * (K * c * c' * XX Ξ p) :=
            mul_le_mul (mul_le_mul (hC _) (hC _) (norm_nonneg _) hC0) q (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · rw [Bt_zero D F F' p ht, norm_zero]; positivity
  · rw [Bt_zero' D F F' hp, norm_zero]; positivity
end Formalism.FourierDecayAlt.P.B6
