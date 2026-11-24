-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.Et_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:26.404854+00:00
-- url     : https://prove2.me/submissions/2ac237ce-0df9-43e1-bec2-3e220730078b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regularised_pairing_continuous_in_t
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_gamma_product_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Et_eq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_Et_zero__544253459110
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_gamma_product_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_mul_of_vanishing_outside_box

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
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (p : SS k r) : Continuous (fun t : ℝ × ℝ => Et D F F' (p, t)) := by
  by_cases hp : D.inSS p
  · have e : (fun t : ℝ × ℝ => Et D F F' (p, t)) = fun t => Ef D F F' p t := funext (Et_eq D F F' hp)
    rw [e]
    unfold Ef
    refine continuous_finsetSum _ fun m hm => continuous_finsetSum _ fun l hl => ?_
    have hm' : m ≤ 2 := by have := Finset.mem_range.1 hm; omega
    have hl' : l ≤ 2 := by have := Finset.mem_range.1 hl; omega
    refine continuous_mul_of_vanishing_outside_box (cutoff_gamma_product_continuous D m l) (fun t ht => ?_)
      (regularised_pairing_continuous_in_t H (admissibleWeight_mono hF hl' hm') (admissibleWeight_mono hF' hl' hm') hp)
    rw [cutoff_gamma_product_zero D m l ht]; simp
  · have e : (fun t : ℝ × ℝ => Et D F F' (p, t)) = fun _ => 0 := funext (Et_zero' D F F' hp)
    rw [e]
    exact continuous_const
end Formalism.FourierDecayAlt.P.B6
