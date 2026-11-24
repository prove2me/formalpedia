-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.gN_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:40:48.953787+00:00
-- url     : https://prove2.me/submissions/4f0e1cc7-10aa-4ace-b920-681f11ee73fb

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_sum_normSq_entries_nonneg
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := by
  apply Real.sqrt_pos.2
  by_contra hcon
  have h0 : hilbertSchmidtNormSq g = 0 := le_antisymm (not_lt.1 hcon) (sum_normSq_entries_nonneg g)
  have hz : g = 0 := by
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (g i j))).1 h0 i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (g i j))).1 h1 j (Finset.mem_univ _)
    simpa using Complex.normSq_eq_zero.1 h2
  have hu := WeylGroupFacts.isUnit_of_uh hg
  rw [hz, Matrix.det_zero] at hu
  exact not_isUnit_zero hu
end Formalism.FourierDecayAlt.P.B6
