-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.out_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:55.131455+00:00
-- url     : https://prove2.me/submissions/2035a271-c1ea-490f-8308-e7dd254f1e44

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.AveragedKernelSums
theorem _root_.solution (z : K) : Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z ∈ R := by
  have h1 : ((Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) : K) : K ⧸ R.toAddSubgroup) =
      (z : K ⧸ R.toAddSubgroup) := QuotientAddGroup.out_eq' _
  have h3 := R.toAddSubgroup.neg_mem (QuotientAddGroup.eq.mp h1)
  have e : -(-(Quotient.out ((z : K) : K ⧸ R.toAddSubgroup)) + z) =
      Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z := by ring
  rw [e] at h3; exact h3
end Formalism.FourierDecayAlt.P.AveragedKernelSums
