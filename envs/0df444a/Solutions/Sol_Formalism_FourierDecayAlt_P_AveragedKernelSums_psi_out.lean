-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.psi_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:54.794472+00:00
-- url     : https://prove2.me/submissions/db19fa8a-28ae-44bc-8a35-6dffe260f84c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_out_sub_mem

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
theorem _root_.solution (hψ : ∀ r ∈ R, ψ r = 1) {c : K} (hc : c ∈ R) (z : K) :
    ψ (Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) * c) = ψ (z * c) := by
  have e : Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) * c =
      z * c + (Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z) * c := by ring
  rw [e, AddChar.map_add_eq_mul, hψ _ (R.mul_mem (out_sub_mem z) hc), mul_one]
end Formalism.FourierDecayAlt.P.AveragedKernelSums
