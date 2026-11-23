-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.mem_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:22.25388+00:00
-- url     : https://prove2.me/submissions/0fb2e2c9-0abb-4cf1-afe9-b2fd35c8c128

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
theorem _root_.solution {P : AddSubgroup K} (hRP : R.toAddSubgroup ≤ P) (z : K) :
    Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) ∈ P ↔ z ∈ P := by
  have h : Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z ∈ P := hRP (out_sub_mem z)
  constructor
  · intro h1
    have := P.sub_mem h1 h
    rwa [sub_sub_cancel] at this
  · intro h1
    have := P.add_mem h h1
    rwa [sub_add_cancel] at this
end Formalism.FourierDecayAlt.P.AveragedKernelSums
