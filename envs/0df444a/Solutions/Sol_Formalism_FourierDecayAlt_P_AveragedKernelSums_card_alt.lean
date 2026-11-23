-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.card_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:54.815854+00:00
-- url     : https://prove2.me/submissions/6b0ac326-88c2-4230-a8c7-48d6f39040c9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_mem_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_relIndex_eq_card_map

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
theorem _root_.solution {P : AddSubgroup K} (hRP : R.toAddSubgroup ≤ P) :
    Nat.card {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ P} = R.toAddSubgroup.relIndex P := by
  rw [relIndex_eq_card_map]
  have : {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ P} =
      ((P.map (QuotientAddGroup.mk' R.toAddSubgroup) : AddSubgroup _) : Set _) := by
    ext x
    constructor
    · intro hx
      exact ⟨Quotient.out x, hx, QuotientAddGroup.out_eq' x⟩
    · rintro ⟨z, hz, rfl⟩
      exact (mem_out hRP z).2 hz
  rw [this]
  rfl
end Formalism.FourierDecayAlt.P.AveragedKernelSums
