-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanNormSquaredBound.sum_sum_sum_sum_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:05.065127+00:00
-- url     : https://prove2.me/submissions/68046e2f-4e74-4c1a-93e8-d5460fc0505e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanNormSquaredBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.MeanNormSquaredBound
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.MeanNormSquaredBound
theorem _root_.solution {α β M : Type} [AddCommMonoid M] (P : Finset α) (H : Finset β)
    (f : α → α → β → β → M) :
    ∑ p ∈ P, ∑ p' ∈ P, ∑ h ∈ H, ∑ h' ∈ H, f p p' h h' =
      ∑ h ∈ H, ∑ h' ∈ H, ∑ p ∈ P, ∑ p' ∈ P, f p p' h h' := by
  calc ∑ p ∈ P, ∑ p' ∈ P, ∑ h ∈ H, ∑ h' ∈ H, f p p' h h'
      = ∑ p ∈ P, ∑ h ∈ H, ∑ p' ∈ P, ∑ h' ∈ H, f p p' h h' :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ h ∈ H, ∑ p ∈ P, ∑ p' ∈ P, ∑ h' ∈ H, f p p' h h' := Finset.sum_comm
    _ = ∑ h ∈ H, ∑ p ∈ P, ∑ h' ∈ H, ∑ p' ∈ P, f p p' h h' :=
        Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ h ∈ H, ∑ h' ∈ H, ∑ p ∈ P, ∑ p' ∈ P, f p p' h h' :=
        Finset.sum_congr rfl fun h _ => Finset.sum_comm
end Formalism.FourierDecayAlt.P.MeanNormSquaredBound
