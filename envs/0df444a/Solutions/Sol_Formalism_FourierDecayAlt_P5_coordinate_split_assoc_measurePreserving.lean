-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.coordinate_split_assoc_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:17.476744+00:00
-- url     : https://prove2.me/submissions/97ad19eb-65e6-46ec-b701-8583a4d86026

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
import Theorems.Thm_Formalism_FourierDecayAlt_P5_coordinate_split_measurePreserving


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (l : Fin r) {β : Type} [MeasurableSpace β] (ν : Measure β) [SFinite ν] :
    MeasurePreserving (coordinateSplitAssoc l (β := β)) (volume.prod ν) (volume.prod (volume.prod ν)) := by
  have h1 : MeasurePreserving (Prod.map (coordinateSplit l) (id : β → β)) (volume.prod ν)
      ((volume : Measure (ℂ × Cf r l.succ)).prod ν) :=
    (coordinate_split_measurePreserving l).prod (MeasurePreserving.id ν)
  exact (measurePreserving_prodAssoc volume volume ν).comp h1
end Formalism.FourierDecayAlt.P5
