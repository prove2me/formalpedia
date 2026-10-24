-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.contDiffAt_energyForm_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:52:08.50215+00:00
-- url     : https://prove2.me/submissions/a4768b64-62cb-4956-bc5d-982d477fb79b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.CoordinateTensor
variable {n r : ℕ}
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities.Analysis.CoordinateTensor in
/-- The energy form is `C²` near every `(A, T)` with `A` a unit. -/
theorem solution (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsUnit A)
    (T : (Fin r → Fin n) → ℝ) :
    ContDiffAt ℝ 2 (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
      FunctionalInequalities.Analysis.CoordinateTensor.energyForm q.1 q.2) (A, T) := by
  classical
  have hinv : ContDiffAt ℝ 2 Ring.inverse A := by
    simpa only [hA.unit_spec] using contDiffAt_ringInverse ℝ hA.unit
  have hcoord (J : Fin r → Fin n) :
      ContDiffAt ℝ 2
        (fun q :
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
            ((Fin r → Fin n) → ℝ) => q.2 J) (A, T) :=
    (ContinuousLinearMap.proj J :
      ((Fin r → Fin n) → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp
        (A, T) contDiffAt_snd
  unfold FunctionalInequalities.Analysis.CoordinateTensor.energyForm
  apply ContDiffAt.sum
  intro J _
  apply ContDiffAt.sum
  intro K _
  apply ContDiffAt.mul ((hcoord J).mul (hcoord K))
  apply contDiffAt_prod
  intro s _
  exact ContDiffAt.inner ℝ contDiffAt_const
    ((hinv.comp (A, T) contDiffAt_fst).clm_apply contDiffAt_const)
