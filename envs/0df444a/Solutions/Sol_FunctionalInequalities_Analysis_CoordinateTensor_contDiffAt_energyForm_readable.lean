-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.contDiffAt_energyForm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:44.291976+00:00
-- url     : https://prove2.me/submissions/05c6f18c-1ab2-4eed-969e-8959a6e324ed

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

noncomputable section
open Matrix
open scoped RealInnerProductSpace
variable {n r : ℕ}
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
