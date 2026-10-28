-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_jointSpace_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:49.795284+00:00
-- url     : https://prove2.me/submissions/ea082e3e-b4cb-4807-bbdb-9b6b8f4f8eb5

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Law
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_map_linearIsometryEquiv_readable
import Theorems.Thm_FunctionalInequalities_KLS_Isotropic_map_linearIsometryEquiv_readable

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Line
/-- `coordinateEquiv` sends standard basis vectors to standard basis vectors. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.coordinateEquiv_basisFun (N n : ℕ) (i : Option (Fin N × Fin n)) :
    coordinateEquiv N n (EuclideanSpace.basisFun _ ℝ i) =
      EuclideanSpace.basisFun (Fin (N * n + 1)) ℝ
        (Fintype.equivFinOfCardEq (card_option_prod N n) i) := by
  simp only [coordinateEquiv, EuclideanSpace.basisFun_apply, EuclideanSpace.piLpCongrLeft_single]
/-- Isotropy is preserved by the coordinate adapter. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.isotropic_map_coordinateEquiv {N n : ℕ} {ν : ProbabilityMeasure (JointSpace N n)}
    (hν : KLS.Isotropic ν) :
    KLS.Isotropic (ν.map (coordinateEquiv N n).continuous.measurable.aemeasurable) :=
  hν.map_linearIsometryEquiv_readable (coordinateEquiv N n)
/-- Log-concavity is preserved by the coordinate adapter. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_map_coordinateEquiv {N n : ℕ} {ν : ProbabilityMeasure (JointSpace N n)}
    (hν : KLS.LogConcave ν) :
    KLS.LogConcave (ν.map (coordinateEquiv N n).continuous.measurable.aemeasurable) := by
  let φ := coordinateEquiv N n
  apply KLS.LogConcave.of_affineIsometry_map hν
    (ν.map φ.continuous.measurable.aemeasurable) φ.symm.toLinearIsometry.toAffineIsometry
  change Measure.map φ.symm (Measure.map φ (ν : Measure (JointSpace N n))) = _
  rw [Measure.map_map φ.symm.continuous.measurable φ.continuous.measurable]
  simp only [Function.comp_def, φ.symm_apply_apply, Measure.map_id']
open FunctionalInequalities.Analysis.BakryEmery in
/-- **`CumulantBound` on the joint space**, through the coordinate adapter: for an isotropic
log-concave `ν` on `JointSpace N n`, `Σ_J κ^ν_{d+1}(u, e_{J 1}, …, e_{J d})² ≤ b |u|²`, the sum
running over the joint index set (`cumulant_map_linearIsometryEquiv` pulls the cumulants back,
`Equiv.sum_comp` reindexes the sum). -/
theorem solution {N n d : ℕ} {b : ℝ} (hb : FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d b)
    {ν : ProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)} (hiso : FunctionalInequalities.KLS.Isotropic ν) (hlc : FunctionalInequalities.KLS.LogConcave ν)
    (u : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n) :
    ∑ J : Fin d → Option (Fin N × Fin n),
      FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun _ ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2 := by
  classical
  let φ := FunctionalInequalities.KLS.LogConcave.Suspension.coordinateEquiv N n
  let e := Fintype.equivFinOfCardEq (FunctionalInequalities.KLS.LogConcave.Suspension.card_option_prod N n)
  have h := hb (N * n + 1) (ν.map φ.continuous.measurable.aemeasurable)
    (FunctionalInequalities.KLS.LogConcave.Suspension.isotropic_map_coordinateEquiv hiso) (FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_map_coordinateEquiv hlc) (φ u)
  rw [LinearIsometryEquiv.norm_map] at h
  refine le_trans (le_of_eq ?_) h
  rw [← (Equiv.piCongrRight fun _ : Fin d => e).sum_comp]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hmap : ((ν.map φ.continuous.measurable.aemeasurable : ProbabilityMeasure _) :
      Measure (EuclideanSpace ℝ (Fin (N * n + 1)))) = (ν : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).map φ := by
    simp [ProbabilityMeasure.toMeasure_map]
  rw [hmap]
  have hvec : (Fin.cons (φ u) fun k => EuclideanSpace.basisFun (Fin (N * n + 1)) ℝ
      ((Equiv.piCongrRight fun _ : Fin d => e) J k)) =
      fun i => φ ((Fin.cons u fun k => EuclideanSpace.basisFun _ ℝ (J k) : Fin (d + 1) → _) i) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · simp only [Fin.cons_succ, Equiv.piCongrRight_apply]
      exact (FunctionalInequalities.KLS.LogConcave.Suspension.coordinateEquiv_basisFun N n (J k)).symm
  rw [hvec, FunctionalInequalities.Analysis.BakryEmery.cumulant_map_linearIsometryEquiv_readable]
