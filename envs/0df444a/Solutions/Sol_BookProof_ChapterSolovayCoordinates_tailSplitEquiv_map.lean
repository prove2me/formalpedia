-- Prove2me | solution 1 for BookProof.ChapterSolovayCoordinates.tailSplitEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T16:00:31.262485+00:00
-- url     : https://prove2.me/submissions/952a9353-5c7e-4759-9f61-4cc9efac0a57

-- Generated from ChapterSolovayCoordinates.lean — solution of BookProof.ChapterSolovayCoordinates.tailSplitEquiv_map
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
import Theorems.Thm_BookProof_ChapterSolovayCoordinates_infinitePi_map_sumPiEquivProdPi
open BookProof.ChapterSolovayCoordinates



open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) :
    Measure.map (tailSplitEquiv k) coordinateTailMeasure =
      (gaussianHead k).prod coordinateTailMeasure := by

  dsimp [coordinateTailMeasure, gaussianHead, standardGaussian, tailSplitEquiv,
      PhysHSGaussian.gammaMeasure]
  have h_reindex : Measure.map
      ((MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) (finSumNatEquiv k)).symm)
      (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) =
      Measure.infinitePi (fun _ : Fin k ⊕ ℕ => gaussianReal 0 1) := by
    have h := Measure.infinitePi_map_piCongrLeft
      (fun _ : Fin k ⊕ ℕ => gaussianReal 0 1) (finSumNatEquiv k).symm
    have h_eq : ((MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ)
      (finSumNatEquiv k)).symm : (ℕ → ℝ) → (Fin k ⊕ ℕ → ℝ)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ ℕ => ℝ)
      (finSumNatEquiv k).symm : (ℕ → ℝ) → (Fin k ⊕ ℕ → ℝ)) := by
      ext f x
      simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.coe_mk,
        Equiv.piCongrLeft_apply]
    simpa [h_eq] using h
  have h_split : Measure.map
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ ℕ => ℝ))
      (Measure.infinitePi (fun _ : Fin k ⊕ ℕ => gaussianReal 0 1)) =
      (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) := by
    exact infinitePi_map_sumPiEquivProdPi (fun _ : Fin k ⊕ ℕ => gaussianReal 0 1)
  calc
    Measure.map
      ((MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) (finSumNatEquiv k)).symm.trans
        (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin k ⊕ ℕ => ℝ))
      (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
        = Measure.map
          (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin k ⊕ ℕ => ℝ)
          (Measure.map
            ((MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) (finSumNatEquiv k)).symm)
            (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))) := by
      simpa [MeasurableEquiv.coe_trans] using
        (Measure.map_map
          (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ ℕ => ℝ)).measurable
          ((MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) (finSumNatEquiv k)).symm.measurable)).symm
    _ = Measure.map
          (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin k ⊕ ℕ => ℝ)
          (Measure.infinitePi (fun _ : Fin k ⊕ ℕ => gaussianReal 0 1)) := by rw [h_reindex]
    _ = (Measure.pi fun _ : Fin k => gaussianReal 0 1).prod
          (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) := by rw [h_split]
    _ = (gaussianHead k).prod coordinateTailMeasure := rfl
