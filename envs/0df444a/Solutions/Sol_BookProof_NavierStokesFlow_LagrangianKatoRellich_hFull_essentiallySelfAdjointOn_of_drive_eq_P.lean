-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_essentiallySelfAdjointOn_of_drive_eq_P
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:21:36.72918+00:00
-- url     : https://prove2.me/submissions/236b5011-9fd3-4892-8b69-b0e45ec28e16

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — solution of BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_essentiallySelfAdjointOn_of_drive_eq_P
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_hFull_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_drift_dominated_of_drive_eq_P
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesLagrangianEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich

















open Filter Topology



open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace F] (hdrive : L.drive = L.P)
    {cc : ℝ} (hcc : 0 ≤ cc) (hC : ∀ v : L.D, ‖(L.constraintOp v : F)‖ ≤ cc * ‖(v : F)‖)
    (hT : EssentiallySelfAdjointOn L.D (L.D.subtype.comp (secondOrder L))) :
    EssentiallySelfAdjointOn L.D (lagrangianCore L) :=
  hFull_essentiallySelfAdjointOn L
      (Finset.sum_nonneg fun _ _ => abs_nonneg _) le_rfl hcc
      (drift_dominated_of_drive_eq_P L hdrive) hC hT
