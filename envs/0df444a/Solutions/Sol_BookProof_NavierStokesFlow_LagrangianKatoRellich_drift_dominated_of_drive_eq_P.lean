-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianKatoRellich.drift_dominated_of_drive_eq_P
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:53:15.197482+00:00
-- url     : https://prove2.me/submissions/d5c078f3-4634-4f00-b662-04141314908e

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — solution of BookProof.NavierStokesFlow.LagrangianKatoRellich.drift_dominated_of_drive_eq_P
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
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
theorem solution (hdrive : L.drive = L.P) (v : L.D) :
    ‖(L.drift v : F)‖
      ≤ (∑ i : Fin 3, |L.force i|) * (∑ j : Fin 3, ‖(L.P j v : F)‖) + 0 * ‖(v : F)‖ := by

  have hdriftsum : (L.drift v : F) = ∑ i : Fin 3, ((L.force i : ℝ) : ℂ) • (L.P i v : F) := by
    simp only [LagrangianFullData.drift, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul, hdrive]
  have hterms : ‖(L.drift v : F)‖ ≤ ∑ i : Fin 3, |L.force i| * ‖(L.P i v : F)‖ := by
    rw [hdriftsum]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_smul]
    simp
  have hle : ∀ i : Fin 3, |L.force i| * ‖(L.P i v : F)‖
      ≤ |L.force i| * (∑ j : Fin 3, ‖(L.P j v : F)‖) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact Finset.single_le_sum (f := fun j : Fin 3 => ‖(L.P j v : F)‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  calc ‖(L.drift v : F)‖ ≤ ∑ i : Fin 3, |L.force i| * ‖(L.P i v : F)‖ := hterms
    _ ≤ ∑ i : Fin 3, |L.force i| * (∑ j : Fin 3, ‖(L.P j v : F)‖) :=
        Finset.sum_le_sum fun i _ => hle i
    _ = (∑ i : Fin 3, |L.force i|) * (∑ j : Fin 3, ‖(L.P j v : F)‖) := by
        rw [Finset.sum_mul]
    _ = (∑ i : Fin 3, |L.force i|) * (∑ j : Fin 3, ‖(L.P j v : F)‖) + 0 * ‖(v : F)‖ := by ring
