-- Prove2me | solution 1 for BookProof.ChapterPvmFibreInducedSystem.homEmb_proj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:43.455033+00:00
-- url     : https://prove2.me/submissions/e5764996-4bbf-493d-b113-6eb529032676

-- Generated from ChapterPvmFibreInducedSystem.lean — solution of BookProof.ChapterPvmFibreInducedSystem.homEmb_proj
import Mathlib
import Definitions.Def_ChapterPvmFibreInducedSystem
import Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_lpCongr_symm_proj
import Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_homEmb_apply
import Definitions.Def_ChapterPvmMeasure
import Definitions.Def_ChapterPvmCyclicUnitary
import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterPvmInducedSystem
import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterL2FibreSum
import Definitions.Def_ChapterHilbertSumIntertwine
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterPvmFibreInducedSystem



open MeasureTheory
open scoped InnerProductSpace


open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicUnitary
open BookProof.ChapterPvmCyclicDecomposition BookProof.ChapterPvmInducedSystem
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterL2FibreSum
open BookProof.ChapterHilbertSumIntertwine
open BookProof.ChapterElectroweakFieldStrength

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Pvm X H} {S : Set H} {μ : Measure X}

set_option maxHeartbeats 1000000 in
theorem solution (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) {E : Set X}
    (hE : MeasurableSet E) (f : Lp ℂ 2 μ) :
    homEmb hmu ψ (proj μ hE f) = P.p E (homEmb hmu ψ f) := by

  rw [homEmb_apply, homEmb_apply, lpCongr_symm_proj (hmu ψ) hE f]
  exact swCLM_proj P (ψ : H) hE _
