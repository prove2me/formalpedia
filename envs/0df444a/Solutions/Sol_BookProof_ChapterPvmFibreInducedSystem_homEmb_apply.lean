-- Prove2me | solution 1 for BookProof.ChapterPvmFibreInducedSystem.homEmb_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T20:57:01.655019+00:00
-- url     : https://prove2.me/submissions/f6bc50d6-3501-44a1-9cb1-6790b8f5d76c

-- Generated from ChapterPvmFibreInducedSystem.lean — solution of BookProof.ChapterPvmFibreInducedSystem.homEmb_apply
import Mathlib
import Definitions.Def_ChapterPvmFibreInducedSystem
import Definitions.Def_ChapterPvmMeasure
import Definitions.Def_ChapterPvmCyclicUnitary
import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterPvmInducedSystem
import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterL2FibreSum
import Definitions.Def_ChapterHilbertSumIntertwine
open BookProof.ChapterPvmFibreInducedSystem



open MeasureTheory
open scoped InnerProductSpace


open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicUnitary
open BookProof.ChapterPvmCyclicDecomposition BookProof.ChapterPvmInducedSystem
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterL2FibreSum
open BookProof.ChapterHilbertSumIntertwine

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Pvm X H} {S : Set H} {μ : Measure X}

set_option maxHeartbeats 1000000 in
theorem solution (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) (f : Lp ℂ 2 μ) :
    homEmb hmu ψ f = swIsom P (ψ : H) ((lpCongr (hmu ψ)).symm f) := rfl
