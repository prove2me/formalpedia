-- Prove2me | solution 1 for BookProof.ChapterPvmFibreInducedSystem.induced_system_of_isHilbertSum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:55:22.92799+00:00
-- url     : https://prove2.me/submissions/8fdb6fa8-b0a1-472e-b216-3ea0fc4d308a

import Definitions.Def_ChapterPvmMeasure
import Definitions.Def_ChapterPvmCyclicUnitary
import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterPvmInducedSystem
import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterL2FibreSum
import Definitions.Def_ChapterHilbertSumIntertwine
import Mathlib
import Definitions.Def_ChapterPvmFibreInducedSystem
import Definitions.Def_ChapterElectroweakFieldStrength
import Theorems.Thm_BookProof_ChapterHilbertSumIntertwine_linearIsometryEquiv_intertwine
-- Generated from ChapterPvmFibreInducedSystem.lean — theorem BookProof.ChapterPvmFibreInducedSystem.induced_system_of_isHilbertSum
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterPvmFibreInducedSystem


open MeasureTheory
open scoped InnerProductSpace


open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicUnitary
open BookProof.ChapterPvmCyclicDecomposition BookProof.ChapterPvmInducedSystem
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterL2FibreSum
open BookProof.ChapterHilbertSumIntertwine

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


theorem solution {ι : Type*} [Countable ι]
    (P : Pvm X H) (μ : Measure X) (V : ∀ _ : ι, Lp ℂ 2 μ →ₗᵢ[ℂ] H)
    (hsum : IsHilbertSum ℂ (fun _ : ι => Lp ℂ 2 μ) V)
    (hint : ∀ (i : ι) (E : Set X) (hE : MeasurableSet E) (f : Lp ℂ 2 μ),
      V i (proj μ hE f) = P.p E (V i f)) :
    ∃ W : H ≃ₗᵢ[ℂ] Lp (Fibre ι) 2 μ,
      ∀ (E : Set X) (hE : MeasurableSet E) (v : H), W (P.p E v) = proj μ hE (W v) := by
  classical
  refine ⟨hsum.linearIsometryEquiv.trans (BookProof.ChapterL2FibreSum.fibreEquiv μ).symm, ?_⟩
  intro E hE v
  apply (BookProof.ChapterL2FibreSum.fibreEquiv (ι := ι) μ).injective
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
  refine lp.ext (funext fun i => ?_)
  rw [BookProof.ChapterL2FibreSum.fibreEquiv_proj, LinearIsometryEquiv.apply_symm_apply]
  exact BookProof.ChapterHilbertSumIntertwine.linearIsometryEquiv_intertwine hsum (P.p E)
    (fun _ => BookProof.ChapterL2FibreSum.projCLM μ hE)
    (fun _ u => BookProof.ChapterL2FibreSum.norm_proj_le μ hE u)
    (fun i f => hint i E hE f) v i

