-- Prove2me | solution 2 for BookProof.ChapterPvmFibreInducedSystem.pvm_induced_system_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:56:21.925+00:00
-- url     : https://prove2.me/submissions/5018d12d-fed1-4bc1-8b9d-6a334e6db53e

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
import Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_isHilbertSum_homEmb
import Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_homEmb_proj
-- Generated from ChapterPvmFibreInducedSystem.lean — theorem BookProof.ChapterPvmFibreInducedSystem.pvm_induced_system_homogeneous
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

variable {P : Pvm X H} {S : Set H} {μ : Measure X}
theorem h44_induced {X : Type*} [MeasurableSpace X]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [Countable ι]
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

theorem solution [Countable S] (hS : OrthCyclicFamily P S)
    (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H))
    (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) :
    ∃ W : H ≃ₗᵢ[ℂ] Lp (Fibre S) 2 μ,
      ∀ (E : Set X) (hE : MeasurableSet E) (v : H), W (P.p E v) = proj μ hE (W v) := by
  exact h44_induced P μ (homEmb hmu)
    (BookProof.ChapterPvmFibreInducedSystem.isHilbertSum_homEmb hS hdense hmu)
    (fun ψ E hE f => BookProof.ChapterPvmFibreInducedSystem.homEmb_proj hmu ψ hE f)

