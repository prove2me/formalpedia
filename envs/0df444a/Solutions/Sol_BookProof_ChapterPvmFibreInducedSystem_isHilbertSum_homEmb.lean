-- Prove2me | solution 1 for BookProof.ChapterPvmFibreInducedSystem.isHilbertSum_homEmb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:44.694541+00:00
-- url     : https://prove2.me/submissions/377b356f-00f4-48de-939e-3021f08b3bb4

-- Generated from ChapterPvmFibreInducedSystem.lean — solution of BookProof.ChapterPvmFibreInducedSystem.isHilbertSum_homEmb
import Mathlib
import Definitions.Def_ChapterPvmFibreInducedSystem
import Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_homEmb_apply
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
theorem solution (hS : OrthCyclicFamily P S)
    (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H))
    (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) :
    IsHilbertSum ℂ (fun _ : S => Lp ℂ 2 μ) (homEmb hmu) := by

  refine IsHilbertSum.mk ?_ ?_
  · intro x y hxy u v
    exact inner_swIsom_eq_zero
      (hS.orth (x : H) x.2 (y : H) y.2 (Subtype.coe_injective.ne hxy)) _ _
  · have hsub : Submodule.span ℂ (familyOrbit P S)
        ≤ ⨆ ψ : S, LinearMap.range (homEmb hmu ψ).toLinearMap := by
      rw [Submodule.span_le]
      rintro v hv
      obtain ⟨ψ, hψ, hv⟩ := Set.mem_iUnion₂.mp hv
      obtain ⟨E, hE, rfl⟩ := hv
      refine Submodule.mem_iSup_of_mem ⟨ψ, hψ⟩ ?_
      refine ⟨lpCongr (hmu ⟨ψ, hψ⟩)
        (indicatorConstLp 2 hE (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ)), ?_⟩
      change homEmb hmu ⟨ψ, hψ⟩ _ = _
      rw [homEmb_apply, LinearIsometryEquiv.symm_apply_apply]
      exact swCLM_indicator P ψ hE
    intro v _
    have hv : v ∈ closure ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H) :=
      hdense v
    have hmono := closure_mono (fun w hw => hsub hw) hv
    rwa [← Submodule.topologicalClosure_coe] at hmono
