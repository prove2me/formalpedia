-- Prove2me | solution 1 for BookProof.ChapterPvmScalarMeasure.exists_induced_system_in_measure_class
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T07:50:29.630987+00:00
-- url     : https://prove2.me/submissions/f777d023-2546-44bb-8b56-2443cdcfaedd

-- Generated from ChapterPvmScalarMeasure.lean — solution of BookProof.ChapterPvmScalarMeasure.exists_induced_system_in_measure_class
import Mathlib
import Definitions.Def_ChapterPvmScalarMeasure
import Theorems.Thm_BookProof_ChapterPvmScalarMeasure_quasiInvariant_of_null_iff
import Definitions.Def_ChapterPvmMeasure
import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterMackeyConverse
import Definitions.Def_ChapterPvmInducedSystem
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterMackeyQuasiInvariant
open BookProof.ChapterPvmScalarMeasure



open MeasureTheory
open scoped InnerProductSpace


open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicDecomposition
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterMackeyConverse
open BookProof.ChapterPvmInducedSystem
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterMackeyQuasiInvariant

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G : Type*} [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (T : ContinuousImprimitivitySystem G X H) :
    ∃ (μ : Measure X) (S : Set H)
      (W : H ≃ₗᵢ[ℂ] lp (fun ψ : S => Lp ℂ 2 (pvmMeasure T.P (ψ : H))) 2),
      IsFiniteMeasure μ ∧ QuasiInvariant μ G ∧ S.Countable ∧
      (∀ ψ ∈ S, ‖ψ‖ = 1) ∧
      (∀ ψ : S, pvmMeasure T.P (ψ : H) ≪ μ) ∧
      (∀ (E : Set X) (hE : MeasurableSet E) (v : H) (ψ : S),
        W (T.P.p E v) ψ = proj (pvmMeasure T.P (ψ : H)) hE (W v ψ)) := by

  obtain ⟨S, hS, hdense⟩ := exists_orthCyclicFamily T.P
  haveI : Countable S := (countable_of_orthCyclicFamily hS).to_subtype
  obtain ⟨n, hn⟩ := Countable.exists_injective_nat S
  have hnull : ∀ E : Set X, MeasurableSet E → (scalarMeasure T.P S n E = 0 ↔ T.P.p E = 0) :=
    fun E hE => scalarMeasure_eq_zero_iff_p_eq_zero hdense hE
  refine ⟨scalarMeasure T.P S n, S, (isHilbertSum_swIsom hS hdense).linearIsometryEquiv,
    ⟨lt_of_le_of_lt (scalarMeasure_univ_le T.P hn hS.unit) (by norm_num)⟩,
    quasiInvariant_of_null_iff T hnull, countable_of_orthCyclicFamily hS, hS.unit,
    fun ψ => pvmMeasure_absolutelyContinuous T.P n ψ,
    fun E hE v ψ => linearIsometryEquiv_swIsom_pvm hS hdense hE v ψ⟩
