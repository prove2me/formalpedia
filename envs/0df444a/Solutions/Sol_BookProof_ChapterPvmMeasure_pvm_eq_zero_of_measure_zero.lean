-- Prove2me | solution 1 for BookProof.ChapterPvmMeasure.pvm_eq_zero_of_measure_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:21:39.292522+00:00
-- url     : https://prove2.me/submissions/b7add856-4c95-4e91-8801-cc5f68e96f7f

-- Generated from ChapterPvmMeasure.lean — solution of BookProof.ChapterPvmMeasure.pvm_eq_zero_of_measure_zero
import Mathlib
import Definitions.Def_ChapterPvmMeasure
import Theorems.Thm_BookProof_ChapterPvmMeasure_pvmMeasure_eq_zero_iff
open BookProof.ChapterPvmMeasure



open MeasureTheory
open scoped InnerProductSpace


variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (P : Pvm X H)
variable (P : Pvm X H) (ψ : H)

set_option maxHeartbeats 1000000 in
theorem solution (hcyc : IsCyclic P ψ) {E : Set X} (hE : MeasurableSet E)
    (h0 : pvmMeasure P ψ E = 0) : P.p E = 0 := by

  have hEψ : P.p E ψ = 0 := (pvmMeasure_eq_zero_iff P ψ hE).mp h0
  -- the projection kills the generating vectors
  have hgen : ∀ v ∈ pvmOrbit P ψ, P.p E v = 0 := by
    rintro _ ⟨F, hF, rfl⟩
    have hEF : pvmMeasure P ψ (E ∩ F) = 0 :=
      measure_mono_null Set.inter_subset_left h0
    have := (pvmMeasure_eq_zero_iff P ψ (hE.inter hF)).mp hEF
    rw [P.inter hE hF ψ]
    exact this
  -- hence the whole closed span
  have hspan : ∀ v ∈ (Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H), P.p E v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul c x _ hx => simp [map_smul, hx]
  have hclosed : IsClosed {v : H | P.p E v = 0} := isClosed_eq (P.p E).continuous continuous_const
  have hsub : ((Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H) : Set H)
      ⊆ {v : H | P.p E v = 0} := hspan
  ext v
  have hv : v ∈ closure ((Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H) : Set H) := by
    rw [hcyc.closure_eq]; trivial
  have := (closure_minimal hsub hclosed) hv
  simpa using this
