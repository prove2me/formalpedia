-- Prove2me | solution 1 for BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:40:42.069929+00:00
-- url     : https://prove2.me/submissions/bebc5c15-b48e-4163-bbe3-8472e13ce0f7

-- Generated from ChapterCompactCompleteReducibility.lean — solution of BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
import Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_avgOp_apply_mem
import Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_avgOp_apply_eq_self
import Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_avgOp_comm
open BookProof.ChapterCompactCompleteReducibility




open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution {ρ : G →* (V ≃L[ℂ] V)}
    (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (μ : Measure G) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] (W : Submodule ℂ V) (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) :
    ∃ W' : Submodule ℂ V, (∀ g : G, ∀ x ∈ W', ρ g x ∈ W') ∧ IsCompl W W' := by

  -- an arbitrary continuous projection onto `W`
  obtain ⟨W₀, hW₀⟩ := W.exists_isCompl
  set T₀ : V →ₗ[ℂ] V := W.subtype.comp (W.projectionOnto W₀ hW₀) with hT₀
  set T : V →L[ℂ] V := LinearMap.toContinuousLinearMap T₀ with hT
  have hTmem : ∀ v, T v ∈ W := by
    intro v
    exact (W.projectionOnto W₀ hW₀ v).2
  have hTid : ∀ w ∈ W, T w = w := by
    intro w hw
    have h2 : W.projectionOnto W₀ hW₀ w = ⟨w, hw⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hW₀ hw
    have hT₀w : T₀ w = w := by
      rw [hT₀, LinearMap.comp_apply, h2]
      rfl
    show T w = w
    exact hT₀w
  -- the averaged projection
  set p : V →L[ℂ] V := avgOp μ ρ T with hp
  have hpmem : ∀ v, p v ∈ W := fun v => avgOp_apply_mem hρ hTmem hW v
  have hpid : ∀ w ∈ W, p w = w := fun w hw => avgOp_apply_eq_self hρ hTid hW hw
  have hpcomm : ∀ (h : G) (v : V), p (ρ h v) = ρ h (p v) := fun h v => avgOp_comm hρ T h v
  -- its kernel is the invariant complement
  set f : V →ₗ[ℂ] W := (p : V →ₗ[ℂ] V).codRestrict W (fun v => hpmem v) with hf
  refine ⟨LinearMap.ker f, ?_, ?_⟩
  · intro g x hx
    have hx0 : p x = 0 := by
      have := hx
      rw [LinearMap.mem_ker] at this
      simpa [hf, Subtype.ext_iff] using congrArg (Subtype.val) this
    rw [LinearMap.mem_ker]
    have : p (ρ g x) = 0 := by rw [hpcomm, hx0, map_zero]
    simp [hf, Subtype.ext_iff, this]
  · refine LinearMap.isCompl_of_proj ?_
    intro x
    have := hpid (x : V) x.2
    simp [hf, Subtype.ext_iff, this]
