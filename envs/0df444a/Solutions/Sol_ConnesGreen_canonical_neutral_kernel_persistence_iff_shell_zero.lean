-- Prove2me | solution 1 for ConnesGreen.canonical_neutral_kernel_persistence_iff_shell_zero
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T07:06:13.605254+00:00
-- url     : https://prove2.me/submissions/5e824598-3aac-43aa-b560-151e46436ce5

import Theorems.Thm_ConnesGreen_RG0Integration_signed_covariance_compression
import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem core_helper (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) (x : Physical t) :
    (canonicalPositiveCovariance T hT -
      canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0 ↔
      (canonicalPositiveCovariance t ht -
        canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ∧
      (1 - U.toContinuousLinearMap ∘L U.toContinuousLinearMap.adjoint)
        ((canonicalPositiveCovariance T hT -
          canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x)) = 0 := by
  have hc := RG0Integration.signed_covariance_compression t T ht hT S U
    (RG0Integration.window_inclusion_original_source_adjoint t T ht hT htT U hU)
  have hcx := congrArg (fun A : Physical t →L[ℂ] Physical t => A x) hc
  change U.toContinuousLinearMap.adjoint
    ((canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
      (canonicalSelectedSynthesis T hT S).adjoint) (U x)) =
    (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L
      (canonicalSelectedSynthesis t ht S).adjoint) x at hcx
  constructor
  · intro hx
    constructor
    · rw [← hcx, hx, map_zero]
    · simp [hx]
  · rintro ⟨hx, hs⟩
    have hz := hcx.trans hx
    change (canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
      (canonicalSelectedSynthesis T hT S).adjoint) (U x) -
      U (U.toContinuousLinearMap.adjoint
        ((canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
          (canonicalSelectedSynthesis T hT S).adjoint) (U x))) = 0 at hs
    rw [hz, map_zero, sub_zero] at hs
    exact hs
theorem solution (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) :
    (∀ x : Physical t, (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔ (canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0) ↔
    (∀ x : Physical t, (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 → (1 - U.toContinuousLinearMap ∘L U.toContinuousLinearMap.adjoint)
      ((canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
        (canonicalSelectedSynthesis T hT S).adjoint) (U x)) = 0) := by
  constructor
  · intro hp x hx
    exact (core_helper t T ht hT htT S U hU x).mp ((hp x).mp hx) |>.2
  · intro hs x
    constructor
    · intro hx
      exact (core_helper t T ht hT htT S U hU x).mpr ⟨hx, hs x hx⟩
    · intro hx
      exact (core_helper t T ht hT htT S U hU x).mp hx |>.1
