-- Prove2me | solution 1 for ConnesGreen.RG0Integration.exists_original_neutral_window_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T23:03:55.693981+00:00
-- url     : https://prove2.me/submissions/b5d70271-038d-4f38-98e1-32a5eabb8ec6

import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Theorems.Thm_ConnesGreen_RG0Integration_original_neutral_kernel_persists_of_source_compression
import Theorems.Thm_ConnesGreen_exists_original_window_inclusion
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
noncomputable section
theorem solution
    (t T : ℝ) (ht : 0 < t) (hT : 0 < T) (htT : t ≤ T) (S : Finset CriticalZeros)
    (hpos : 0 ≤ canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
      (canonicalSelectedSynthesis T hT S).adjoint) :
    ∃ U : Physical t →ₗᵢ[ℂ] Physical T,
      (∀ g : ℝ → ℂ, ∀ hg : SupportedTest t g,
        U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
      (∀ x : Physical t,
        (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L
          (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔
        (canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
          (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0) := by
  obtain ⟨U, hU⟩ := exists_original_window_inclusion t T ht hT htT
  exact ⟨U, hU, fun x =>
    ConnesGreen.RG0Integration.original_neutral_kernel_persists_of_source_compression
      t T ht hT S U
      (ConnesGreen.RG0Integration.window_inclusion_original_source_adjoint t T ht hT htT U hU)
      hpos x⟩
