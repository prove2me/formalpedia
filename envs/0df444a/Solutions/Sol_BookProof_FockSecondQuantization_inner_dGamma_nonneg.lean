-- Prove2me | solution 1 for BookProof.FockSecondQuantization.inner_dGamma_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:38:56.42961+00:00
-- url     : https://prove2.me/submissions/5bc9e3f0-2b45-436d-bdba-7bbd05354fbd

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.inner_dGamma_nonneg
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp_of_subset
import Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_right
import Theorems.Thm_BookProof_FockSecondQuantization_modes_right_subset_closure
import Theorems.Thm_BookProof_FockSecondQuantization_col_support_subset_closure
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) (u : FockAlg) :
    0 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by

  classical
  set L := closureModes col u u with hLdef
  set S : Finset Conf := L.biUnion fun k => (annA k u).support with hSdef
  rw [inner_dGamma_right col u u (modes_right_subset_closure col u u)
    (col_support_subset_closure col u u)]
  have hinner : ∀ k ∈ L, ∀ j : ℕ,
      (inner ℂ (toLp (annA k u)) (toLp (annA j u)) : ℂ)
        = ∑ α ∈ S, (starRingEnd ℂ) ((annA k u) α) * (annA j u) α := by
    intro k hk j
    exact inner_toLp_of_subset (fun α hα => Finset.mem_biUnion.mpr ⟨k, hk, hα⟩) _
  have hstep : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j u)))
      = ∑ α ∈ S, ∑ j ∈ L, ∑ k ∈ L,
          (starRingEnd ℂ) ((annA j u) α) * (col k) j * ((annA k u) α) := by
    have h1 : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j u)))
        = ∑ j ∈ L, ∑ k ∈ L, ∑ α ∈ S,
            (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k hk => ?_
      rw [hinner k hk j, Finset.mul_sum]
    rw [h1]
    rw [Finset.sum_comm (s := L) (t := L)]
    rw [show (∑ k ∈ L, ∑ j ∈ L, ∑ α ∈ S,
          (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α))
        = ∑ k ∈ L, ∑ α ∈ S, ∑ j ∈ L,
          (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α) from
      Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm (s := L) (t := S)]
    refine Finset.sum_congr rfl fun α _ => ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hstep, Complex.re_sum]
  refine Finset.sum_nonneg fun α _ => hpos L fun k => (annA k u) α
